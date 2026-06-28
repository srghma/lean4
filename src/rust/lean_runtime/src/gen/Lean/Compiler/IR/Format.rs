// Lean compiler output
// Module: Lean.Compiler.IR.Format
// Imports: Lean.Compiler.IR.Basic Init.Data.Format.Macro
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::r#gen::Lean::Compiler::IR::Basic::{
    initialize_Lean_Compiler_IR_Basic, runtime_initialize_Lean_Compiler_IR_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [120, 95, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 151, 190, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatArg___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lean_IR_formatArray___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_formatArray___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatArray___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatArray___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatArray___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatLitVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatLitVal___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatLitVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatLitVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatLitVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatLitVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 116, 111, 114, 95, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatCtorInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatCtorInfo___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatCtorInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatCtorInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 115, 101, 116, 91, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [93, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 101, 117, 115, 101, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 105, 110, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [33, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 114, 111, 106, 91, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 112, 114, 111, 106, 91, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 112, 114, 111, 106, 91, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 97, 112, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [97, 112, 112, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [98, 111, 120, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 110, 98, 111, 120, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 115, 83, 104, 97, 114, 101, 100, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatExpr___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringExpr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 108, 111, 97, 116, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [117, 56, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 49, 54, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 51, 50, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 54, 52, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [117, 115, 105, 122, 101, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [111, 98, 106, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 111, 98, 106, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 108, 111, 97, 116, 51, 50, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 116, 114, 117, 99, 116, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [123, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 110, 105, 111, 110, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 97, 103, 103, 101, 100, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [118, 111, 105, 100, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatIRType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatIRType___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatIRType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringIRType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringIRType___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringIRType___closed__1_value: crate::leanh::LeanClosureObject<5> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instToStringIRType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringIRType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [64, 38, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatParam___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatParam___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatParam: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatAlt___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [32, 226, 134, 146, 0],
    };
static mut l_Lean_IR_formatAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatAlt___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_formatAlt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatAlt___closed__2_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 9,
        m_data: [100, 101, 102, 97, 117, 108, 116, 32, 226, 134, 146, 0],
    };
static mut l_Lean_IR_formatAlt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatAlt___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_formatAlt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 101, 116, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__4_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [98, 108, 111, 99, 107, 95, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__5_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [32, 58, 61, 32, 46, 46, 46, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 101, 116, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__9_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [93, 32, 58, 61, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__10_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__11_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 101, 116, 84, 97, 103, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__13_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [117, 115, 101, 116, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__14_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__15_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [115, 115, 101, 116, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__16_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__17_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [93, 32, 58, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__18_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__19_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [105, 110, 99, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_formatFnBodyHead___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_formatFnBodyHead___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_formatFnBodyHead___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_formatFnBodyHead___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_formatFnBodyHead___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value
        ) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__24_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [100, 101, 99, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__25_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__26_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 101, 108, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__27_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__28_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__29_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__30_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [32, 111, 102, 32, 46, 46, 46, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__31_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__32_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [114, 101, 116, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__33_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__32_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__34_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [106, 109, 112, 32, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__35_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__34_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__36_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [226, 138, 165, 0],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__37_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__36_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_formatFnBodyHead___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [59, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 61, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 111, 102, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatFnBody___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatFnBody___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatFnBody___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatFnBody___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatFnBody: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatFnBody___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringFnBody___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringFnBody___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringFnBody___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringFnBody___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringFnBody: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringFnBody___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatDecl___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 101, 102, 32, 0],
    };
static mut l_Lean_IR_formatDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatDecl___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_formatDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatDecl___closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 120, 116, 101, 114, 110, 32, 0],
    };
static mut l_Lean_IR_formatDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_formatDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_formatDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToFormatDecl___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatDecl___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToFormatDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringDecl___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_declToString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(
    mut v_x_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1357_) == 0 {
                    v_id_1358_ = crate::leanh::lean_ctor_get(v_x_1357_, 0);
                    v_isSharedCheck_1368_ = (!crate::leanh::lean_is_exclusive(v_x_1357_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1360_ = v_x_1357_;
                        v_isShared_1361_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_id_1358_);
                        crate::leanh::lean_dec(v_x_1357_);
                        v___x_1360_ = crate::leanh::lean_box(0);
                        v_isShared_1361_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1369_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2;
                    return v___x_1369_;
                }
            }
            1 => {
                v___x_1362_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1363_ = l_Nat_reprFast(v_id_1358_);
                v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
                crate::leanh::lean_dec_ref(v___x_1363_);
                if v_isShared_1361_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1360_, 3);
                    crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
                    v___x_1366_ = v_reuseFailAlloc_1367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatArg___private__1(
    mut v_a_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_a_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Lean_IR_formatArray___redArg___lam__0(
    mut v_inst_1377_: *mut crate::leanh::LeanObject,
    mut v_x1_1378_: *mut crate::leanh::LeanObject,
    mut v_x2_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
    v___x_1381_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1381_, 0, v_x1_1378_);
    crate::leanh::lean_ctor_set(v___x_1381_, 1, v___x_1380_);
    v___x_1382_ = crate::leanh::lean_apply_1(v_inst_1377_, v_x2_1379_);
    v___x_1383_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1383_, 0, v___x_1381_);
    crate::leanh::lean_ctor_set(v___x_1383_, 1, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn l_Lean_IR_formatArray___redArg(
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_args_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    v___x_1405_ = crate::leanh::lean_box(0);
    v___x_1406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1407_ = lean_array_get_size(v_args_1404_);
    v___x_1408_ = l_Lean_IR_formatArray___redArg___closed__9;
    v___x_1409_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
    if v___x_1409_ == 0 {
        crate::leanh::lean_dec_ref(v_args_1404_);
        crate::leanh::lean_dec_ref(v_inst_1403_);
        return v___x_1405_;
    } else {
        let mut v___f_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: u8 = 0;
        v___f_1410_ = crate::leanh::lean_alloc_closure(
            l_Lean_IR_formatArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1410_, 0, v_inst_1403_);
        v___x_1411_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
        if v___x_1411_ == 0 {
            if v___x_1409_ == 0 {
                crate::leanh::lean_dec_ref(v___f_1410_);
                crate::leanh::lean_dec_ref(v_args_1404_);
                return v___x_1405_;
            } else {
                let mut v___x_1412_: usize = 0;
                let mut v___x_1413_: usize = 0;
                let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1412_ = 0usize;
                v___x_1413_ = lean_usize_of_nat(v___x_1407_);
                v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1408_,
                    v___f_1410_,
                    v_args_1404_,
                    v___x_1412_,
                    v___x_1413_,
                    v___x_1405_,
                );
                return v___x_1414_;
            }
        } else {
            let mut v___x_1415_: usize = 0;
            let mut v___x_1416_: usize = 0;
            let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1415_ = 0usize;
            v___x_1416_ = lean_usize_of_nat(v___x_1407_);
            v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1408_,
                v___f_1410_,
                v_args_1404_,
                v___x_1415_,
                v___x_1416_,
                v___x_1405_,
            );
            return v___x_1417_;
        }
    }
}
pub unsafe fn l_Lean_IR_formatArray(
    mut v_00_u03b1_1418_: *mut crate::leanh::LeanObject,
    mut v_inst_1419_: *mut crate::leanh::LeanObject,
    mut v_args_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_Lean_IR_formatArray___redArg(v_inst_1419_, v_args_1420_);
    return v___x_1421_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(
    mut v_x_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut v_v_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1422_) == 0 {
                    v_v_1423_ = crate::leanh::lean_ctor_get(v_x_1422_, 0);
                    v_isSharedCheck_1431_ = (!crate::leanh::lean_is_exclusive(v_x_1422_)) as u8;
                    if v_isSharedCheck_1431_ == 0 {
                        v___x_1425_ = v_x_1422_;
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_1423_);
                        crate::leanh::lean_dec(v_x_1422_);
                        v___x_1425_ = crate::leanh::lean_box(0);
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_1432_ = crate::leanh::lean_ctor_get(v_x_1422_, 0);
                    v_isSharedCheck_1440_ = (!crate::leanh::lean_is_exclusive(v_x_1422_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v___x_1434_ = v_x_1422_;
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_1432_);
                        crate::leanh::lean_dec(v_x_1422_);
                        v___x_1434_ = crate::leanh::lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1427_ = l_Nat_reprFast(v_v_1423_);
                if v_isShared_1426_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1425_, 3);
                    crate::leanh::lean_ctor_set(v___x_1425_, 0, v___x_1427_);
                    v___x_1429_ = v___x_1425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1430_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
                    v___x_1429_ = v_reuseFailAlloc_1430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1429_;
            }
            3 => {
                v___x_1436_ = l_String_quote(v_v_1432_);
                if v_isShared_1435_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1434_, 3);
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1436_);
                    v___x_1438_ = v___x_1434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
                    v___x_1438_ = v_reuseFailAlloc_1439_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatLitVal___private__1(
    mut v_a_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_a_1441_);
    return v___x_1442_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1458_ = crate::leanh::lean_ctor_get(v_x_1457_, 0);
                crate::leanh::lean_inc(v_name_1458_);
                v_cidx_1459_ = crate::leanh::lean_ctor_get(v_x_1457_, 1);
                crate::leanh::lean_inc(v_cidx_1459_);
                v_usize_1460_ = crate::leanh::lean_ctor_get(v_x_1457_, 3);
                crate::leanh::lean_inc(v_usize_1460_);
                v_ssize_1461_ = crate::leanh::lean_ctor_get(v_x_1457_, 4);
                crate::leanh::lean_inc(v_ssize_1461_);
                crate::leanh::lean_dec_ref(v_x_1457_);
                v___x_1474_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5;
                v___x_1475_ = l_Nat_reprFast(v_cidx_1459_);
                v___x_1476_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1476_, 0, v___x_1475_);
                v_r_1477_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_r_1477_, 0, v___x_1474_);
                crate::leanh::lean_ctor_set(v_r_1477_, 1, v___x_1476_);
                v___x_1489_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1490_ = lean_nat_dec_lt(v___x_1489_, v_usize_1460_);
                if v___x_1490_ == 0 {
                    v___x_1491_ = lean_nat_dec_lt(v___x_1489_, v_ssize_1461_);
                    v___y_1479_ = v___x_1491_;
                    state = 2;
                    continue;
                } else {
                    v___y_1479_ = v___x_1490_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1464_ = crate::leanh::lean_box(0);
                v___x_1465_ = lean_name_eq(v_name_1458_, v___x_1464_);
                if v___x_1465_ == 0 {
                    v___x_1466_ = 1;
                    v___x_1467_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_1468_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1468_, 0, v_r_1463_);
                    crate::leanh::lean_ctor_set(v___x_1468_, 1, v___x_1467_);
                    v___x_1469_ = l_Lean_Name_toString(v_name_1458_, v___x_1466_);
                    v___x_1470_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1469_);
                    v___x_1471_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1468_);
                    crate::leanh::lean_ctor_set(v___x_1471_, 1, v___x_1470_);
                    v___x_1472_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                    v_r_1473_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_1473_, 0, v___x_1471_);
                    crate::leanh::lean_ctor_set(v_r_1473_, 1, v___x_1472_);
                    return v_r_1473_;
                } else {
                    crate::leanh::lean_dec(v_name_1458_);
                    return v_r_1463_;
                }
            }
            2 => {
                if v___y_1479_ == 0 {
                    crate::leanh::lean_dec(v_ssize_1461_);
                    crate::leanh::lean_dec(v_usize_1460_);
                    v_r_1463_ = v_r_1477_;
                    state = 1;
                    continue;
                } else {
                    v___x_1480_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7;
                    v___x_1481_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1481_, 0, v_r_1477_);
                    crate::leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                    v___x_1482_ = l_Nat_reprFast(v_usize_1460_);
                    v___x_1483_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1483_, 0, v___x_1482_);
                    v___x_1484_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1484_, 0, v___x_1481_);
                    crate::leanh::lean_ctor_set(v___x_1484_, 1, v___x_1483_);
                    v___x_1485_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                    crate::leanh::lean_ctor_set(v___x_1485_, 1, v___x_1480_);
                    v___x_1486_ = l_Nat_reprFast(v_ssize_1461_);
                    v___x_1487_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1486_);
                    v_r_1488_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_1488_, 0, v___x_1485_);
                    crate::leanh::lean_ctor_set(v_r_1488_, 1, v___x_1487_);
                    v_r_1463_ = v_r_1488_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatCtorInfo___private__1(
    mut v_a_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_a_1492_);
    return v___x_1493_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(
    mut v_as_1496_: *mut crate::leanh::LeanObject,
    mut v_i_1497_: usize,
    mut v_stop_1498_: usize,
    mut v_b_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: usize = 0;
    let mut v___x_1507_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1500_ = lean_usize_dec_eq(v_i_1497_, v_stop_1498_);
                if v___x_1500_ == 0 {
                    v___x_1501_ = lean_array_uget_borrowed(v_as_1496_, v_i_1497_);
                    v___x_1502_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                    v___x_1503_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1503_, 0, v_b_1499_);
                    crate::leanh::lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                    crate::leanh::lean_inc(v___x_1501_);
                    v___x_1504_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_1501_);
                    v___x_1505_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                    crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                    v___x_1506_ = 1usize;
                    v___x_1507_ = lean_usize_add(v_i_1497_, v___x_1506_);
                    v_i_1497_ = v___x_1507_;
                    v_b_1499_ = v___x_1505_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1499_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(
    mut v_as_1509_: *mut crate::leanh::LeanObject,
    mut v_i_1510_: *mut crate::leanh::LeanObject,
    mut v_stop_1511_: *mut crate::leanh::LeanObject,
    mut v_b_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1513_: usize = 0;
    let mut v_stop_boxed_1514_: usize = 0;
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1513_ = crate::leanh::lean_unbox_usize(v_i_1510_);
    crate::leanh::lean_dec(v_i_1510_);
    v_stop_boxed_1514_ = crate::leanh::lean_unbox_usize(v_stop_1511_);
    crate::leanh::lean_dec(v_stop_1511_);
    v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_, v_b_1512_);
    crate::leanh::lean_dec_ref(v_as_1509_);
    return v_res_1515_;
}
pub unsafe fn l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(
    mut v_args_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    v___x_1517_ = crate::leanh::lean_box(0);
    v___x_1518_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1519_ = lean_array_get_size(v_args_1516_);
    v___x_1520_ = lean_nat_dec_lt(v___x_1518_, v___x_1519_);
    if v___x_1520_ == 0 {
        return v___x_1517_;
    } else {
        let mut v___x_1521_: u8 = 0;
        v___x_1521_ = lean_nat_dec_le(v___x_1519_, v___x_1519_);
        if v___x_1521_ == 0 {
            if v___x_1520_ == 0 {
                return v___x_1517_;
            } else {
                let mut v___x_1522_: usize = 0;
                let mut v___x_1523_: usize = 0;
                let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1522_ = 0usize;
                v___x_1523_ = lean_usize_of_nat(v___x_1519_);
                v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_1516_, v___x_1522_, v___x_1523_, v___x_1517_);
                return v___x_1524_;
            }
        } else {
            let mut v___x_1525_: usize = 0;
            let mut v___x_1526_: usize = 0;
            let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1525_ = 0usize;
            v___x_1526_ = lean_usize_of_nat(v___x_1519_);
            v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_1516_, v___x_1525_, v___x_1526_, v___x_1517_);
            return v___x_1527_;
        }
    }
}
pub unsafe fn l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(
    mut v_args_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_1528_);
    crate::leanh::lean_dec_ref(v_args_1528_);
    return v_res_1529_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(
    mut v_x_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_n_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_1604_: u8 = 0;
    let mut v_ys_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_i_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_n_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut v_c_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut v_x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_unused_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_v_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_1571_) {
                    0 => {
                        v_i_1572_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_ys_1573_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1582_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1582_ == 0 {
                            v___x_1575_ = v_x_1571_;
                            v_isShared_1576_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ys_1573_);
                            crate::leanh::lean_inc(v_i_1572_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1575_ = crate::leanh::lean_box(0);
                            v_isShared_1576_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_n_1583_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_x_1584_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1601_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1601_ == 0 {
                            v___x_1586_ = v_x_1571_;
                            v_isShared_1587_ = v_isSharedCheck_1601_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1584_);
                            crate::leanh::lean_inc(v_n_1583_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1586_ = crate::leanh::lean_box(0);
                            v_isShared_1587_ = v_isSharedCheck_1601_;
                            state = 3;
                            continue;
                        }
                    }
                    2 => {
                        v_x_1602_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        crate::leanh::lean_inc(v_x_1602_);
                        v_i_1603_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        crate::leanh::lean_inc_ref(v_i_1603_);
                        v_updtHeader_1604_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_1571_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_ys_1605_ = crate::leanh::lean_ctor_get(v_x_1571_, 2);
                        crate::leanh::lean_inc_ref(v_ys_1605_);
                        crate::leanh::lean_dec_ref_known(v_x_1571_, 3);
                        v___x_1606_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5;
                        if v_updtHeader_1604_ == 0 {
                            v___x_1624_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8;
                            v___y_1608_ = v___x_1624_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1625_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9;
                            v___y_1608_ = v___x_1625_;
                            state = 5;
                            continue;
                        }
                    }
                    3 => {
                        v_i_1626_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_x_1627_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1644_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1644_ == 0 {
                            v___x_1629_ = v_x_1571_;
                            v_isShared_1630_ = v_isSharedCheck_1644_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1627_);
                            crate::leanh::lean_inc(v_i_1626_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1629_ = crate::leanh::lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1644_;
                            state = 6;
                            continue;
                        }
                    }
                    4 => {
                        v_i_1645_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_x_1646_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1663_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1663_ == 0 {
                            v___x_1648_ = v_x_1571_;
                            v_isShared_1649_ = v_isSharedCheck_1663_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1646_);
                            crate::leanh::lean_inc(v_i_1645_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1648_ = crate::leanh::lean_box(0);
                            v_isShared_1649_ = v_isSharedCheck_1663_;
                            state = 8;
                            continue;
                        }
                    }
                    5 => {
                        v_n_1664_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        crate::leanh::lean_inc(v_n_1664_);
                        v_offset_1665_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        crate::leanh::lean_inc(v_offset_1665_);
                        v_x_1666_ = crate::leanh::lean_ctor_get(v_x_1571_, 2);
                        crate::leanh::lean_inc(v_x_1666_);
                        crate::leanh::lean_dec_ref_known(v_x_1571_, 3);
                        v___x_1667_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15;
                        v___x_1668_ = l_Nat_reprFast(v_n_1664_);
                        v___x_1669_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
                        v___x_1670_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1667_);
                        crate::leanh::lean_ctor_set(v___x_1670_, 1, v___x_1669_);
                        v___x_1671_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                        v___x_1672_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1670_);
                        crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                        v___x_1673_ = l_Nat_reprFast(v_offset_1665_);
                        v___x_1674_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1674_, 0, v___x_1673_);
                        v___x_1675_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1672_);
                        crate::leanh::lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                        v___x_1676_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                        v___x_1677_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1675_);
                        crate::leanh::lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                        v___x_1678_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                        v___x_1679_ = l_Nat_reprFast(v_x_1666_);
                        v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
                        crate::leanh::lean_dec_ref(v___x_1679_);
                        v___x_1681_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
                        v___x_1682_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1677_);
                        crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                        return v___x_1682_;
                    }
                    6 => {
                        v_c_1683_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_ys_1684_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1695_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1695_ == 0 {
                            v___x_1686_ = v_x_1571_;
                            v_isShared_1687_ = v_isSharedCheck_1695_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ys_1684_);
                            crate::leanh::lean_inc(v_c_1683_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1686_ = crate::leanh::lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1695_;
                            state = 10;
                            continue;
                        }
                    }
                    7 => {
                        v_c_1696_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_ys_1697_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1710_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1710_ == 0 {
                            v___x_1699_ = v_x_1571_;
                            v_isShared_1700_ = v_isSharedCheck_1710_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ys_1697_);
                            crate::leanh::lean_inc(v_c_1696_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1699_ = crate::leanh::lean_box(0);
                            v_isShared_1700_ = v_isSharedCheck_1710_;
                            state = 12;
                            continue;
                        }
                    }
                    8 => {
                        v_x_1711_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_ys_1712_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1726_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1726_ == 0 {
                            v___x_1714_ = v_x_1571_;
                            v_isShared_1715_ = v_isSharedCheck_1726_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_ys_1712_);
                            crate::leanh::lean_inc(v_x_1711_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1714_ = crate::leanh::lean_box(0);
                            v_isShared_1715_ = v_isSharedCheck_1726_;
                            state = 14;
                            continue;
                        }
                    }
                    9 => {
                        v_x_1727_ = crate::leanh::lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1739_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1739_ == 0 {
                            v_unused_1740_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                            crate::leanh::lean_dec(v_unused_1740_);
                            v___x_1729_ = v_x_1571_;
                            v_isShared_1730_ = v_isSharedCheck_1739_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1727_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1729_ = crate::leanh::lean_box(0);
                            v_isShared_1730_ = v_isSharedCheck_1739_;
                            state = 16;
                            continue;
                        }
                    }
                    10 => {
                        v_x_1741_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_isSharedCheck_1753_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1753_ == 0 {
                            v___x_1743_ = v_x_1571_;
                            v_isShared_1744_ = v_isSharedCheck_1753_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1741_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1743_ = crate::leanh::lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1753_;
                            state = 18;
                            continue;
                        }
                    }
                    11 => {
                        v_v_1754_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        crate::leanh::lean_inc_ref(v_v_1754_);
                        crate::leanh::lean_dec_ref_known(v_x_1571_, 1);
                        v___x_1755_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_v_1754_);
                        return v___x_1755_;
                    }
                    _ => {
                        v_x_1756_ = crate::leanh::lean_ctor_get(v_x_1571_, 0);
                        v_isSharedCheck_1768_ = (!crate::leanh::lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1768_ == 0 {
                            v___x_1758_ = v_x_1571_;
                            v_isShared_1759_ = v_isSharedCheck_1768_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_x_1756_);
                            crate::leanh::lean_dec(v_x_1571_);
                            v___x_1758_ = crate::leanh::lean_box(0);
                            v_isShared_1759_ = v_isSharedCheck_1768_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1577_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_1572_);
                v___x_1578_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1573_);
                crate::leanh::lean_dec_ref(v_ys_1573_);
                if v_isShared_1576_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1575_, 5);
                    crate::leanh::lean_ctor_set(v___x_1575_, 1, v___x_1578_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1580_ = v___x_1575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1580_;
            }
            3 => {
                v___x_1588_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1;
                v___x_1589_ = l_Nat_reprFast(v_n_1583_);
                v___x_1590_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1586_, 5);
                    crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1590_);
                    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1588_);
                    v___x_1592_ = v___x_1586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1590_);
                    v___x_1592_ = v_reuseFailAlloc_1600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1593_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1594_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1594_, 0, v___x_1592_);
                crate::leanh::lean_ctor_set(v___x_1594_, 1, v___x_1593_);
                v___x_1595_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1596_ = l_Nat_reprFast(v_x_1584_);
                v___x_1597_ = lean_string_append(v___x_1595_, v___x_1596_);
                crate::leanh::lean_dec_ref(v___x_1596_);
                v___x_1598_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1597_);
                v___x_1599_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1599_, 0, v___x_1594_);
                crate::leanh::lean_ctor_set(v___x_1599_, 1, v___x_1598_);
                return v___x_1599_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_1608_);
                v___x_1609_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1609_, 0, v___y_1608_);
                v___x_1610_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1606_);
                crate::leanh::lean_ctor_set(v___x_1610_, 1, v___x_1609_);
                v___x_1611_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_1612_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1610_);
                crate::leanh::lean_ctor_set(v___x_1612_, 1, v___x_1611_);
                v___x_1613_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1614_ = l_Nat_reprFast(v_x_1602_);
                v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
                crate::leanh::lean_dec_ref(v___x_1614_);
                v___x_1616_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1616_, 0, v___x_1615_);
                v___x_1617_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1612_);
                crate::leanh::lean_ctor_set(v___x_1617_, 1, v___x_1616_);
                v___x_1618_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7;
                v___x_1619_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1619_, 0, v___x_1617_);
                crate::leanh::lean_ctor_set(v___x_1619_, 1, v___x_1618_);
                v___x_1620_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_1603_);
                v___x_1621_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1621_, 0, v___x_1619_);
                crate::leanh::lean_ctor_set(v___x_1621_, 1, v___x_1620_);
                v___x_1622_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1605_);
                crate::leanh::lean_dec_ref(v_ys_1605_);
                v___x_1623_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1623_, 0, v___x_1621_);
                crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                return v___x_1623_;
            }
            6 => {
                v___x_1631_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11;
                v___x_1632_ = l_Nat_reprFast(v_i_1626_);
                v___x_1633_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1633_, 0, v___x_1632_);
                if v_isShared_1630_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1629_, 5);
                    crate::leanh::lean_ctor_set(v___x_1629_, 1, v___x_1633_);
                    crate::leanh::lean_ctor_set(v___x_1629_, 0, v___x_1631_);
                    v___x_1635_ = v___x_1629_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1643_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1633_);
                    v___x_1635_ = v_reuseFailAlloc_1643_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1636_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1637_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1637_, 0, v___x_1635_);
                crate::leanh::lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                v___x_1638_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1639_ = l_Nat_reprFast(v_x_1627_);
                v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
                crate::leanh::lean_dec_ref(v___x_1639_);
                v___x_1641_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1640_);
                v___x_1642_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1642_, 0, v___x_1637_);
                crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1641_);
                return v___x_1642_;
            }
            8 => {
                v___x_1650_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13;
                v___x_1651_ = l_Nat_reprFast(v_i_1645_);
                v___x_1652_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
                if v_isShared_1649_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1648_, 5);
                    crate::leanh::lean_ctor_set(v___x_1648_, 1, v___x_1652_);
                    crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1650_);
                    v___x_1654_ = v___x_1648_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1652_);
                    v___x_1654_ = v_reuseFailAlloc_1662_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1655_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1656_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1654_);
                crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                v___x_1657_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1658_ = l_Nat_reprFast(v_x_1646_);
                v___x_1659_ = lean_string_append(v___x_1657_, v___x_1658_);
                crate::leanh::lean_dec_ref(v___x_1658_);
                v___x_1660_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1659_);
                v___x_1661_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1661_, 0, v___x_1656_);
                crate::leanh::lean_ctor_set(v___x_1661_, 1, v___x_1660_);
                return v___x_1661_;
            }
            10 => {
                v___x_1688_ = 1;
                v___x_1689_ = l_Lean_Name_toString(v_c_1683_, v___x_1688_);
                v___x_1690_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1690_, 0, v___x_1689_);
                v___x_1691_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1684_);
                crate::leanh::lean_dec_ref(v_ys_1684_);
                if v_isShared_1687_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1686_, 5);
                    crate::leanh::lean_ctor_set(v___x_1686_, 1, v___x_1691_);
                    crate::leanh::lean_ctor_set(v___x_1686_, 0, v___x_1690_);
                    v___x_1693_ = v___x_1686_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1693_;
            }
            12 => {
                v___x_1701_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19;
                v___x_1702_ = 1;
                v___x_1703_ = l_Lean_Name_toString(v_c_1696_, v___x_1702_);
                v___x_1704_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                if v_isShared_1700_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1699_, 5);
                    crate::leanh::lean_ctor_set(v___x_1699_, 1, v___x_1704_);
                    crate::leanh::lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1706_ = v___x_1699_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1704_);
                    v___x_1706_ = v_reuseFailAlloc_1709_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1707_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1697_);
                crate::leanh::lean_dec_ref(v_ys_1697_);
                v___x_1708_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1706_);
                crate::leanh::lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                return v___x_1708_;
            }
            14 => {
                v___x_1716_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21;
                v___x_1717_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1718_ = l_Nat_reprFast(v_x_1711_);
                v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
                crate::leanh::lean_dec_ref(v___x_1718_);
                v___x_1720_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1720_, 0, v___x_1719_);
                if v_isShared_1715_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1714_, 5);
                    crate::leanh::lean_ctor_set(v___x_1714_, 1, v___x_1720_);
                    crate::leanh::lean_ctor_set(v___x_1714_, 0, v___x_1716_);
                    v___x_1722_ = v___x_1714_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1720_);
                    v___x_1722_ = v_reuseFailAlloc_1725_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_1723_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1712_);
                crate::leanh::lean_dec_ref(v_ys_1712_);
                v___x_1724_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1724_, 0, v___x_1722_);
                crate::leanh::lean_ctor_set(v___x_1724_, 1, v___x_1723_);
                return v___x_1724_;
            }
            16 => {
                v___x_1731_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23;
                v___x_1732_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1733_ = l_Nat_reprFast(v_x_1727_);
                v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
                crate::leanh::lean_dec_ref(v___x_1733_);
                v___x_1735_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1734_);
                if v_isShared_1730_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1729_, 5);
                    crate::leanh::lean_ctor_set(v___x_1729_, 1, v___x_1735_);
                    crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1731_);
                    v___x_1737_ = v___x_1729_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
                    v___x_1737_ = v_reuseFailAlloc_1738_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1737_;
            }
            18 => {
                v___x_1745_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25;
                v___x_1746_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1747_ = l_Nat_reprFast(v_x_1741_);
                v___x_1748_ = lean_string_append(v___x_1746_, v___x_1747_);
                crate::leanh::lean_dec_ref(v___x_1747_);
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1743_, 3);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1743_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1748_);
                    v___x_1750_ = v_reuseFailAlloc_1752_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1751_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1745_);
                crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1750_);
                return v___x_1751_;
            }
            20 => {
                v___x_1760_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27;
                v___x_1761_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1762_ = l_Nat_reprFast(v_x_1756_);
                v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
                crate::leanh::lean_dec_ref(v___x_1762_);
                if v_isShared_1759_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1758_, 3);
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1763_);
                    v___x_1765_ = v___x_1758_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1763_);
                    v___x_1765_ = v_reuseFailAlloc_1767_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1766_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1760_);
                crate::leanh::lean_ctor_set(v___x_1766_, 1, v___x_1765_);
                return v___x_1766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatExpr___private__1(
    mut v_a_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_1769_);
    return v___x_1770_;
}
pub unsafe fn l_Lean_IR_instToStringExpr___lam__0(
    mut v_e_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_1773_);
    v___x_1775_ = l_Std_Format_defWidth;
    v___x_1776_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1777_ = l_Std_Format_pretty(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(
    mut v_a_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = lean_nat_to_int(v_a_1780_);
    return v___x_1781_;
}
pub unsafe fn l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(
    mut v_x_1812_: *mut crate::leanh::LeanObject,
    mut v_x_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1812_) == 0 {
        let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1813_);
        v___x_1814_ = crate::leanh::lean_box(0);
        return v___x_1814_;
    } else {
        let mut v_tail_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1815_ = crate::leanh::lean_ctor_get(v_x_1812_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1815_) == 0 {
            let mut v_head_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1813_);
            v_head_1816_ = crate::leanh::lean_ctor_get(v_x_1812_, 0);
            crate::leanh::lean_inc(v_head_1816_);
            crate::leanh::lean_dec_ref_known(v_x_1812_, 2);
            v___x_1817_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1816_);
            return v___x_1817_;
        } else {
            let mut v_head_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1815_);
            v_head_1818_ = crate::leanh::lean_ctor_get(v_x_1812_, 0);
            crate::leanh::lean_inc(v_head_1818_);
            crate::leanh::lean_dec_ref_known(v_x_1812_, 2);
            v___x_1819_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1818_);
            v___x_1820_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_1813_, v___x_1819_, v_tail_1815_);
            return v___x_1820_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20;
    v___x_1823_ = lean_string_length(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once
        ),
        _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22,
    );
    v___x_1825_ = lean_nat_to_int(v___x_1824_);
    return v___x_1825_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(
    mut v_x_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_unused_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_unused_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_1840_) {
                    0 => {
                        v___x_1841_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1;
                        return v___x_1841_;
                    }
                    1 => {
                        v___x_1842_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3;
                        return v___x_1842_;
                    }
                    2 => {
                        v___x_1843_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5;
                        return v___x_1843_;
                    }
                    3 => {
                        v___x_1844_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7;
                        return v___x_1844_;
                    }
                    4 => {
                        v___x_1845_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9;
                        return v___x_1845_;
                    }
                    5 => {
                        v___x_1846_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11;
                        return v___x_1846_;
                    }
                    6 => {
                        v___x_1847_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2;
                        return v___x_1847_;
                    }
                    7 => {
                        v___x_1848_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13;
                        return v___x_1848_;
                    }
                    8 => {
                        v___x_1849_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15;
                        return v___x_1849_;
                    }
                    9 => {
                        v___x_1850_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17;
                        return v___x_1850_;
                    }
                    10 => {
                        v_types_1851_ = crate::leanh::lean_ctor_get(v_x_1840_, 1);
                        v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v_x_1840_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v_unused_1871_ = crate::leanh::lean_ctor_get(v_x_1840_, 0);
                            crate::leanh::lean_dec(v_unused_1871_);
                            v___x_1853_ = v_x_1840_;
                            v_isShared_1854_ = v_isSharedCheck_1870_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_types_1851_);
                            crate::leanh::lean_dec(v_x_1840_);
                            v___x_1853_ = crate::leanh::lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1870_;
                            state = 1;
                            continue;
                        }
                    }
                    11 => {
                        v_types_1872_ = crate::leanh::lean_ctor_get(v_x_1840_, 1);
                        v_isSharedCheck_1891_ = (!crate::leanh::lean_is_exclusive(v_x_1840_)) as u8;
                        if v_isSharedCheck_1891_ == 0 {
                            v_unused_1892_ = crate::leanh::lean_ctor_get(v_x_1840_, 0);
                            crate::leanh::lean_dec(v_unused_1892_);
                            v___x_1874_ = v_x_1840_;
                            v_isShared_1875_ = v_isSharedCheck_1891_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_types_1872_);
                            crate::leanh::lean_dec(v_x_1840_);
                            v___x_1874_ = crate::leanh::lean_box(0);
                            v_isShared_1875_ = v_isSharedCheck_1891_;
                            state = 3;
                            continue;
                        }
                    }
                    12 => {
                        v___x_1893_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29;
                        return v___x_1893_;
                    }
                    _ => {
                        v___x_1894_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31;
                        return v___x_1894_;
                    }
                }
            }
            1 => {
                v___x_1855_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19;
                v___x_1856_ = lean_array_to_list(v_types_1851_);
                v___x_1857_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                v___x_1858_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_1856_, v___x_1857_);
                v___x_1859_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once), _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
                v___x_1860_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24;
                if v_isShared_1854_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1853_, 5);
                    crate::leanh::lean_ctor_set(v___x_1853_, 1, v___x_1858_);
                    crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1858_);
                    v___x_1862_ = v_reuseFailAlloc_1869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1863_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25;
                v___x_1864_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1862_);
                crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1863_);
                v___x_1865_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1865_, 0, v___x_1859_);
                crate::leanh::lean_ctor_set(v___x_1865_, 1, v___x_1864_);
                v___x_1866_ = 0;
                v___x_1867_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1865_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1867_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1866_,
                );
                v___x_1868_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1855_);
                crate::leanh::lean_ctor_set(v___x_1868_, 1, v___x_1867_);
                return v___x_1868_;
            }
            3 => {
                v___x_1876_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27;
                v___x_1877_ = lean_array_to_list(v_types_1872_);
                v___x_1878_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                v___x_1879_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_1877_, v___x_1878_);
                v___x_1880_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once), _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
                v___x_1881_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24;
                if v_isShared_1875_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1874_, 5);
                    crate::leanh::lean_ctor_set(v___x_1874_, 1, v___x_1879_);
                    crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1879_);
                    v___x_1883_ = v_reuseFailAlloc_1890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1884_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25;
                v___x_1885_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1885_, 0, v___x_1883_);
                crate::leanh::lean_ctor_set(v___x_1885_, 1, v___x_1884_);
                v___x_1886_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1880_);
                crate::leanh::lean_ctor_set(v___x_1886_, 1, v___x_1885_);
                v___x_1887_ = 0;
                v___x_1888_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1888_, 0, v___x_1886_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1888_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1887_,
                );
                v___x_1889_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1889_, 0, v___x_1876_);
                crate::leanh::lean_ctor_set(v___x_1889_, 1, v___x_1888_);
                return v___x_1889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(
    mut v_x_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1897_) == 0 {
                    crate::leanh::lean_dec(v_x_1895_);
                    return v_x_1896_;
                } else {
                    v_head_1898_ = crate::leanh::lean_ctor_get(v_x_1897_, 0);
                    v_tail_1899_ = crate::leanh::lean_ctor_get(v_x_1897_, 1);
                    v_isSharedCheck_1909_ = (!crate::leanh::lean_is_exclusive(v_x_1897_)) as u8;
                    if v_isSharedCheck_1909_ == 0 {
                        v___x_1901_ = v_x_1897_;
                        v_isShared_1902_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1899_);
                        crate::leanh::lean_inc(v_head_1898_);
                        crate::leanh::lean_dec(v_x_1897_);
                        v___x_1901_ = crate::leanh::lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1895_);
                if v_isShared_1902_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1901_, 5);
                    crate::leanh::lean_ctor_set(v___x_1901_, 1, v_x_1895_);
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v_x_1896_);
                    v___x_1904_ = v___x_1901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_x_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_x_1895_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1898_);
                v___x_1906_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1904_);
                crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1905_);
                v_x_1896_ = v___x_1906_;
                v_x_1897_ = v_tail_1899_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatIRType___private__1(
    mut v_a_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_IR_instToStringIRType___lam__0(
    mut v_f_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Std_Format_defWidth;
    v___x_1916_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1917_ = l_Std_Format_pretty(v_f_1914_, v___x_1915_, v___x_1916_, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(
    mut v_x_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_1935_: u8 = 0;
    let mut v_ty_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_1934_ = crate::leanh::lean_ctor_get(v_x_1933_, 0);
                crate::leanh::lean_inc(v_x_1934_);
                v_borrow_1935_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1933_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_ty_1936_ = crate::leanh::lean_ctor_get(v_x_1933_, 1);
                crate::leanh::lean_inc(v_ty_1936_);
                crate::leanh::lean_dec_ref(v_x_1933_);
                v___x_1937_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1;
                v___x_1938_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1939_ = l_Nat_reprFast(v_x_1934_);
                v___x_1940_ = lean_string_append(v___x_1938_, v___x_1939_);
                crate::leanh::lean_dec_ref(v___x_1939_);
                v___x_1941_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1941_, 0, v___x_1940_);
                v___x_1942_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1937_);
                crate::leanh::lean_ctor_set(v___x_1942_, 1, v___x_1941_);
                v___x_1943_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                v___x_1944_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1944_, 0, v___x_1942_);
                crate::leanh::lean_ctor_set(v___x_1944_, 1, v___x_1943_);
                if v_borrow_1935_ == 0 {
                    v___x_1953_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8;
                    v___y_1946_ = v___x_1953_;
                    state = 1;
                    continue;
                } else {
                    v___x_1954_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6;
                    v___y_1946_ = v___x_1954_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1946_);
                v___x_1947_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1947_, 0, v___y_1946_);
                v___x_1948_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1948_, 0, v___x_1944_);
                crate::leanh::lean_ctor_set(v___x_1948_, 1, v___x_1947_);
                v___x_1949_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1936_);
                v___x_1950_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1948_);
                crate::leanh::lean_ctor_set(v___x_1950_, 1, v___x_1949_);
                v___x_1951_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5;
                v___x_1952_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1950_);
                crate::leanh::lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                return v___x_1952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatParam___private__1(
    mut v_a_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_IR_formatAlt(
    mut v_fmt_1965_: *mut crate::leanh::LeanObject,
    mut v_indent_1966_: *mut crate::leanh::LeanObject,
    mut v_x_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v_name_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_b_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1967_) == 0 {
                    v_info_1968_ = crate::leanh::lean_ctor_get(v_x_1967_, 0);
                    v_b_1969_ = crate::leanh::lean_ctor_get(v_x_1967_, 1);
                    v_isSharedCheck_1987_ = (!crate::leanh::lean_is_exclusive(v_x_1967_)) as u8;
                    if v_isSharedCheck_1987_ == 0 {
                        v___x_1971_ = v_x_1967_;
                        v_isShared_1972_ = v_isSharedCheck_1987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_1969_);
                        crate::leanh::lean_inc(v_info_1968_);
                        crate::leanh::lean_dec(v_x_1967_);
                        v___x_1971_ = crate::leanh::lean_box(0);
                        v_isShared_1972_ = v_isSharedCheck_1987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_b_1988_ = crate::leanh::lean_ctor_get(v_x_1967_, 0);
                    crate::leanh::lean_inc(v_b_1988_);
                    crate::leanh::lean_dec_ref_known(v_x_1967_, 1);
                    v___x_1989_ = l_Lean_IR_formatAlt___closed__3;
                    v___x_1990_ = lean_nat_to_int(v_indent_1966_);
                    v___x_1991_ = crate::leanh::lean_box(1);
                    v___x_1992_ = crate::leanh::lean_apply_1(v_fmt_1965_, v_b_1988_);
                    v___x_1993_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_1991_);
                    crate::leanh::lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                    v___x_1994_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1990_);
                    crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                    v___x_1995_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_1989_);
                    crate::leanh::lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    return v___x_1995_;
                }
            }
            1 => {
                v_name_1973_ = crate::leanh::lean_ctor_get(v_info_1968_, 0);
                crate::leanh::lean_inc(v_name_1973_);
                crate::leanh::lean_dec_ref(v_info_1968_);
                v___x_1974_ = 1;
                v___x_1975_ = l_Lean_Name_toString(v_name_1973_, v___x_1974_);
                v___x_1976_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_1975_);
                v___x_1977_ = l_Lean_IR_formatAlt___closed__1;
                if v_isShared_1972_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1971_, 5);
                    crate::leanh::lean_ctor_set(v___x_1971_, 1, v___x_1977_);
                    crate::leanh::lean_ctor_set(v___x_1971_, 0, v___x_1976_);
                    v___x_1979_ = v___x_1971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1977_);
                    v___x_1979_ = v_reuseFailAlloc_1986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1980_ = lean_nat_to_int(v_indent_1966_);
                v___x_1981_ = crate::leanh::lean_box(1);
                v___x_1982_ = crate::leanh::lean_apply_1(v_fmt_1965_, v_b_1969_);
                v___x_1983_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                crate::leanh::lean_ctor_set(v___x_1983_, 1, v___x_1982_);
                v___x_1984_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1984_, 0, v___x_1980_);
                crate::leanh::lean_ctor_set(v___x_1984_, 1, v___x_1983_);
                v___x_1985_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1979_);
                crate::leanh::lean_ctor_set(v___x_1985_, 1, v___x_1984_);
                return v___x_1985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(
    mut v_as_1996_: *mut crate::leanh::LeanObject,
    mut v_i_1997_: usize,
    mut v_stop_1998_: usize,
    mut v_b_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: usize = 0;
    let mut v___x_2007_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2000_ = lean_usize_dec_eq(v_i_1997_, v_stop_1998_);
                if v___x_2000_ == 0 {
                    v___x_2001_ = lean_array_uget_borrowed(v_as_1996_, v_i_1997_);
                    v___x_2002_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                    v___x_2003_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2003_, 0, v_b_1999_);
                    crate::leanh::lean_ctor_set(v___x_2003_, 1, v___x_2002_);
                    crate::leanh::lean_inc(v___x_2001_);
                    v___x_2004_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_2001_);
                    v___x_2005_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_2003_);
                    crate::leanh::lean_ctor_set(v___x_2005_, 1, v___x_2004_);
                    v___x_2006_ = 1usize;
                    v___x_2007_ = lean_usize_add(v_i_1997_, v___x_2006_);
                    v_i_1997_ = v___x_2007_;
                    v_b_1999_ = v___x_2005_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1999_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0___boxed(
    mut v_as_2009_: *mut crate::leanh::LeanObject,
    mut v_i_2010_: *mut crate::leanh::LeanObject,
    mut v_stop_2011_: *mut crate::leanh::LeanObject,
    mut v_b_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2013_: usize = 0;
    let mut v_stop_boxed_2014_: usize = 0;
    let mut v_res_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2013_ = crate::leanh::lean_unbox_usize(v_i_2010_);
    crate::leanh::lean_dec(v_i_2010_);
    v_stop_boxed_2014_ = crate::leanh::lean_unbox_usize(v_stop_2011_);
    crate::leanh::lean_dec(v_stop_2011_);
    v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_2009_, v_i_boxed_2013_, v_stop_boxed_2014_, v_b_2012_);
    crate::leanh::lean_dec_ref(v_as_2009_);
    return v_res_2015_;
}
pub unsafe fn l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(
    mut v_args_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    v___x_2017_ = crate::leanh::lean_box(0);
    v___x_2018_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2019_ = lean_array_get_size(v_args_2016_);
    v___x_2020_ = lean_nat_dec_lt(v___x_2018_, v___x_2019_);
    if v___x_2020_ == 0 {
        return v___x_2017_;
    } else {
        let mut v___x_2021_: u8 = 0;
        v___x_2021_ = lean_nat_dec_le(v___x_2019_, v___x_2019_);
        if v___x_2021_ == 0 {
            if v___x_2020_ == 0 {
                return v___x_2017_;
            } else {
                let mut v___x_2022_: usize = 0;
                let mut v___x_2023_: usize = 0;
                let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2022_ = 0usize;
                v___x_2023_ = lean_usize_of_nat(v___x_2019_);
                v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_2016_, v___x_2022_, v___x_2023_, v___x_2017_);
                return v___x_2024_;
            }
        } else {
            let mut v___x_2025_: usize = 0;
            let mut v___x_2026_: usize = 0;
            let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2025_ = 0usize;
            v___x_2026_ = lean_usize_of_nat(v___x_2019_);
            v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_2016_, v___x_2025_, v___x_2026_, v___x_2017_);
            return v___x_2027_;
        }
    }
}
pub unsafe fn l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(
    mut v_args_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_2028_);
    crate::leanh::lean_dec_ref(v_args_2028_);
    return v_res_2029_;
}
pub unsafe fn l_Lean_IR_formatParams(
    mut v_ps_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_2030_);
    return v___x_2031_;
}
pub unsafe fn l_Lean_IR_formatParams___boxed(
    mut v_ps_2032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Lean_IR_formatParams(v_ps_2032_);
    crate::leanh::lean_dec_ref(v_ps_2032_);
    return v_res_2033_;
}
pub unsafe fn _init_l_Lean_IR_formatFnBodyHead___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0;
    v___x_2066_ = lean_string_length(v___x_2065_);
    return v___x_2066_;
}
pub unsafe fn _init_l_Lean_IR_formatFnBodyHead___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__21),
        core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__21_once),
        _init_l_Lean_IR_formatFnBodyHead___closed__21,
    );
    v___x_2068_ = lean_nat_to_int(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lean_IR_formatFnBodyHead(
    mut v_x_2092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v_unused_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2092_) {
                0 => {
                    v_x_2093_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2093_);
                    v_ty_2094_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_ty_2094_);
                    v_e_2095_ = crate::leanh::lean_ctor_get(v_x_2092_, 2);
                    crate::leanh::lean_inc_ref(v_e_2095_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2096_ = l_Lean_IR_formatFnBodyHead___closed__1;
                    v___x_2097_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2098_ = l_Nat_reprFast(v_x_2093_);
                    v___x_2099_ = lean_string_append(v___x_2097_, v___x_2098_);
                    crate::leanh::lean_dec_ref(v___x_2098_);
                    v___x_2100_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
                    v___x_2101_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2096_);
                    crate::leanh::lean_ctor_set(v___x_2101_, 1, v___x_2100_);
                    v___x_2102_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2103_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2101_);
                    crate::leanh::lean_ctor_set(v___x_2103_, 1, v___x_2102_);
                    v___x_2104_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2094_);
                    v___x_2105_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2105_, 0, v___x_2103_);
                    crate::leanh::lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                    v___x_2106_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2107_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2105_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2106_);
                    v___x_2108_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_2095_);
                    v___x_2109_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2109_, 0, v___x_2107_);
                    crate::leanh::lean_ctor_set(v___x_2109_, 1, v___x_2108_);
                    return v___x_2109_;
                }
                1 => {
                    v_j_2110_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_j_2110_);
                    v_xs_2111_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc_ref(v_xs_2111_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2112_ = l_Lean_IR_formatFnBodyHead___closed__4;
                    v___x_2113_ = l_Nat_reprFast(v_j_2110_);
                    v___x_2114_ = lean_string_append(v___x_2112_, v___x_2113_);
                    crate::leanh::lean_dec_ref(v___x_2113_);
                    v___x_2115_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___x_2114_);
                    v___x_2116_ =
                        l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2111_);
                    crate::leanh::lean_dec_ref(v_xs_2111_);
                    v___x_2117_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2115_);
                    crate::leanh::lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                    v___x_2118_ = l_Lean_IR_formatFnBodyHead___closed__6;
                    v___x_2119_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2117_);
                    crate::leanh::lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                    return v___x_2119_;
                }
                2 => {
                    v_x_2120_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2120_);
                    v_i_2121_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_i_2121_);
                    v_y_2122_ = crate::leanh::lean_ctor_get(v_x_2092_, 2);
                    crate::leanh::lean_inc(v_y_2122_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2123_ = l_Lean_IR_formatFnBodyHead___closed__8;
                    v___x_2124_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2125_ = l_Nat_reprFast(v_x_2120_);
                    v___x_2126_ = lean_string_append(v___x_2124_, v___x_2125_);
                    crate::leanh::lean_dec_ref(v___x_2125_);
                    v___x_2127_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2126_);
                    v___x_2128_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2123_);
                    crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                    v___x_2129_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2130_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2128_);
                    crate::leanh::lean_ctor_set(v___x_2130_, 1, v___x_2129_);
                    v___x_2131_ = l_Nat_reprFast(v_i_2121_);
                    v___x_2132_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                    v___x_2133_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2130_);
                    crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                    v___x_2134_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2135_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2133_);
                    crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                    v___x_2136_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_2122_);
                    v___x_2137_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2135_);
                    crate::leanh::lean_ctor_set(v___x_2137_, 1, v___x_2136_);
                    return v___x_2137_;
                }
                3 => {
                    v_x_2138_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2138_);
                    v_cidx_2139_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_cidx_2139_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2140_ = l_Lean_IR_formatFnBodyHead___closed__12;
                    v___x_2141_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2142_ = l_Nat_reprFast(v_x_2138_);
                    v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
                    crate::leanh::lean_dec_ref(v___x_2142_);
                    v___x_2144_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2144_, 0, v___x_2143_);
                    v___x_2145_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2140_);
                    crate::leanh::lean_ctor_set(v___x_2145_, 1, v___x_2144_);
                    v___x_2146_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2147_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                    v___x_2148_ = l_Nat_reprFast(v_cidx_2139_);
                    v___x_2149_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2149_, 0, v___x_2148_);
                    v___x_2150_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2150_, 0, v___x_2147_);
                    crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
                    return v___x_2150_;
                }
                4 => {
                    v_x_2151_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2151_);
                    v_i_2152_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_i_2152_);
                    v_y_2153_ = crate::leanh::lean_ctor_get(v_x_2092_, 2);
                    crate::leanh::lean_inc(v_y_2153_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2154_ = l_Lean_IR_formatFnBodyHead___closed__14;
                    v___x_2155_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2156_ = l_Nat_reprFast(v_x_2151_);
                    v___x_2157_ = lean_string_append(v___x_2155_, v___x_2156_);
                    crate::leanh::lean_dec_ref(v___x_2156_);
                    v___x_2158_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v___x_2157_);
                    v___x_2159_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2159_, 0, v___x_2154_);
                    crate::leanh::lean_ctor_set(v___x_2159_, 1, v___x_2158_);
                    v___x_2160_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2161_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2159_);
                    crate::leanh::lean_ctor_set(v___x_2161_, 1, v___x_2160_);
                    v___x_2162_ = l_Nat_reprFast(v_i_2152_);
                    v___x_2163_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                    v___x_2164_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2161_);
                    crate::leanh::lean_ctor_set(v___x_2164_, 1, v___x_2163_);
                    v___x_2165_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2166_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2164_);
                    crate::leanh::lean_ctor_set(v___x_2166_, 1, v___x_2165_);
                    v___x_2167_ = l_Nat_reprFast(v_y_2153_);
                    v___x_2168_ = lean_string_append(v___x_2155_, v___x_2167_);
                    crate::leanh::lean_dec_ref(v___x_2167_);
                    v___x_2169_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
                    v___x_2170_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2166_);
                    crate::leanh::lean_ctor_set(v___x_2170_, 1, v___x_2169_);
                    return v___x_2170_;
                }
                5 => {
                    v_x_2171_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2171_);
                    v_i_2172_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_i_2172_);
                    v_offset_2173_ = crate::leanh::lean_ctor_get(v_x_2092_, 2);
                    crate::leanh::lean_inc(v_offset_2173_);
                    v_y_2174_ = crate::leanh::lean_ctor_get(v_x_2092_, 3);
                    crate::leanh::lean_inc(v_y_2174_);
                    v_ty_2175_ = crate::leanh::lean_ctor_get(v_x_2092_, 4);
                    crate::leanh::lean_inc(v_ty_2175_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 6);
                    v___x_2176_ = l_Lean_IR_formatFnBodyHead___closed__16;
                    v___x_2177_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2178_ = l_Nat_reprFast(v_x_2171_);
                    v___x_2179_ = lean_string_append(v___x_2177_, v___x_2178_);
                    crate::leanh::lean_dec_ref(v___x_2178_);
                    v___x_2180_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
                    v___x_2181_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2176_);
                    crate::leanh::lean_ctor_set(v___x_2181_, 1, v___x_2180_);
                    v___x_2182_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2183_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2181_);
                    crate::leanh::lean_ctor_set(v___x_2183_, 1, v___x_2182_);
                    v___x_2184_ = l_Nat_reprFast(v_i_2172_);
                    v___x_2185_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2185_, 0, v___x_2184_);
                    v___x_2186_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2183_);
                    crate::leanh::lean_ctor_set(v___x_2186_, 1, v___x_2185_);
                    v___x_2187_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                    v___x_2188_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2186_);
                    crate::leanh::lean_ctor_set(v___x_2188_, 1, v___x_2187_);
                    v___x_2189_ = l_Nat_reprFast(v_offset_2173_);
                    v___x_2190_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2189_);
                    v___x_2191_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2188_);
                    crate::leanh::lean_ctor_set(v___x_2191_, 1, v___x_2190_);
                    v___x_2192_ = l_Lean_IR_formatFnBodyHead___closed__18;
                    v___x_2193_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2193_, 0, v___x_2191_);
                    crate::leanh::lean_ctor_set(v___x_2193_, 1, v___x_2192_);
                    v___x_2194_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2175_);
                    v___x_2195_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2193_);
                    crate::leanh::lean_ctor_set(v___x_2195_, 1, v___x_2194_);
                    v___x_2196_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2197_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2195_);
                    crate::leanh::lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                    v___x_2198_ = l_Nat_reprFast(v_y_2174_);
                    v___x_2199_ = lean_string_append(v___x_2177_, v___x_2198_);
                    crate::leanh::lean_dec_ref(v___x_2198_);
                    v___x_2200_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                    v___x_2201_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2197_);
                    crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                    return v___x_2201_;
                }
                6 => {
                    v_x_2202_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2202_);
                    v_n_2203_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_n_2203_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2204_ = l_Lean_IR_formatFnBodyHead___closed__20;
                    v___x_2215_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2216_ = lean_nat_dec_eq(v_n_2203_, v___x_2215_);
                    if v___x_2216_ == 0 {
                        v___x_2217_ = l_Nat_reprFast(v_n_2203_);
                        v___x_2218_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2217_);
                        v___x_2219_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2220_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2221_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
                        crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2218_);
                        v___x_2222_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2223_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2223_, 0, v___x_2221_);
                        crate::leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
                        v___x_2224_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2219_);
                        crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                        v___x_2225_ = 0;
                        v___x_2226_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2224_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2226_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2225_,
                        );
                        v___y_2206_ = v___x_2226_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_2203_);
                        v___x_2227_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2206_ = v___x_2227_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_x_2228_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2228_);
                    v_n_2229_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_n_2229_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2230_ = l_Lean_IR_formatFnBodyHead___closed__25;
                    v___x_2241_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2242_ = lean_nat_dec_eq(v_n_2229_, v___x_2241_);
                    if v___x_2242_ == 0 {
                        v___x_2243_ = l_Nat_reprFast(v_n_2229_);
                        v___x_2244_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
                        v___x_2245_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2246_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2247_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                        crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2244_);
                        v___x_2248_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2249_, 0, v___x_2247_);
                        crate::leanh::lean_ctor_set(v___x_2249_, 1, v___x_2248_);
                        v___x_2250_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2250_, 0, v___x_2245_);
                        crate::leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
                        v___x_2251_ = 0;
                        v___x_2252_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2250_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2252_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2251_,
                        );
                        v___y_2232_ = v___x_2252_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_2229_);
                        v___x_2253_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2232_ = v___x_2253_;
                        state = 2;
                        continue;
                    }
                }
                8 => {
                    v_x_2254_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    v_isSharedCheck_2266_ = (!crate::leanh::lean_is_exclusive(v_x_2092_)) as u8;
                    if v_isSharedCheck_2266_ == 0 {
                        v_unused_2267_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                        crate::leanh::lean_dec(v_unused_2267_);
                        v___x_2256_ = v_x_2092_;
                        v_isShared_2257_ = v_isSharedCheck_2266_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_x_2254_);
                        crate::leanh::lean_dec(v_x_2092_);
                        v___x_2256_ = crate::leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2266_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_x_2268_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    crate::leanh::lean_inc(v_x_2268_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2269_ = l_Lean_IR_formatFnBodyHead___closed__29;
                    v___x_2270_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2271_ = l_Nat_reprFast(v_x_2268_);
                    v___x_2272_ = lean_string_append(v___x_2270_, v___x_2271_);
                    crate::leanh::lean_dec_ref(v___x_2271_);
                    v___x_2273_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2273_, 0, v___x_2272_);
                    v___x_2274_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2274_, 0, v___x_2269_);
                    crate::leanh::lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                    v___x_2275_ = l_Lean_IR_formatFnBodyHead___closed__31;
                    v___x_2276_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2274_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    return v___x_2276_;
                }
                10 => {
                    v_x_2277_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    crate::leanh::lean_inc(v_x_2277_);
                    crate::leanh::lean_dec_ref_known(v_x_2092_, 1);
                    v___x_2278_ = l_Lean_IR_formatFnBodyHead___closed__33;
                    v___x_2279_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_2277_);
                    v___x_2280_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2280_, 0, v___x_2278_);
                    crate::leanh::lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                    return v___x_2280_;
                }
                11 => {
                    v_j_2281_ = crate::leanh::lean_ctor_get(v_x_2092_, 0);
                    v_ys_2282_ = crate::leanh::lean_ctor_get(v_x_2092_, 1);
                    v_isSharedCheck_2296_ = (!crate::leanh::lean_is_exclusive(v_x_2092_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2284_ = v_x_2092_;
                        v_isShared_2285_ = v_isSharedCheck_2296_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ys_2282_);
                        crate::leanh::lean_inc(v_j_2281_);
                        crate::leanh::lean_dec(v_x_2092_);
                        v___x_2284_ = crate::leanh::lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2296_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_2297_ = l_Lean_IR_formatFnBodyHead___closed__37;
                    return v___x_2297_;
                }
            },
            1 => {
                v___x_2207_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2207_, 0, v___x_2204_);
                crate::leanh::lean_ctor_set(v___x_2207_, 1, v___y_2206_);
                v___x_2208_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2209_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2209_, 0, v___x_2207_);
                crate::leanh::lean_ctor_set(v___x_2209_, 1, v___x_2208_);
                v___x_2210_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2211_ = l_Nat_reprFast(v_x_2202_);
                v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
                crate::leanh::lean_dec_ref(v___x_2211_);
                v___x_2213_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2212_);
                v___x_2214_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2214_, 0, v___x_2209_);
                crate::leanh::lean_ctor_set(v___x_2214_, 1, v___x_2213_);
                return v___x_2214_;
            }
            2 => {
                v___x_2233_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2233_, 0, v___x_2230_);
                crate::leanh::lean_ctor_set(v___x_2233_, 1, v___y_2232_);
                v___x_2234_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2235_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2233_);
                crate::leanh::lean_ctor_set(v___x_2235_, 1, v___x_2234_);
                v___x_2236_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2237_ = l_Nat_reprFast(v_x_2228_);
                v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
                crate::leanh::lean_dec_ref(v___x_2237_);
                v___x_2239_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                v___x_2240_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2235_);
                crate::leanh::lean_ctor_set(v___x_2240_, 1, v___x_2239_);
                return v___x_2240_;
            }
            3 => {
                v___x_2258_ = l_Lean_IR_formatFnBodyHead___closed__27;
                v___x_2259_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2260_ = l_Nat_reprFast(v_x_2254_);
                v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
                crate::leanh::lean_dec_ref(v___x_2260_);
                v___x_2262_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2262_, 0, v___x_2261_);
                if v_isShared_2257_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2256_, 5);
                    crate::leanh::lean_ctor_set(v___x_2256_, 1, v___x_2262_);
                    crate::leanh::lean_ctor_set(v___x_2256_, 0, v___x_2258_);
                    v___x_2264_ = v___x_2256_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
                    v___x_2264_ = v_reuseFailAlloc_2265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2264_;
            }
            5 => {
                v___x_2286_ = l_Lean_IR_formatFnBodyHead___closed__35;
                v___x_2287_ = l_Lean_IR_formatFnBodyHead___closed__4;
                v___x_2288_ = l_Nat_reprFast(v_j_2281_);
                v___x_2289_ = lean_string_append(v___x_2287_, v___x_2288_);
                crate::leanh::lean_dec_ref(v___x_2288_);
                v___x_2290_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2289_);
                if v_isShared_2285_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2284_, 5);
                    crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2290_);
                    crate::leanh::lean_ctor_set(v___x_2284_, 0, v___x_2286_);
                    v___x_2292_ = v___x_2284_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2290_);
                    v___x_2292_ = v_reuseFailAlloc_2295_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2293_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_2282_);
                crate::leanh::lean_dec_ref(v_ys_2282_);
                v___x_2294_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2294_, 0, v___x_2292_);
                crate::leanh::lean_ctor_set(v___x_2294_, 1, v___x_2293_);
                return v___x_2294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_ir_format_fn_body_head(
    mut v_fn_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_IR_formatFnBodyHead(v_fn_2298_);
    v___x_2300_ = l_Std_Format_defWidth;
    v___x_2301_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2302_ = l_Std_Format_pretty(v___x_2299_, v___x_2300_, v___x_2301_, v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
    mut v_indent_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u8 = 0;
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut v_x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xType_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_2313_) {
                0 => {
                    v_x_2314_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2314_);
                    v_ty_2315_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_ty_2315_);
                    v_e_2316_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc_ref(v_e_2316_);
                    v_b_2317_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc(v_b_2317_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2318_ = l_Lean_IR_formatFnBodyHead___closed__1;
                    v___x_2319_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2320_ = l_Nat_reprFast(v_x_2314_);
                    v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
                    crate::leanh::lean_dec_ref(v___x_2320_);
                    v___x_2322_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
                    v___x_2323_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2318_);
                    crate::leanh::lean_ctor_set(v___x_2323_, 1, v___x_2322_);
                    v___x_2324_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2325_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2323_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 1, v___x_2324_);
                    v___x_2326_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2315_);
                    v___x_2327_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2327_, 0, v___x_2325_);
                    crate::leanh::lean_ctor_set(v___x_2327_, 1, v___x_2326_);
                    v___x_2328_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2329_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2327_);
                    crate::leanh::lean_ctor_set(v___x_2329_, 1, v___x_2328_);
                    v___x_2330_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_2316_);
                    v___x_2331_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2331_, 0, v___x_2329_);
                    crate::leanh::lean_ctor_set(v___x_2331_, 1, v___x_2330_);
                    v___x_2332_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2333_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2331_);
                    crate::leanh::lean_ctor_set(v___x_2333_, 1, v___x_2332_);
                    v___x_2334_ = crate::leanh::lean_box(1);
                    v___x_2335_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2333_);
                    crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                    v___x_2336_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2317_,
                    );
                    v___x_2337_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                    crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                    return v___x_2337_;
                }
                1 => {
                    v_j_2338_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_j_2338_);
                    v_xs_2339_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc_ref(v_xs_2339_);
                    v_v_2340_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_v_2340_);
                    v_b_2341_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc(v_b_2341_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2342_ = l_Lean_IR_formatFnBodyHead___closed__4;
                    v___x_2343_ = l_Nat_reprFast(v_j_2338_);
                    v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
                    crate::leanh::lean_dec_ref(v___x_2343_);
                    v___x_2345_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
                    v___x_2346_ =
                        l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2339_);
                    crate::leanh::lean_dec_ref(v_xs_2339_);
                    v___x_2347_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2347_, 0, v___x_2345_);
                    crate::leanh::lean_ctor_set(v___x_2347_, 1, v___x_2346_);
                    v___x_2348_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3;
                    v___x_2349_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2349_, 0, v___x_2347_);
                    crate::leanh::lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                    crate::leanh::lean_inc_n(v_indent_2312_, 2);
                    v___x_2350_ = lean_nat_to_int(v_indent_2312_);
                    v___x_2351_ = crate::leanh::lean_box(1);
                    v___x_2352_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_v_2340_,
                    );
                    v___x_2353_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2353_, 0, v___x_2351_);
                    crate::leanh::lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2350_);
                    crate::leanh::lean_ctor_set(v___x_2354_, 1, v___x_2353_);
                    v___x_2355_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2349_);
                    crate::leanh::lean_ctor_set(v___x_2355_, 1, v___x_2354_);
                    v___x_2356_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2357_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                    crate::leanh::lean_ctor_set(v___x_2357_, 1, v___x_2356_);
                    v___x_2358_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2358_, 0, v___x_2357_);
                    crate::leanh::lean_ctor_set(v___x_2358_, 1, v___x_2351_);
                    v___x_2359_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2341_,
                    );
                    v___x_2360_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2360_, 0, v___x_2358_);
                    crate::leanh::lean_ctor_set(v___x_2360_, 1, v___x_2359_);
                    return v___x_2360_;
                }
                2 => {
                    v_x_2361_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2361_);
                    v_i_2362_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_i_2362_);
                    v_y_2363_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_y_2363_);
                    v_b_2364_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc(v_b_2364_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2365_ = l_Lean_IR_formatFnBodyHead___closed__8;
                    v___x_2366_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2367_ = l_Nat_reprFast(v_x_2361_);
                    v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
                    crate::leanh::lean_dec_ref(v___x_2367_);
                    v___x_2369_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                    v___x_2370_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2370_, 0, v___x_2365_);
                    crate::leanh::lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                    v___x_2371_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2372_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2372_, 0, v___x_2370_);
                    crate::leanh::lean_ctor_set(v___x_2372_, 1, v___x_2371_);
                    v___x_2373_ = l_Nat_reprFast(v_i_2362_);
                    v___x_2374_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2373_);
                    v___x_2375_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2372_);
                    crate::leanh::lean_ctor_set(v___x_2375_, 1, v___x_2374_);
                    v___x_2376_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2377_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2375_);
                    crate::leanh::lean_ctor_set(v___x_2377_, 1, v___x_2376_);
                    v___x_2378_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_2363_);
                    v___x_2379_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2379_, 0, v___x_2377_);
                    crate::leanh::lean_ctor_set(v___x_2379_, 1, v___x_2378_);
                    v___x_2380_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2381_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2381_, 0, v___x_2379_);
                    crate::leanh::lean_ctor_set(v___x_2381_, 1, v___x_2380_);
                    v___x_2382_ = crate::leanh::lean_box(1);
                    v___x_2383_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2381_);
                    crate::leanh::lean_ctor_set(v___x_2383_, 1, v___x_2382_);
                    v___x_2384_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2364_,
                    );
                    v___x_2385_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2385_, 0, v___x_2383_);
                    crate::leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                    return v___x_2385_;
                }
                3 => {
                    v_x_2386_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2386_);
                    v_cidx_2387_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_cidx_2387_);
                    v_b_2388_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_b_2388_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2389_ = l_Lean_IR_formatFnBodyHead___closed__12;
                    v___x_2390_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2391_ = l_Nat_reprFast(v_x_2386_);
                    v___x_2392_ = lean_string_append(v___x_2390_, v___x_2391_);
                    crate::leanh::lean_dec_ref(v___x_2391_);
                    v___x_2393_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    v___x_2394_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2394_, 0, v___x_2389_);
                    crate::leanh::lean_ctor_set(v___x_2394_, 1, v___x_2393_);
                    v___x_2395_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2396_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2394_);
                    crate::leanh::lean_ctor_set(v___x_2396_, 1, v___x_2395_);
                    v___x_2397_ = l_Nat_reprFast(v_cidx_2387_);
                    v___x_2398_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
                    v___x_2399_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2399_, 0, v___x_2396_);
                    crate::leanh::lean_ctor_set(v___x_2399_, 1, v___x_2398_);
                    v___x_2400_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2401_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2401_, 0, v___x_2399_);
                    crate::leanh::lean_ctor_set(v___x_2401_, 1, v___x_2400_);
                    v___x_2402_ = crate::leanh::lean_box(1);
                    v___x_2403_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2403_, 0, v___x_2401_);
                    crate::leanh::lean_ctor_set(v___x_2403_, 1, v___x_2402_);
                    v___x_2404_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2388_,
                    );
                    v___x_2405_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                    crate::leanh::lean_ctor_set(v___x_2405_, 1, v___x_2404_);
                    return v___x_2405_;
                }
                4 => {
                    v_x_2406_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2406_);
                    v_i_2407_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_i_2407_);
                    v_y_2408_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_y_2408_);
                    v_b_2409_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc(v_b_2409_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2410_ = l_Lean_IR_formatFnBodyHead___closed__14;
                    v___x_2411_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2412_ = l_Nat_reprFast(v_x_2406_);
                    v___x_2413_ = lean_string_append(v___x_2411_, v___x_2412_);
                    crate::leanh::lean_dec_ref(v___x_2412_);
                    v___x_2414_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                    v___x_2415_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2415_, 0, v___x_2410_);
                    crate::leanh::lean_ctor_set(v___x_2415_, 1, v___x_2414_);
                    v___x_2416_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2417_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2415_);
                    crate::leanh::lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                    v___x_2418_ = l_Nat_reprFast(v_i_2407_);
                    v___x_2419_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2419_, 0, v___x_2418_);
                    v___x_2420_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2420_, 0, v___x_2417_);
                    crate::leanh::lean_ctor_set(v___x_2420_, 1, v___x_2419_);
                    v___x_2421_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2422_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2422_, 0, v___x_2420_);
                    crate::leanh::lean_ctor_set(v___x_2422_, 1, v___x_2421_);
                    v___x_2423_ = l_Nat_reprFast(v_y_2408_);
                    v___x_2424_ = lean_string_append(v___x_2411_, v___x_2423_);
                    crate::leanh::lean_dec_ref(v___x_2423_);
                    v___x_2425_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                    v___x_2426_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2422_);
                    crate::leanh::lean_ctor_set(v___x_2426_, 1, v___x_2425_);
                    v___x_2427_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2428_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2428_, 0, v___x_2426_);
                    crate::leanh::lean_ctor_set(v___x_2428_, 1, v___x_2427_);
                    v___x_2429_ = crate::leanh::lean_box(1);
                    v___x_2430_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2430_, 0, v___x_2428_);
                    crate::leanh::lean_ctor_set(v___x_2430_, 1, v___x_2429_);
                    v___x_2431_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2409_,
                    );
                    v___x_2432_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2432_, 0, v___x_2430_);
                    crate::leanh::lean_ctor_set(v___x_2432_, 1, v___x_2431_);
                    return v___x_2432_;
                }
                5 => {
                    v_x_2433_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2433_);
                    v_i_2434_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_i_2434_);
                    v_offset_2435_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_offset_2435_);
                    v_y_2436_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc(v_y_2436_);
                    v_ty_2437_ = crate::leanh::lean_ctor_get(v_a_2313_, 4);
                    crate::leanh::lean_inc(v_ty_2437_);
                    v_b_2438_ = crate::leanh::lean_ctor_get(v_a_2313_, 5);
                    crate::leanh::lean_inc(v_b_2438_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 6);
                    v___x_2439_ = l_Lean_IR_formatFnBodyHead___closed__16;
                    v___x_2440_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2441_ = l_Nat_reprFast(v_x_2433_);
                    v___x_2442_ = lean_string_append(v___x_2440_, v___x_2441_);
                    crate::leanh::lean_dec_ref(v___x_2441_);
                    v___x_2443_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                    v___x_2444_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2444_, 0, v___x_2439_);
                    crate::leanh::lean_ctor_set(v___x_2444_, 1, v___x_2443_);
                    v___x_2445_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2446_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2446_, 0, v___x_2444_);
                    crate::leanh::lean_ctor_set(v___x_2446_, 1, v___x_2445_);
                    v___x_2447_ = l_Nat_reprFast(v_i_2434_);
                    v___x_2448_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2447_);
                    v___x_2449_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2449_, 0, v___x_2446_);
                    crate::leanh::lean_ctor_set(v___x_2449_, 1, v___x_2448_);
                    v___x_2450_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                    v___x_2451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2451_, 0, v___x_2449_);
                    crate::leanh::lean_ctor_set(v___x_2451_, 1, v___x_2450_);
                    v___x_2452_ = l_Nat_reprFast(v_offset_2435_);
                    v___x_2453_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2453_, 0, v___x_2452_);
                    v___x_2454_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2454_, 0, v___x_2451_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                    v___x_2455_ = l_Lean_IR_formatFnBodyHead___closed__18;
                    v___x_2456_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                    crate::leanh::lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    v___x_2457_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2437_);
                    v___x_2458_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2458_, 0, v___x_2456_);
                    crate::leanh::lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                    v___x_2459_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2460_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2460_, 0, v___x_2458_);
                    crate::leanh::lean_ctor_set(v___x_2460_, 1, v___x_2459_);
                    v___x_2461_ = l_Nat_reprFast(v_y_2436_);
                    v___x_2462_ = lean_string_append(v___x_2440_, v___x_2461_);
                    crate::leanh::lean_dec_ref(v___x_2461_);
                    v___x_2463_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    v___x_2464_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2464_, 0, v___x_2460_);
                    crate::leanh::lean_ctor_set(v___x_2464_, 1, v___x_2463_);
                    v___x_2465_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2466_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2466_, 0, v___x_2464_);
                    crate::leanh::lean_ctor_set(v___x_2466_, 1, v___x_2465_);
                    v___x_2467_ = crate::leanh::lean_box(1);
                    v___x_2468_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2468_, 0, v___x_2466_);
                    crate::leanh::lean_ctor_set(v___x_2468_, 1, v___x_2467_);
                    v___x_2469_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2438_,
                    );
                    v___x_2470_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2470_, 0, v___x_2468_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 1, v___x_2469_);
                    return v___x_2470_;
                }
                6 => {
                    v_x_2471_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2471_);
                    v_n_2472_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_n_2472_);
                    v_b_2473_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_b_2473_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2474_ = l_Lean_IR_formatFnBodyHead___closed__20;
                    v___x_2491_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2492_ = lean_nat_dec_eq(v_n_2472_, v___x_2491_);
                    if v___x_2492_ == 0 {
                        v___x_2493_ = l_Nat_reprFast(v_n_2472_);
                        v___x_2494_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2494_, 0, v___x_2493_);
                        v___x_2495_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2496_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2497_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2496_);
                        crate::leanh::lean_ctor_set(v___x_2497_, 1, v___x_2494_);
                        v___x_2498_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2499_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2499_, 0, v___x_2497_);
                        crate::leanh::lean_ctor_set(v___x_2499_, 1, v___x_2498_);
                        v___x_2500_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2500_, 0, v___x_2495_);
                        crate::leanh::lean_ctor_set(v___x_2500_, 1, v___x_2499_);
                        v___x_2501_ = 0;
                        v___x_2502_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2502_, 0, v___x_2500_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2502_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2501_,
                        );
                        v___y_2476_ = v___x_2502_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_2472_);
                        v___x_2503_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2476_ = v___x_2503_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_x_2504_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2504_);
                    v_n_2505_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_n_2505_);
                    v_b_2506_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_b_2506_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2507_ = l_Lean_IR_formatFnBodyHead___closed__25;
                    v___x_2524_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2525_ = lean_nat_dec_eq(v_n_2505_, v___x_2524_);
                    if v___x_2525_ == 0 {
                        v___x_2526_ = l_Nat_reprFast(v_n_2505_);
                        v___x_2527_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2527_, 0, v___x_2526_);
                        v___x_2528_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2529_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2530_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2529_);
                        crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2527_);
                        v___x_2531_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2532_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2530_);
                        crate::leanh::lean_ctor_set(v___x_2532_, 1, v___x_2531_);
                        v___x_2533_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2533_, 0, v___x_2528_);
                        crate::leanh::lean_ctor_set(v___x_2533_, 1, v___x_2532_);
                        v___x_2534_ = 0;
                        v___x_2535_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2533_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2535_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2534_,
                        );
                        v___y_2509_ = v___x_2535_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_2505_);
                        v___x_2536_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2509_ = v___x_2536_;
                        state = 2;
                        continue;
                    }
                }
                8 => {
                    v_x_2537_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    v_b_2538_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    v_isSharedCheck_2556_ = (!crate::leanh::lean_is_exclusive(v_a_2313_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2540_ = v_a_2313_;
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_2538_);
                        crate::leanh::lean_inc(v_x_2537_);
                        crate::leanh::lean_dec(v_a_2313_);
                        v___x_2540_ = crate::leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_x_2557_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    crate::leanh::lean_inc(v_x_2557_);
                    v_xType_2558_ = crate::leanh::lean_ctor_get(v_a_2313_, 2);
                    crate::leanh::lean_inc(v_xType_2558_);
                    v_cs_2559_ = crate::leanh::lean_ctor_get(v_a_2313_, 3);
                    crate::leanh::lean_inc_ref(v_cs_2559_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2560_ = l_Lean_IR_formatFnBodyHead___closed__29;
                    v___x_2561_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2562_ = l_Nat_reprFast(v_x_2557_);
                    v___x_2563_ = lean_string_append(v___x_2561_, v___x_2562_);
                    crate::leanh::lean_dec_ref(v___x_2562_);
                    v___x_2564_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
                    v___x_2565_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2560_);
                    crate::leanh::lean_ctor_set(v___x_2565_, 1, v___x_2564_);
                    v___x_2566_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2567_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2567_, 0, v___x_2565_);
                    crate::leanh::lean_ctor_set(v___x_2567_, 1, v___x_2566_);
                    v___x_2568_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_2558_);
                    v___x_2569_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2569_, 0, v___x_2567_);
                    crate::leanh::lean_ctor_set(v___x_2569_, 1, v___x_2568_);
                    v___x_2570_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5;
                    v___x_2571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2571_, 0, v___x_2569_);
                    crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2570_);
                    v___x_2572_ = crate::leanh::lean_box(0);
                    v___x_2573_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2574_ = lean_array_get_size(v_cs_2559_);
                    v___x_2575_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
                    if v___x_2575_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_2559_);
                        crate::leanh::lean_dec(v_indent_2312_);
                        v___x_2576_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2571_);
                        crate::leanh::lean_ctor_set(v___x_2576_, 1, v___x_2572_);
                        return v___x_2576_;
                    } else {
                        v___x_2577_ = lean_nat_dec_le(v___x_2574_, v___x_2574_);
                        if v___x_2577_ == 0 {
                            if v___x_2575_ == 0 {
                                crate::leanh::lean_dec_ref(v_cs_2559_);
                                crate::leanh::lean_dec(v_indent_2312_);
                                v___x_2578_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2578_, 0, v___x_2571_);
                                crate::leanh::lean_ctor_set(v___x_2578_, 1, v___x_2572_);
                                return v___x_2578_;
                            } else {
                                v___x_2579_ = 0usize;
                                v___x_2580_ = lean_usize_of_nat(v___x_2574_);
                                v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2312_, v_cs_2559_, v___x_2579_, v___x_2580_, v___x_2572_);
                                crate::leanh::lean_dec_ref(v_cs_2559_);
                                v___x_2582_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2582_, 0, v___x_2571_);
                                crate::leanh::lean_ctor_set(v___x_2582_, 1, v___x_2581_);
                                return v___x_2582_;
                            }
                        } else {
                            v___x_2583_ = 0usize;
                            v___x_2584_ = lean_usize_of_nat(v___x_2574_);
                            v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2312_, v_cs_2559_, v___x_2583_, v___x_2584_, v___x_2572_);
                            crate::leanh::lean_dec_ref(v_cs_2559_);
                            v___x_2586_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2586_, 0, v___x_2571_);
                            crate::leanh::lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                            return v___x_2586_;
                        }
                    }
                }
                10 => {
                    crate::leanh::lean_dec(v_indent_2312_);
                    v_x_2587_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    crate::leanh::lean_inc(v_x_2587_);
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 1);
                    v___x_2588_ = l_Lean_IR_formatFnBodyHead___closed__33;
                    v___x_2589_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_2587_);
                    v___x_2590_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2588_);
                    crate::leanh::lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                    return v___x_2590_;
                }
                11 => {
                    crate::leanh::lean_dec(v_indent_2312_);
                    v_j_2591_ = crate::leanh::lean_ctor_get(v_a_2313_, 0);
                    v_ys_2592_ = crate::leanh::lean_ctor_get(v_a_2313_, 1);
                    v_isSharedCheck_2606_ = (!crate::leanh::lean_is_exclusive(v_a_2313_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v___x_2594_ = v_a_2313_;
                        v_isShared_2595_ = v_isSharedCheck_2606_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ys_2592_);
                        crate::leanh::lean_inc(v_j_2591_);
                        crate::leanh::lean_dec(v_a_2313_);
                        v___x_2594_ = crate::leanh::lean_box(0);
                        v_isShared_2595_ = v_isSharedCheck_2606_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_indent_2312_);
                    v___x_2607_ = l_Lean_IR_formatFnBodyHead___closed__37;
                    return v___x_2607_;
                }
            },
            1 => {
                v___x_2477_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2474_);
                crate::leanh::lean_ctor_set(v___x_2477_, 1, v___y_2476_);
                v___x_2478_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2479_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2479_, 0, v___x_2477_);
                crate::leanh::lean_ctor_set(v___x_2479_, 1, v___x_2478_);
                v___x_2480_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2481_ = l_Nat_reprFast(v_x_2471_);
                v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
                crate::leanh::lean_dec_ref(v___x_2481_);
                v___x_2483_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                v___x_2484_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2484_, 0, v___x_2479_);
                crate::leanh::lean_ctor_set(v___x_2484_, 1, v___x_2483_);
                v___x_2485_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2486_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2484_);
                crate::leanh::lean_ctor_set(v___x_2486_, 1, v___x_2485_);
                v___x_2487_ = crate::leanh::lean_box(1);
                v___x_2488_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2488_, 0, v___x_2486_);
                crate::leanh::lean_ctor_set(v___x_2488_, 1, v___x_2487_);
                v___x_2489_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2473_,
                );
                v___x_2490_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2490_, 0, v___x_2488_);
                crate::leanh::lean_ctor_set(v___x_2490_, 1, v___x_2489_);
                return v___x_2490_;
            }
            2 => {
                v___x_2510_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2507_);
                crate::leanh::lean_ctor_set(v___x_2510_, 1, v___y_2509_);
                v___x_2511_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2512_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2512_, 0, v___x_2510_);
                crate::leanh::lean_ctor_set(v___x_2512_, 1, v___x_2511_);
                v___x_2513_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2514_ = l_Nat_reprFast(v_x_2504_);
                v___x_2515_ = lean_string_append(v___x_2513_, v___x_2514_);
                crate::leanh::lean_dec_ref(v___x_2514_);
                v___x_2516_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                v___x_2517_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2512_);
                crate::leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
                v___x_2518_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2519_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2517_);
                crate::leanh::lean_ctor_set(v___x_2519_, 1, v___x_2518_);
                v___x_2520_ = crate::leanh::lean_box(1);
                v___x_2521_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2521_, 0, v___x_2519_);
                crate::leanh::lean_ctor_set(v___x_2521_, 1, v___x_2520_);
                v___x_2522_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2506_,
                );
                v___x_2523_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2523_, 0, v___x_2521_);
                crate::leanh::lean_ctor_set(v___x_2523_, 1, v___x_2522_);
                return v___x_2523_;
            }
            3 => {
                v___x_2542_ = l_Lean_IR_formatFnBodyHead___closed__27;
                v___x_2543_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2544_ = l_Nat_reprFast(v_x_2537_);
                v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
                crate::leanh::lean_dec_ref(v___x_2544_);
                v___x_2546_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                if v_isShared_2541_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2540_, 5);
                    crate::leanh::lean_ctor_set(v___x_2540_, 1, v___x_2546_);
                    crate::leanh::lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2548_ = v___x_2540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2546_);
                    v___x_2548_ = v_reuseFailAlloc_2555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2549_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2550_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2550_, 0, v___x_2548_);
                crate::leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
                v___x_2551_ = crate::leanh::lean_box(1);
                v___x_2552_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2550_);
                crate::leanh::lean_ctor_set(v___x_2552_, 1, v___x_2551_);
                v___x_2553_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2538_,
                );
                v___x_2554_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2552_);
                crate::leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                return v___x_2554_;
            }
            5 => {
                v___x_2596_ = l_Lean_IR_formatFnBodyHead___closed__35;
                v___x_2597_ = l_Lean_IR_formatFnBodyHead___closed__4;
                v___x_2598_ = l_Nat_reprFast(v_j_2591_);
                v___x_2599_ = lean_string_append(v___x_2597_, v___x_2598_);
                crate::leanh::lean_dec_ref(v___x_2598_);
                v___x_2600_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2599_);
                if v_isShared_2595_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2594_, 5);
                    crate::leanh::lean_ctor_set(v___x_2594_, 1, v___x_2600_);
                    crate::leanh::lean_ctor_set(v___x_2594_, 0, v___x_2596_);
                    v___x_2602_ = v___x_2594_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2600_);
                    v___x_2602_ = v_reuseFailAlloc_2605_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2603_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_2592_);
                crate::leanh::lean_dec_ref(v_ys_2592_);
                v___x_2604_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2604_, 0, v___x_2602_);
                crate::leanh::lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(
    mut v_indent_2608_: *mut crate::leanh::LeanObject,
    mut v_as_2609_: *mut crate::leanh::LeanObject,
    mut v_i_2610_: usize,
    mut v_stop_2611_: usize,
    mut v_b_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2613_ = lean_usize_dec_eq(v_i_2610_, v_stop_2611_);
                if v___x_2613_ == 0 {
                    v___x_2614_ = lean_array_uget_borrowed(v_as_2609_, v_i_2610_);
                    v___x_2615_ = crate::leanh::lean_box(1);
                    v___x_2616_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2616_, 0, v_b_2612_);
                    crate::leanh::lean_ctor_set(v___x_2616_, 1, v___x_2615_);
                    crate::leanh::lean_inc_n(v_indent_2608_, 2);
                    v___x_2617_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_2617_, 0, v_indent_2608_);
                    crate::leanh::lean_inc(v___x_2614_);
                    v___x_2618_ = l_Lean_IR_formatAlt(v___x_2617_, v_indent_2608_, v___x_2614_);
                    v___x_2619_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2619_, 0, v___x_2616_);
                    crate::leanh::lean_ctor_set(v___x_2619_, 1, v___x_2618_);
                    v___x_2620_ = 1usize;
                    v___x_2621_ = lean_usize_add(v_i_2610_, v___x_2620_);
                    v_i_2610_ = v___x_2621_;
                    v_b_2612_ = v___x_2619_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_indent_2608_);
                    return v_b_2612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(
    mut v_indent_2623_: *mut crate::leanh::LeanObject,
    mut v_as_2624_: *mut crate::leanh::LeanObject,
    mut v_i_2625_: *mut crate::leanh::LeanObject,
    mut v_stop_2626_: *mut crate::leanh::LeanObject,
    mut v_b_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2628_: usize = 0;
    let mut v_stop_boxed_2629_: usize = 0;
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2628_ = crate::leanh::lean_unbox_usize(v_i_2625_);
    crate::leanh::lean_dec(v_i_2625_);
    v_stop_boxed_2629_ = crate::leanh::lean_unbox_usize(v_stop_2626_);
    crate::leanh::lean_dec(v_stop_2626_);
    v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2623_, v_as_2624_, v_i_boxed_2628_, v_stop_boxed_2629_, v_b_2627_);
    crate::leanh::lean_dec_ref(v_as_2624_);
    return v_res_2630_;
}
pub unsafe fn l_Lean_IR_formatFnBody(
    mut v_fnBody_2631_: *mut crate::leanh::LeanObject,
    mut v_indent_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2633_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
        v_indent_2632_,
        v_fnBody_2631_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_IR_instToFormatFnBody___lam__0(
    mut v_fnBody_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2635_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2636_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
        v___x_2635_,
        v_fnBody_2634_,
    );
    return v___x_2636_;
}
pub unsafe fn l_Lean_IR_instToStringFnBody___lam__0(
    mut v_b_2639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2640_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2641_ =
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_2640_, v_b_2639_);
    v___x_2642_ = l_Std_Format_defWidth;
    v___x_2643_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2644_ = l_Std_Format_pretty(v___x_2641_, v___x_2642_, v___x_2643_, v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Lean_IR_formatDecl(
    mut v_decl_2653_: *mut crate::leanh::LeanObject,
    mut v_indent_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_2653_) == 0 {
        let mut v_f_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2660_: u8 = 0;
        let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_f_2655_ = crate::leanh::lean_ctor_get(v_decl_2653_, 0);
        crate::leanh::lean_inc(v_f_2655_);
        v_xs_2656_ = crate::leanh::lean_ctor_get(v_decl_2653_, 1);
        crate::leanh::lean_inc_ref(v_xs_2656_);
        v_type_2657_ = crate::leanh::lean_ctor_get(v_decl_2653_, 2);
        crate::leanh::lean_inc(v_type_2657_);
        v_body_2658_ = crate::leanh::lean_ctor_get(v_decl_2653_, 3);
        crate::leanh::lean_inc(v_body_2658_);
        crate::leanh::lean_dec_ref_known(v_decl_2653_, 5);
        v___x_2659_ = l_Lean_IR_formatDecl___closed__1;
        v___x_2660_ = 1;
        v___x_2661_ = l_Lean_Name_toString(v_f_2655_, v___x_2660_);
        v___x_2662_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2662_, 0, v___x_2661_);
        v___x_2663_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2659_);
        crate::leanh::lean_ctor_set(v___x_2663_, 1, v___x_2662_);
        v___x_2664_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2656_);
        crate::leanh::lean_dec_ref(v_xs_2656_);
        v___x_2665_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2665_, 0, v___x_2663_);
        crate::leanh::lean_ctor_set(v___x_2665_, 1, v___x_2664_);
        v___x_2666_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
        v___x_2667_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2667_, 0, v___x_2665_);
        crate::leanh::lean_ctor_set(v___x_2667_, 1, v___x_2666_);
        v___x_2668_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_2657_);
        v___x_2669_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2669_, 0, v___x_2667_);
        crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2668_);
        v___x_2670_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3;
        v___x_2671_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2671_, 0, v___x_2669_);
        crate::leanh::lean_ctor_set(v___x_2671_, 1, v___x_2670_);
        crate::leanh::lean_inc(v_indent_2654_);
        v___x_2672_ = lean_nat_to_int(v_indent_2654_);
        v___x_2673_ = crate::leanh::lean_box(1);
        v___x_2674_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
            v_indent_2654_,
            v_body_2658_,
        );
        v___x_2675_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2675_, 0, v___x_2673_);
        crate::leanh::lean_ctor_set(v___x_2675_, 1, v___x_2674_);
        v___x_2676_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2672_);
        crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
        v___x_2677_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2677_, 0, v___x_2671_);
        crate::leanh::lean_ctor_set(v___x_2677_, 1, v___x_2676_);
        return v___x_2677_;
    } else {
        let mut v_f_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_indent_2654_);
        v_f_2678_ = crate::leanh::lean_ctor_get(v_decl_2653_, 0);
        crate::leanh::lean_inc(v_f_2678_);
        v_xs_2679_ = crate::leanh::lean_ctor_get(v_decl_2653_, 1);
        crate::leanh::lean_inc_ref(v_xs_2679_);
        v_type_2680_ = crate::leanh::lean_ctor_get(v_decl_2653_, 2);
        crate::leanh::lean_inc(v_type_2680_);
        crate::leanh::lean_dec_ref_known(v_decl_2653_, 4);
        v___x_2681_ = l_Lean_IR_formatDecl___closed__3;
        v___x_2682_ = 1;
        v___x_2683_ = l_Lean_Name_toString(v_f_2678_, v___x_2682_);
        v___x_2684_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
        v___x_2685_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2685_, 0, v___x_2681_);
        crate::leanh::lean_ctor_set(v___x_2685_, 1, v___x_2684_);
        v___x_2686_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2679_);
        crate::leanh::lean_dec_ref(v_xs_2679_);
        v___x_2687_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2685_);
        crate::leanh::lean_ctor_set(v___x_2687_, 1, v___x_2686_);
        v___x_2688_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
        v___x_2689_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2689_, 0, v___x_2687_);
        crate::leanh::lean_ctor_set(v___x_2689_, 1, v___x_2688_);
        v___x_2690_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_2680_);
        v___x_2691_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2691_, 0, v___x_2689_);
        crate::leanh::lean_ctor_set(v___x_2691_, 1, v___x_2690_);
        return v___x_2691_;
    }
}
pub unsafe fn l_Lean_IR_instToFormatDecl___lam__0(
    mut v_decl_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2694_ = l_Lean_IR_formatDecl(v_decl_2692_, v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_IR_declToString(
    mut v_d_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2699_ = l_Lean_IR_formatDecl(v_d_2697_, v___x_2698_);
    v___x_2700_ = l_Std_Format_defWidth;
    v___x_2701_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2702_ = l_Std_Format_pretty(v___x_2699_, v___x_2700_, v___x_2701_, v___x_2701_);
    return v___x_2702_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Format(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Format(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Format(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Format(builtin);
}
