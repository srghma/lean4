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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value:
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
    m_data: [120, 95, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_IR_instToFormatArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instToFormatArg___private__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instToFormatArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___lam__0___closed__0_value: LeanStringObject<2> =
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
        m_data: [32, 0],
    };
static mut l_Lean_IR_formatArray___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_formatArray___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_formatArray___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_formatArray___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_formatArray___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_IR_formatArray___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_formatArray___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatArray___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_IR_instToFormatLitVal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatLitVal___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatLitVal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatLitVal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatLitVal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatLitVal___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value:
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value:
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value:
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__6_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7_value
) as *mut LeanObject;
pub static l_Lean_IR_instToFormatCtorInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatCtorInfo___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatCtorInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatCtorInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatCtorInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatCtorInfo___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value:
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
    m_data: [93, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value:
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
    m_data: [32, 105, 110, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__6_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value:
    LeanStringObject<1> = LeanStringObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value:
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
    m_data: [33, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__10_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__14_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value:
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
    m_data: [44, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__16_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value:
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
    m_data: [112, 97, 112, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__18_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__19_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value:
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
    m_data: [97, 112, 112, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__20_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value:
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
    m_data: [98, 111, 120, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__22_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__24_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__25_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__26_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27_value
)
    as *mut LeanObject;
pub static l_Lean_IR_instToFormatExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instToFormatExpr___private__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instToFormatExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instToStringExpr___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instToStringExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value:
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
    m_data: [117, 56, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__6_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__8_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__10_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__12_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__13_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value:
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
    m_data: [116, 111, 98, 106, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__14_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__15_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value:
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
    m_data: [102, 108, 111, 97, 116, 51, 50, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__16_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__17_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value:
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
    m_data: [115, 116, 114, 117, 99, 116, 32, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__18_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__19_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value:
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
    m_data: [123, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value
) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value:
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
    m_data: [125, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__21_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__26_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__28_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__29_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value:
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
    m_data: [118, 111, 105, 100, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__30_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__31_value
) as *mut LeanObject;
pub static l_Lean_IR_instToFormatIRType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatIRType___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatIRType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatIRType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringIRType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringIRType___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringIRType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringIRType___closed__1_value: LeanClosureObject<5> =
    LeanClosureObject {
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
            core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instToFormatIRType___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instToStringIRType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringIRType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringIRType___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value:
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
    m_data: [40, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value:
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
    m_data: [41, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__6_value
)
    as *mut LeanObject;
pub static l_Lean_IR_instToFormatParam___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatParam___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatParam___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatParam: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatParam___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatAlt___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatAlt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatAlt___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatAlt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_formatAlt___closed__2_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatAlt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_formatAlt___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatAlt___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatAlt___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__4_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__5_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__6_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__7_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__7_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__7_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__8_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__9_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__9_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__9_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__10_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__11_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__11_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__11_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__12_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__13_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__13_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__13_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__14_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__15_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__15_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__15_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__16_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__17_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__17_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__18_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__17_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__18_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__19_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__19_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__20_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__19_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__20_value) as *mut LeanObject;
static mut l_Lean_IR_formatFnBodyHead___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_formatFnBodyHead___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_formatFnBodyHead___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_formatFnBodyHead___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_formatFnBodyHead___closed__23_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__23_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__24_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__24_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__25_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__24_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__25_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__26_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__26_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__27_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__26_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__27_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__28_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__28_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__29_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__28_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__29_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__30_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__30_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__31_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__30_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__31_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__32_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__32_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__33_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__32_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__33_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__34_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__34_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__35_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__34_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__35_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__36_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatFnBodyHead___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__36_value) as *mut LeanObject;
pub static l_Lean_IR_formatFnBodyHead___closed__37_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__36_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatFnBodyHead___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatFnBodyHead___closed__37_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value:
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
    m_data: [59, 0],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value:
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
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5_value
) as *mut LeanObject;
pub static l_Lean_IR_instToFormatFnBody___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToFormatFnBody___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToFormatFnBody___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatFnBody___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatFnBody: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatFnBody___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringFnBody___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringFnBody___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringFnBody___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringFnBody___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringFnBody: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringFnBody___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatDecl___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_formatDecl___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_formatDecl___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_IR_formatDecl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_formatDecl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_IR_formatDecl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_formatDecl___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_instToFormatDecl___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instToFormatDecl___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instToFormatDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatDecl___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToFormatDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToFormatDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringDecl___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_declToString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instToStringDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringDecl___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringDecl___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(
    mut v_x_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1357_) == 0 {
                    v_id_1358_ = lean_ctor_get(v_x_1357_, 0);
                    v_isSharedCheck_1368_ = (!lean_is_exclusive(v_x_1357_)) as u8;
                    if v_isSharedCheck_1368_ == 0 {
                        v___x_1360_ = v_x_1357_;
                        v_isShared_1361_ = v_isSharedCheck_1368_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_id_1358_);
                        lean_dec(v_x_1357_);
                        v___x_1360_ = lean_box(0);
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
                lean_dec_ref(v___x_1363_);
                if v_isShared_1361_ == 0 {
                    lean_ctor_set_tag(v___x_1360_, 3);
                    lean_ctor_set(v___x_1360_, 0, v___x_1364_);
                    v___x_1366_ = v___x_1360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
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
    mut v_a_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_a_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Lean_IR_formatArray___redArg___lam__0(
    mut v_inst_1377_: *mut LeanObject,
    mut v_x1_1378_: *mut LeanObject,
    mut v_x2_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
    v___x_1381_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1381_, 0, v_x1_1378_);
    lean_ctor_set(v___x_1381_, 1, v___x_1380_);
    v___x_1382_ = lean_apply_1(v_inst_1377_, v_x2_1379_);
    v___x_1383_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1383_, 0, v___x_1381_);
    lean_ctor_set(v___x_1383_, 1, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn l_Lean_IR_formatArray___redArg(
    mut v_inst_1403_: *mut LeanObject,
    mut v_args_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    v___x_1405_ = lean_box(0);
    v___x_1406_ = lean_unsigned_to_nat(0);
    v___x_1407_ = lean_array_get_size(v_args_1404_);
    v___x_1408_ = l_Lean_IR_formatArray___redArg___closed__9;
    v___x_1409_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
    if v___x_1409_ == 0 {
        lean_dec_ref(v_args_1404_);
        lean_dec_ref(v_inst_1403_);
        return v___x_1405_;
    } else {
        let mut v___f_1410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1411_: u8 = 0;
        v___f_1410_ = lean_alloc_closure(
            l_Lean_IR_formatArray___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1410_, 0, v_inst_1403_);
        v___x_1411_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
        if v___x_1411_ == 0 {
            if v___x_1409_ == 0 {
                lean_dec_ref(v___f_1410_);
                lean_dec_ref(v_args_1404_);
                return v___x_1405_;
            } else {
                let mut v___x_1412_: usize = 0;
                let mut v___x_1413_: usize = 0;
                let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
                v___x_1412_ = 0usize;
                v___x_1413_ = lean_usize_of_nat(v___x_1407_);
                v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
            v___x_1415_ = 0usize;
            v___x_1416_ = lean_usize_of_nat(v___x_1407_);
            v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_1418_: *mut LeanObject,
    mut v_inst_1419_: *mut LeanObject,
    mut v_args_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_Lean_IR_formatArray___redArg(v_inst_1419_, v_args_1420_);
    return v___x_1421_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(
    mut v_x_1422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut v_v_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1422_) == 0 {
                    v_v_1423_ = lean_ctor_get(v_x_1422_, 0);
                    v_isSharedCheck_1431_ = (!lean_is_exclusive(v_x_1422_)) as u8;
                    if v_isSharedCheck_1431_ == 0 {
                        v___x_1425_ = v_x_1422_;
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_1423_);
                        lean_dec(v_x_1422_);
                        v___x_1425_ = lean_box(0);
                        v_isShared_1426_ = v_isSharedCheck_1431_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_1432_ = lean_ctor_get(v_x_1422_, 0);
                    v_isSharedCheck_1440_ = (!lean_is_exclusive(v_x_1422_)) as u8;
                    if v_isSharedCheck_1440_ == 0 {
                        v___x_1434_ = v_x_1422_;
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_v_1432_);
                        lean_dec(v_x_1422_);
                        v___x_1434_ = lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1440_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1427_ = l_Nat_reprFast(v_v_1423_);
                if v_isShared_1426_ == 0 {
                    lean_ctor_set_tag(v___x_1425_, 3);
                    lean_ctor_set(v___x_1425_, 0, v___x_1427_);
                    v___x_1429_ = v___x_1425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1430_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
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
                    lean_ctor_set_tag(v___x_1434_, 3);
                    lean_ctor_set(v___x_1434_, 0, v___x_1436_);
                    v___x_1438_ = v___x_1434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
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
    mut v_a_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_a_1441_);
    return v___x_1442_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(
    mut v_x_1457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1458_ = lean_ctor_get(v_x_1457_, 0);
                lean_inc(v_name_1458_);
                v_cidx_1459_ = lean_ctor_get(v_x_1457_, 1);
                lean_inc(v_cidx_1459_);
                v_usize_1460_ = lean_ctor_get(v_x_1457_, 3);
                lean_inc(v_usize_1460_);
                v_ssize_1461_ = lean_ctor_get(v_x_1457_, 4);
                lean_inc(v_ssize_1461_);
                lean_dec_ref(v_x_1457_);
                v___x_1474_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__5;
                v___x_1475_ = l_Nat_reprFast(v_cidx_1459_);
                v___x_1476_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1476_, 0, v___x_1475_);
                v_r_1477_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v_r_1477_, 0, v___x_1474_);
                lean_ctor_set(v_r_1477_, 1, v___x_1476_);
                v___x_1489_ = lean_unsigned_to_nat(0);
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
                v___x_1464_ = lean_box(0);
                v___x_1465_ = lean_name_eq(v_name_1458_, v___x_1464_);
                if v___x_1465_ == 0 {
                    v___x_1466_ = 1;
                    v___x_1467_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_1468_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1468_, 0, v_r_1463_);
                    lean_ctor_set(v___x_1468_, 1, v___x_1467_);
                    v___x_1469_ = l_Lean_Name_toString(v_name_1458_, v___x_1466_);
                    v___x_1470_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1470_, 0, v___x_1469_);
                    v___x_1471_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1471_, 0, v___x_1468_);
                    lean_ctor_set(v___x_1471_, 1, v___x_1470_);
                    v___x_1472_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                    v_r_1473_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_r_1473_, 0, v___x_1471_);
                    lean_ctor_set(v_r_1473_, 1, v___x_1472_);
                    return v_r_1473_;
                } else {
                    lean_dec(v_name_1458_);
                    return v_r_1463_;
                }
            }
            2 => {
                if v___y_1479_ == 0 {
                    lean_dec(v_ssize_1461_);
                    lean_dec(v_usize_1460_);
                    v_r_1463_ = v_r_1477_;
                    state = 1;
                    continue;
                } else {
                    v___x_1480_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__7;
                    v___x_1481_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1481_, 0, v_r_1477_);
                    lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                    v___x_1482_ = l_Nat_reprFast(v_usize_1460_);
                    v___x_1483_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1483_, 0, v___x_1482_);
                    v___x_1484_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1484_, 0, v___x_1481_);
                    lean_ctor_set(v___x_1484_, 1, v___x_1483_);
                    v___x_1485_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                    lean_ctor_set(v___x_1485_, 1, v___x_1480_);
                    v___x_1486_ = l_Nat_reprFast(v_ssize_1461_);
                    v___x_1487_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1487_, 0, v___x_1486_);
                    v_r_1488_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_r_1488_, 0, v___x_1485_);
                    lean_ctor_set(v_r_1488_, 1, v___x_1487_);
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
    mut v_a_1492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_a_1492_);
    return v___x_1493_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(
    mut v_as_1496_: *mut LeanObject,
    mut v_i_1497_: usize,
    mut v_stop_1498_: usize,
    mut v_b_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_1503_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1503_, 0, v_b_1499_);
                    lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                    lean_inc(v___x_1501_);
                    v___x_1504_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v___x_1501_);
                    v___x_1505_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                    lean_ctor_set(v___x_1505_, 1, v___x_1504_);
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
    mut v_as_1509_: *mut LeanObject,
    mut v_i_1510_: *mut LeanObject,
    mut v_stop_1511_: *mut LeanObject,
    mut v_b_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1513_: usize = 0;
    let mut v_stop_boxed_1514_: usize = 0;
    let mut v_res_1515_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
    lean_dec(v_i_1510_);
    v_stop_boxed_1514_ = lean_unbox_usize(v_stop_1511_);
    lean_dec(v_stop_1511_);
    v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_, v_b_1512_);
    lean_dec_ref(v_as_1509_);
    return v_res_1515_;
}
pub unsafe fn l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(
    mut v_args_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    v___x_1517_ = lean_box(0);
    v___x_1518_ = lean_unsigned_to_nat(0);
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
                let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
                v___x_1522_ = 0usize;
                v___x_1523_ = lean_usize_of_nat(v___x_1519_);
                v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_1516_, v___x_1522_, v___x_1523_, v___x_1517_);
                return v___x_1524_;
            }
        } else {
            let mut v___x_1525_: usize = 0;
            let mut v___x_1526_: usize = 0;
            let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
            v___x_1525_ = 0usize;
            v___x_1526_ = lean_usize_of_nat(v___x_1519_);
            v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(v_args_1516_, v___x_1525_, v___x_1526_, v___x_1517_);
            return v___x_1527_;
        }
    }
}
pub unsafe fn l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(
    mut v_args_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1529_: *mut LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_args_1528_);
    lean_dec_ref(v_args_1528_);
    return v_res_1529_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(
    mut v_x_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_n_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_1604_: u8 = 0;
    let mut v_ys_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_i_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_n_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut v_c_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1700_: u8 = 0;
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut v_x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1715_: u8 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1726_: u8 = 0;
    let mut v_x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_unused_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_v_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1759_: u8 = 0;
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_1571_) {
                    0 => {
                        v_i_1572_ = lean_ctor_get(v_x_1571_, 0);
                        v_ys_1573_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1582_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1582_ == 0 {
                            v___x_1575_ = v_x_1571_;
                            v_isShared_1576_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_ys_1573_);
                            lean_inc(v_i_1572_);
                            lean_dec(v_x_1571_);
                            v___x_1575_ = lean_box(0);
                            v_isShared_1576_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_n_1583_ = lean_ctor_get(v_x_1571_, 0);
                        v_x_1584_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1601_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1601_ == 0 {
                            v___x_1586_ = v_x_1571_;
                            v_isShared_1587_ = v_isSharedCheck_1601_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_x_1584_);
                            lean_inc(v_n_1583_);
                            lean_dec(v_x_1571_);
                            v___x_1586_ = lean_box(0);
                            v_isShared_1587_ = v_isSharedCheck_1601_;
                            state = 3;
                            continue;
                        }
                    }
                    2 => {
                        v_x_1602_ = lean_ctor_get(v_x_1571_, 0);
                        lean_inc(v_x_1602_);
                        v_i_1603_ = lean_ctor_get(v_x_1571_, 1);
                        lean_inc_ref(v_i_1603_);
                        v_updtHeader_1604_ = lean_ctor_get_uint8(
                            v_x_1571_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_ys_1605_ = lean_ctor_get(v_x_1571_, 2);
                        lean_inc_ref(v_ys_1605_);
                        lean_dec_ref_known(v_x_1571_, 3);
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
                        v_i_1626_ = lean_ctor_get(v_x_1571_, 0);
                        v_x_1627_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1644_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1644_ == 0 {
                            v___x_1629_ = v_x_1571_;
                            v_isShared_1630_ = v_isSharedCheck_1644_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_x_1627_);
                            lean_inc(v_i_1626_);
                            lean_dec(v_x_1571_);
                            v___x_1629_ = lean_box(0);
                            v_isShared_1630_ = v_isSharedCheck_1644_;
                            state = 6;
                            continue;
                        }
                    }
                    4 => {
                        v_i_1645_ = lean_ctor_get(v_x_1571_, 0);
                        v_x_1646_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1663_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1663_ == 0 {
                            v___x_1648_ = v_x_1571_;
                            v_isShared_1649_ = v_isSharedCheck_1663_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_x_1646_);
                            lean_inc(v_i_1645_);
                            lean_dec(v_x_1571_);
                            v___x_1648_ = lean_box(0);
                            v_isShared_1649_ = v_isSharedCheck_1663_;
                            state = 8;
                            continue;
                        }
                    }
                    5 => {
                        v_n_1664_ = lean_ctor_get(v_x_1571_, 0);
                        lean_inc(v_n_1664_);
                        v_offset_1665_ = lean_ctor_get(v_x_1571_, 1);
                        lean_inc(v_offset_1665_);
                        v_x_1666_ = lean_ctor_get(v_x_1571_, 2);
                        lean_inc(v_x_1666_);
                        lean_dec_ref_known(v_x_1571_, 3);
                        v___x_1667_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__15;
                        v___x_1668_ = l_Nat_reprFast(v_n_1664_);
                        v___x_1669_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_1669_, 0, v___x_1668_);
                        v___x_1670_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1670_, 0, v___x_1667_);
                        lean_ctor_set(v___x_1670_, 1, v___x_1669_);
                        v___x_1671_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                        v___x_1672_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1672_, 0, v___x_1670_);
                        lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                        v___x_1673_ = l_Nat_reprFast(v_offset_1665_);
                        v___x_1674_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_1674_, 0, v___x_1673_);
                        v___x_1675_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1675_, 0, v___x_1672_);
                        lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                        v___x_1676_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                        v___x_1677_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1677_, 0, v___x_1675_);
                        lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                        v___x_1678_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                        v___x_1679_ = l_Nat_reprFast(v_x_1666_);
                        v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
                        lean_dec_ref(v___x_1679_);
                        v___x_1681_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_1681_, 0, v___x_1680_);
                        v___x_1682_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1682_, 0, v___x_1677_);
                        lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                        return v___x_1682_;
                    }
                    6 => {
                        v_c_1683_ = lean_ctor_get(v_x_1571_, 0);
                        v_ys_1684_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1695_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1695_ == 0 {
                            v___x_1686_ = v_x_1571_;
                            v_isShared_1687_ = v_isSharedCheck_1695_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_ys_1684_);
                            lean_inc(v_c_1683_);
                            lean_dec(v_x_1571_);
                            v___x_1686_ = lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1695_;
                            state = 10;
                            continue;
                        }
                    }
                    7 => {
                        v_c_1696_ = lean_ctor_get(v_x_1571_, 0);
                        v_ys_1697_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1710_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1710_ == 0 {
                            v___x_1699_ = v_x_1571_;
                            v_isShared_1700_ = v_isSharedCheck_1710_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_ys_1697_);
                            lean_inc(v_c_1696_);
                            lean_dec(v_x_1571_);
                            v___x_1699_ = lean_box(0);
                            v_isShared_1700_ = v_isSharedCheck_1710_;
                            state = 12;
                            continue;
                        }
                    }
                    8 => {
                        v_x_1711_ = lean_ctor_get(v_x_1571_, 0);
                        v_ys_1712_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1726_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1726_ == 0 {
                            v___x_1714_ = v_x_1571_;
                            v_isShared_1715_ = v_isSharedCheck_1726_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_ys_1712_);
                            lean_inc(v_x_1711_);
                            lean_dec(v_x_1571_);
                            v___x_1714_ = lean_box(0);
                            v_isShared_1715_ = v_isSharedCheck_1726_;
                            state = 14;
                            continue;
                        }
                    }
                    9 => {
                        v_x_1727_ = lean_ctor_get(v_x_1571_, 1);
                        v_isSharedCheck_1739_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1739_ == 0 {
                            v_unused_1740_ = lean_ctor_get(v_x_1571_, 0);
                            lean_dec(v_unused_1740_);
                            v___x_1729_ = v_x_1571_;
                            v_isShared_1730_ = v_isSharedCheck_1739_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_x_1727_);
                            lean_dec(v_x_1571_);
                            v___x_1729_ = lean_box(0);
                            v_isShared_1730_ = v_isSharedCheck_1739_;
                            state = 16;
                            continue;
                        }
                    }
                    10 => {
                        v_x_1741_ = lean_ctor_get(v_x_1571_, 0);
                        v_isSharedCheck_1753_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1753_ == 0 {
                            v___x_1743_ = v_x_1571_;
                            v_isShared_1744_ = v_isSharedCheck_1753_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_x_1741_);
                            lean_dec(v_x_1571_);
                            v___x_1743_ = lean_box(0);
                            v_isShared_1744_ = v_isSharedCheck_1753_;
                            state = 18;
                            continue;
                        }
                    }
                    11 => {
                        v_v_1754_ = lean_ctor_get(v_x_1571_, 0);
                        lean_inc_ref(v_v_1754_);
                        lean_dec_ref_known(v_x_1571_, 1);
                        v___x_1755_ =
                            l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(v_v_1754_);
                        return v___x_1755_;
                    }
                    _ => {
                        v_x_1756_ = lean_ctor_get(v_x_1571_, 0);
                        v_isSharedCheck_1768_ = (!lean_is_exclusive(v_x_1571_)) as u8;
                        if v_isSharedCheck_1768_ == 0 {
                            v___x_1758_ = v_x_1571_;
                            v_isShared_1759_ = v_isSharedCheck_1768_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_x_1756_);
                            lean_dec(v_x_1571_);
                            v___x_1758_ = lean_box(0);
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
                lean_dec_ref(v_ys_1573_);
                if v_isShared_1576_ == 0 {
                    lean_ctor_set_tag(v___x_1575_, 5);
                    lean_ctor_set(v___x_1575_, 1, v___x_1578_);
                    lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1580_ = v___x_1575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
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
                v___x_1590_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                if v_isShared_1587_ == 0 {
                    lean_ctor_set_tag(v___x_1586_, 5);
                    lean_ctor_set(v___x_1586_, 1, v___x_1590_);
                    lean_ctor_set(v___x_1586_, 0, v___x_1588_);
                    v___x_1592_ = v___x_1586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1588_);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1590_);
                    v___x_1592_ = v_reuseFailAlloc_1600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1593_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1594_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1594_, 0, v___x_1592_);
                lean_ctor_set(v___x_1594_, 1, v___x_1593_);
                v___x_1595_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1596_ = l_Nat_reprFast(v_x_1584_);
                v___x_1597_ = lean_string_append(v___x_1595_, v___x_1596_);
                lean_dec_ref(v___x_1596_);
                v___x_1598_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1598_, 0, v___x_1597_);
                v___x_1599_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1599_, 0, v___x_1594_);
                lean_ctor_set(v___x_1599_, 1, v___x_1598_);
                return v___x_1599_;
            }
            5 => {
                lean_inc_ref(v___y_1608_);
                v___x_1609_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1609_, 0, v___y_1608_);
                v___x_1610_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1610_, 0, v___x_1606_);
                lean_ctor_set(v___x_1610_, 1, v___x_1609_);
                v___x_1611_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_1612_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1612_, 0, v___x_1610_);
                lean_ctor_set(v___x_1612_, 1, v___x_1611_);
                v___x_1613_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1614_ = l_Nat_reprFast(v_x_1602_);
                v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
                lean_dec_ref(v___x_1614_);
                v___x_1616_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1616_, 0, v___x_1615_);
                v___x_1617_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1617_, 0, v___x_1612_);
                lean_ctor_set(v___x_1617_, 1, v___x_1616_);
                v___x_1618_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__7;
                v___x_1619_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1619_, 0, v___x_1617_);
                lean_ctor_set(v___x_1619_, 1, v___x_1618_);
                v___x_1620_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(v_i_1603_);
                v___x_1621_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1621_, 0, v___x_1619_);
                lean_ctor_set(v___x_1621_, 1, v___x_1620_);
                v___x_1622_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1605_);
                lean_dec_ref(v_ys_1605_);
                v___x_1623_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1623_, 0, v___x_1621_);
                lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                return v___x_1623_;
            }
            6 => {
                v___x_1631_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__11;
                v___x_1632_ = l_Nat_reprFast(v_i_1626_);
                v___x_1633_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1633_, 0, v___x_1632_);
                if v_isShared_1630_ == 0 {
                    lean_ctor_set_tag(v___x_1629_, 5);
                    lean_ctor_set(v___x_1629_, 1, v___x_1633_);
                    lean_ctor_set(v___x_1629_, 0, v___x_1631_);
                    v___x_1635_ = v___x_1629_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1643_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1631_);
                    lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1633_);
                    v___x_1635_ = v_reuseFailAlloc_1643_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1636_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1637_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1637_, 0, v___x_1635_);
                lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                v___x_1638_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1639_ = l_Nat_reprFast(v_x_1627_);
                v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
                lean_dec_ref(v___x_1639_);
                v___x_1641_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1641_, 0, v___x_1640_);
                v___x_1642_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1642_, 0, v___x_1637_);
                lean_ctor_set(v___x_1642_, 1, v___x_1641_);
                return v___x_1642_;
            }
            8 => {
                v___x_1650_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__13;
                v___x_1651_ = l_Nat_reprFast(v_i_1645_);
                v___x_1652_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1652_, 0, v___x_1651_);
                if v_isShared_1649_ == 0 {
                    lean_ctor_set_tag(v___x_1648_, 5);
                    lean_ctor_set(v___x_1648_, 1, v___x_1652_);
                    lean_ctor_set(v___x_1648_, 0, v___x_1650_);
                    v___x_1654_ = v___x_1648_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1650_);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1652_);
                    v___x_1654_ = v_reuseFailAlloc_1662_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1655_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__3;
                v___x_1656_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1656_, 0, v___x_1654_);
                lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                v___x_1657_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1658_ = l_Nat_reprFast(v_x_1646_);
                v___x_1659_ = lean_string_append(v___x_1657_, v___x_1658_);
                lean_dec_ref(v___x_1658_);
                v___x_1660_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1660_, 0, v___x_1659_);
                v___x_1661_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1661_, 0, v___x_1656_);
                lean_ctor_set(v___x_1661_, 1, v___x_1660_);
                return v___x_1661_;
            }
            10 => {
                v___x_1688_ = 1;
                v___x_1689_ = l_Lean_Name_toString(v_c_1683_, v___x_1688_);
                v___x_1690_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1690_, 0, v___x_1689_);
                v___x_1691_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1684_);
                lean_dec_ref(v_ys_1684_);
                if v_isShared_1687_ == 0 {
                    lean_ctor_set_tag(v___x_1686_, 5);
                    lean_ctor_set(v___x_1686_, 1, v___x_1691_);
                    lean_ctor_set(v___x_1686_, 0, v___x_1690_);
                    v___x_1693_ = v___x_1686_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
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
                v___x_1704_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                if v_isShared_1700_ == 0 {
                    lean_ctor_set_tag(v___x_1699_, 5);
                    lean_ctor_set(v___x_1699_, 1, v___x_1704_);
                    lean_ctor_set(v___x_1699_, 0, v___x_1701_);
                    v___x_1706_ = v___x_1699_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1701_);
                    lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1704_);
                    v___x_1706_ = v_reuseFailAlloc_1709_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1707_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1697_);
                lean_dec_ref(v_ys_1697_);
                v___x_1708_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1708_, 0, v___x_1706_);
                lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                return v___x_1708_;
            }
            14 => {
                v___x_1716_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__21;
                v___x_1717_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1718_ = l_Nat_reprFast(v_x_1711_);
                v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
                lean_dec_ref(v___x_1718_);
                v___x_1720_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1720_, 0, v___x_1719_);
                if v_isShared_1715_ == 0 {
                    lean_ctor_set_tag(v___x_1714_, 5);
                    lean_ctor_set(v___x_1714_, 1, v___x_1720_);
                    lean_ctor_set(v___x_1714_, 0, v___x_1716_);
                    v___x_1722_ = v___x_1714_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1716_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1720_);
                    v___x_1722_ = v_reuseFailAlloc_1725_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_1723_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_1712_);
                lean_dec_ref(v_ys_1712_);
                v___x_1724_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1724_, 0, v___x_1722_);
                lean_ctor_set(v___x_1724_, 1, v___x_1723_);
                return v___x_1724_;
            }
            16 => {
                v___x_1731_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__23;
                v___x_1732_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1733_ = l_Nat_reprFast(v_x_1727_);
                v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
                lean_dec_ref(v___x_1733_);
                v___x_1735_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1735_, 0, v___x_1734_);
                if v_isShared_1730_ == 0 {
                    lean_ctor_set_tag(v___x_1729_, 5);
                    lean_ctor_set(v___x_1729_, 1, v___x_1735_);
                    lean_ctor_set(v___x_1729_, 0, v___x_1731_);
                    v___x_1737_ = v___x_1729_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1731_);
                    lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
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
                lean_dec_ref(v___x_1747_);
                if v_isShared_1744_ == 0 {
                    lean_ctor_set_tag(v___x_1743_, 3);
                    lean_ctor_set(v___x_1743_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1743_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1748_);
                    v___x_1750_ = v_reuseFailAlloc_1752_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1751_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1751_, 0, v___x_1745_);
                lean_ctor_set(v___x_1751_, 1, v___x_1750_);
                return v___x_1751_;
            }
            20 => {
                v___x_1760_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__27;
                v___x_1761_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1762_ = l_Nat_reprFast(v_x_1756_);
                v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
                lean_dec_ref(v___x_1762_);
                if v_isShared_1759_ == 0 {
                    lean_ctor_set_tag(v___x_1758_, 3);
                    lean_ctor_set(v___x_1758_, 0, v___x_1763_);
                    v___x_1765_ = v___x_1758_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1763_);
                    v___x_1765_ = v_reuseFailAlloc_1767_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1766_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1766_, 0, v___x_1760_);
                lean_ctor_set(v___x_1766_, 1, v___x_1765_);
                return v___x_1766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatExpr___private__1(
    mut v_a_1769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_a_1769_);
    return v___x_1770_;
}
pub unsafe fn l_Lean_IR_instToStringExpr___lam__0(
    mut v_e_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1774_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_1773_);
    v___x_1775_ = l_Std_Format_defWidth;
    v___x_1776_ = lean_unsigned_to_nat(0);
    v___x_1777_ = l_Std_Format_pretty(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__1(
    mut v_a_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    v___x_1781_ = lean_nat_to_int(v_a_1780_);
    return v___x_1781_;
}
pub unsafe fn l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(
    mut v_x_1812_: *mut LeanObject,
    mut v_x_1813_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1812_) == 0 {
        let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1813_);
        v___x_1814_ = lean_box(0);
        return v___x_1814_;
    } else {
        let mut v_tail_1815_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1815_ = lean_ctor_get(v_x_1812_, 1);
        if lean_obj_tag(v_tail_1815_) == 0 {
            let mut v_head_1816_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1813_);
            v_head_1816_ = lean_ctor_get(v_x_1812_, 0);
            lean_inc(v_head_1816_);
            lean_dec_ref_known(v_x_1812_, 2);
            v___x_1817_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1816_);
            return v___x_1817_;
        } else {
            let mut v_head_1818_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1815_);
            v_head_1818_ = lean_ctor_get(v_x_1812_, 0);
            lean_inc(v_head_1818_);
            lean_dec_ref_known(v_x_1812_, 2);
            v___x_1819_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1818_);
            v___x_1820_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(v_x_1813_, v___x_1819_, v_tail_1815_);
            return v___x_1820_;
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__22()
-> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__20;
    v___x_1823_ = lean_string_length(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23()
-> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1824_ = lean_obj_once(
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
    mut v_x_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_types_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_unused_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_types_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_unused_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_1840_) {
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
                        v_types_1851_ = lean_ctor_get(v_x_1840_, 1);
                        v_isSharedCheck_1870_ = (!lean_is_exclusive(v_x_1840_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v_unused_1871_ = lean_ctor_get(v_x_1840_, 0);
                            lean_dec(v_unused_1871_);
                            v___x_1853_ = v_x_1840_;
                            v_isShared_1854_ = v_isSharedCheck_1870_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_types_1851_);
                            lean_dec(v_x_1840_);
                            v___x_1853_ = lean_box(0);
                            v_isShared_1854_ = v_isSharedCheck_1870_;
                            state = 1;
                            continue;
                        }
                    }
                    11 => {
                        v_types_1872_ = lean_ctor_get(v_x_1840_, 1);
                        v_isSharedCheck_1891_ = (!lean_is_exclusive(v_x_1840_)) as u8;
                        if v_isSharedCheck_1891_ == 0 {
                            v_unused_1892_ = lean_ctor_get(v_x_1840_, 0);
                            lean_dec(v_unused_1892_);
                            v___x_1874_ = v_x_1840_;
                            v_isShared_1875_ = v_isSharedCheck_1891_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_types_1872_);
                            lean_dec(v_x_1840_);
                            v___x_1874_ = lean_box(0);
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
                v___x_1859_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once), _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
                v___x_1860_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24;
                if v_isShared_1854_ == 0 {
                    lean_ctor_set_tag(v___x_1853_, 5);
                    lean_ctor_set(v___x_1853_, 1, v___x_1858_);
                    lean_ctor_set(v___x_1853_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1860_);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1858_);
                    v___x_1862_ = v_reuseFailAlloc_1869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1863_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25;
                v___x_1864_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1864_, 0, v___x_1862_);
                lean_ctor_set(v___x_1864_, 1, v___x_1863_);
                v___x_1865_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1865_, 0, v___x_1859_);
                lean_ctor_set(v___x_1865_, 1, v___x_1864_);
                v___x_1866_ = 0;
                v___x_1867_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1867_, 0, v___x_1865_);
                lean_ctor_set_uint8(
                    v___x_1867_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1866_,
                );
                v___x_1868_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1868_, 0, v___x_1855_);
                lean_ctor_set(v___x_1868_, 1, v___x_1867_);
                return v___x_1868_;
            }
            3 => {
                v___x_1876_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__27;
                v___x_1877_ = lean_array_to_list(v_types_1872_);
                v___x_1878_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                v___x_1879_ = l_Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(v___x_1877_, v___x_1878_);
                v___x_1880_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23_once), _init_l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__23);
                v___x_1881_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__24;
                if v_isShared_1875_ == 0 {
                    lean_ctor_set_tag(v___x_1874_, 5);
                    lean_ctor_set(v___x_1874_, 1, v___x_1879_);
                    lean_ctor_set(v___x_1874_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1881_);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1879_);
                    v___x_1883_ = v_reuseFailAlloc_1890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1884_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType___closed__25;
                v___x_1885_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1885_, 0, v___x_1883_);
                lean_ctor_set(v___x_1885_, 1, v___x_1884_);
                v___x_1886_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1886_, 0, v___x_1880_);
                lean_ctor_set(v___x_1886_, 1, v___x_1885_);
                v___x_1887_ = 0;
                v___x_1888_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1888_, 0, v___x_1886_);
                lean_ctor_set_uint8(
                    v___x_1888_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1887_,
                );
                v___x_1889_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1889_, 0, v___x_1876_);
                lean_ctor_set(v___x_1889_, 1, v___x_1888_);
                return v___x_1889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(
    mut v_x_1895_: *mut LeanObject,
    mut v_x_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1897_) == 0 {
                    lean_dec(v_x_1895_);
                    return v_x_1896_;
                } else {
                    v_head_1898_ = lean_ctor_get(v_x_1897_, 0);
                    v_tail_1899_ = lean_ctor_get(v_x_1897_, 1);
                    v_isSharedCheck_1909_ = (!lean_is_exclusive(v_x_1897_)) as u8;
                    if v_isSharedCheck_1909_ == 0 {
                        v___x_1901_ = v_x_1897_;
                        v_isShared_1902_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1899_);
                        lean_inc(v_head_1898_);
                        lean_dec(v_x_1897_);
                        v___x_1901_ = lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1895_);
                if v_isShared_1902_ == 0 {
                    lean_ctor_set_tag(v___x_1901_, 5);
                    lean_ctor_set(v___x_1901_, 1, v_x_1895_);
                    lean_ctor_set(v___x_1901_, 0, v_x_1896_);
                    v___x_1904_ = v___x_1901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_x_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_x_1895_);
                    v___x_1904_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1905_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_head_1898_);
                v___x_1906_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1906_, 0, v___x_1904_);
                lean_ctor_set(v___x_1906_, 1, v___x_1905_);
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
    mut v_a_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_a_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_IR_instToStringIRType___lam__0(
    mut v_f_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_Std_Format_defWidth;
    v___x_1916_ = lean_unsigned_to_nat(0);
    v___x_1917_ = l_Std_Format_pretty(v_f_1914_, v___x_1915_, v___x_1916_, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(
    mut v_x_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_1935_: u8 = 0;
    let mut v_ty_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_1934_ = lean_ctor_get(v_x_1933_, 0);
                lean_inc(v_x_1934_);
                v_borrow_1935_ = lean_ctor_get_uint8(
                    v_x_1933_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_ty_1936_ = lean_ctor_get(v_x_1933_, 1);
                lean_inc(v_ty_1936_);
                lean_dec_ref(v_x_1933_);
                v___x_1937_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__1;
                v___x_1938_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_1939_ = l_Nat_reprFast(v_x_1934_);
                v___x_1940_ = lean_string_append(v___x_1938_, v___x_1939_);
                lean_dec_ref(v___x_1939_);
                v___x_1941_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1941_, 0, v___x_1940_);
                v___x_1942_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1942_, 0, v___x_1937_);
                lean_ctor_set(v___x_1942_, 1, v___x_1941_);
                v___x_1943_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                v___x_1944_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1944_, 0, v___x_1942_);
                lean_ctor_set(v___x_1944_, 1, v___x_1943_);
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
                lean_inc_ref(v___y_1946_);
                v___x_1947_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1947_, 0, v___y_1946_);
                v___x_1948_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1948_, 0, v___x_1944_);
                lean_ctor_set(v___x_1948_, 1, v___x_1947_);
                v___x_1949_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_1936_);
                v___x_1950_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1950_, 0, v___x_1948_);
                lean_ctor_set(v___x_1950_, 1, v___x_1949_);
                v___x_1951_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__5;
                v___x_1952_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1952_, 0, v___x_1950_);
                lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                return v___x_1952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instToFormatParam___private__1(
    mut v_a_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1956_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v_a_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Lean_IR_formatAlt(
    mut v_fmt_1965_: *mut LeanObject,
    mut v_indent_1966_: *mut LeanObject,
    mut v_x_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v_name_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_b_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1967_) == 0 {
                    v_info_1968_ = lean_ctor_get(v_x_1967_, 0);
                    v_b_1969_ = lean_ctor_get(v_x_1967_, 1);
                    v_isSharedCheck_1987_ = (!lean_is_exclusive(v_x_1967_)) as u8;
                    if v_isSharedCheck_1987_ == 0 {
                        v___x_1971_ = v_x_1967_;
                        v_isShared_1972_ = v_isSharedCheck_1987_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_b_1969_);
                        lean_inc(v_info_1968_);
                        lean_dec(v_x_1967_);
                        v___x_1971_ = lean_box(0);
                        v_isShared_1972_ = v_isSharedCheck_1987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_b_1988_ = lean_ctor_get(v_x_1967_, 0);
                    lean_inc(v_b_1988_);
                    lean_dec_ref_known(v_x_1967_, 1);
                    v___x_1989_ = l_Lean_IR_formatAlt___closed__3;
                    v___x_1990_ = lean_nat_to_int(v_indent_1966_);
                    v___x_1991_ = lean_box(1);
                    v___x_1992_ = lean_apply_1(v_fmt_1965_, v_b_1988_);
                    v___x_1993_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1993_, 0, v___x_1991_);
                    lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                    v___x_1994_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v___x_1994_, 0, v___x_1990_);
                    lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                    v___x_1995_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1995_, 0, v___x_1989_);
                    lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    return v___x_1995_;
                }
            }
            1 => {
                v_name_1973_ = lean_ctor_get(v_info_1968_, 0);
                lean_inc(v_name_1973_);
                lean_dec_ref(v_info_1968_);
                v___x_1974_ = 1;
                v___x_1975_ = l_Lean_Name_toString(v_name_1973_, v___x_1974_);
                v___x_1976_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1976_, 0, v___x_1975_);
                v___x_1977_ = l_Lean_IR_formatAlt___closed__1;
                if v_isShared_1972_ == 0 {
                    lean_ctor_set_tag(v___x_1971_, 5);
                    lean_ctor_set(v___x_1971_, 1, v___x_1977_);
                    lean_ctor_set(v___x_1971_, 0, v___x_1976_);
                    v___x_1979_ = v___x_1971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1976_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1977_);
                    v___x_1979_ = v_reuseFailAlloc_1986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1980_ = lean_nat_to_int(v_indent_1966_);
                v___x_1981_ = lean_box(1);
                v___x_1982_ = lean_apply_1(v_fmt_1965_, v_b_1969_);
                v___x_1983_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                lean_ctor_set(v___x_1983_, 1, v___x_1982_);
                v___x_1984_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1984_, 0, v___x_1980_);
                lean_ctor_set(v___x_1984_, 1, v___x_1983_);
                v___x_1985_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1985_, 0, v___x_1979_);
                lean_ctor_set(v___x_1985_, 1, v___x_1984_);
                return v___x_1985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(
    mut v_as_1996_: *mut LeanObject,
    mut v_i_1997_: usize,
    mut v_stop_1998_: usize,
    mut v_b_1999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_2003_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2003_, 0, v_b_1999_);
                    lean_ctor_set(v___x_2003_, 1, v___x_2002_);
                    lean_inc(v___x_2001_);
                    v___x_2004_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(v___x_2001_);
                    v___x_2005_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2005_, 0, v___x_2003_);
                    lean_ctor_set(v___x_2005_, 1, v___x_2004_);
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
    mut v_as_2009_: *mut LeanObject,
    mut v_i_2010_: *mut LeanObject,
    mut v_stop_2011_: *mut LeanObject,
    mut v_b_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2013_: usize = 0;
    let mut v_stop_boxed_2014_: usize = 0;
    let mut v_res_2015_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2013_ = lean_unbox_usize(v_i_2010_);
    lean_dec(v_i_2010_);
    v_stop_boxed_2014_ = lean_unbox_usize(v_stop_2011_);
    lean_dec(v_stop_2011_);
    v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_as_2009_, v_i_boxed_2013_, v_stop_boxed_2014_, v_b_2012_);
    lean_dec_ref(v_as_2009_);
    return v_res_2015_;
}
pub unsafe fn l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(
    mut v_args_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u8 = 0;
    v___x_2017_ = lean_box(0);
    v___x_2018_ = lean_unsigned_to_nat(0);
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
                let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
                v___x_2022_ = 0usize;
                v___x_2023_ = lean_usize_of_nat(v___x_2019_);
                v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_2016_, v___x_2022_, v___x_2023_, v___x_2017_);
                return v___x_2024_;
            }
        } else {
            let mut v___x_2025_: usize = 0;
            let mut v___x_2026_: usize = 0;
            let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
            v___x_2025_ = 0usize;
            v___x_2026_ = lean_usize_of_nat(v___x_2019_);
            v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0_spec__0(v_args_2016_, v___x_2025_, v___x_2026_, v___x_2017_);
            return v___x_2027_;
        }
    }
}
pub unsafe fn l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0___boxed(
    mut v_args_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2029_: *mut LeanObject = core::ptr::null_mut();
    v_res_2029_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_args_2028_);
    lean_dec_ref(v_args_2028_);
    return v_res_2029_;
}
pub unsafe fn l_Lean_IR_formatParams(mut v_ps_2030_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_ps_2030_);
    return v___x_2031_;
}
pub unsafe fn l_Lean_IR_formatParams___boxed(mut v_ps_2032_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2033_: *mut LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Lean_IR_formatParams(v_ps_2032_);
    lean_dec_ref(v_ps_2032_);
    return v_res_2033_;
}
pub unsafe fn _init_l_Lean_IR_formatFnBodyHead___closed__21() -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__0;
    v___x_2066_ = lean_string_length(v___x_2065_);
    return v___x_2066_;
}
pub unsafe fn _init_l_Lean_IR_formatFnBodyHead___closed__22() -> *mut LeanObject {
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    v___x_2067_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__21),
        core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__21_once),
        _init_l_Lean_IR_formatFnBodyHead___closed__21,
    );
    v___x_2068_ = lean_nat_to_int(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lean_IR_formatFnBodyHead(mut v_x_2092_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v_unused_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2092_) {
                0 => {
                    v_x_2093_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2093_);
                    v_ty_2094_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_ty_2094_);
                    v_e_2095_ = lean_ctor_get(v_x_2092_, 2);
                    lean_inc_ref(v_e_2095_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2096_ = l_Lean_IR_formatFnBodyHead___closed__1;
                    v___x_2097_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2098_ = l_Nat_reprFast(v_x_2093_);
                    v___x_2099_ = lean_string_append(v___x_2097_, v___x_2098_);
                    lean_dec_ref(v___x_2098_);
                    v___x_2100_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2100_, 0, v___x_2099_);
                    v___x_2101_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2101_, 0, v___x_2096_);
                    lean_ctor_set(v___x_2101_, 1, v___x_2100_);
                    v___x_2102_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2103_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2103_, 0, v___x_2101_);
                    lean_ctor_set(v___x_2103_, 1, v___x_2102_);
                    v___x_2104_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2094_);
                    v___x_2105_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2105_, 0, v___x_2103_);
                    lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                    v___x_2106_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2107_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2107_, 0, v___x_2105_);
                    lean_ctor_set(v___x_2107_, 1, v___x_2106_);
                    v___x_2108_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_2095_);
                    v___x_2109_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2109_, 0, v___x_2107_);
                    lean_ctor_set(v___x_2109_, 1, v___x_2108_);
                    return v___x_2109_;
                }
                1 => {
                    v_j_2110_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_j_2110_);
                    v_xs_2111_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc_ref(v_xs_2111_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2112_ = l_Lean_IR_formatFnBodyHead___closed__4;
                    v___x_2113_ = l_Nat_reprFast(v_j_2110_);
                    v___x_2114_ = lean_string_append(v___x_2112_, v___x_2113_);
                    lean_dec_ref(v___x_2113_);
                    v___x_2115_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2115_, 0, v___x_2114_);
                    v___x_2116_ =
                        l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2111_);
                    lean_dec_ref(v_xs_2111_);
                    v___x_2117_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2117_, 0, v___x_2115_);
                    lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                    v___x_2118_ = l_Lean_IR_formatFnBodyHead___closed__6;
                    v___x_2119_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2119_, 0, v___x_2117_);
                    lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                    return v___x_2119_;
                }
                2 => {
                    v_x_2120_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2120_);
                    v_i_2121_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_i_2121_);
                    v_y_2122_ = lean_ctor_get(v_x_2092_, 2);
                    lean_inc(v_y_2122_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2123_ = l_Lean_IR_formatFnBodyHead___closed__8;
                    v___x_2124_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2125_ = l_Nat_reprFast(v_x_2120_);
                    v___x_2126_ = lean_string_append(v___x_2124_, v___x_2125_);
                    lean_dec_ref(v___x_2125_);
                    v___x_2127_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2127_, 0, v___x_2126_);
                    v___x_2128_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2128_, 0, v___x_2123_);
                    lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                    v___x_2129_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2130_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2130_, 0, v___x_2128_);
                    lean_ctor_set(v___x_2130_, 1, v___x_2129_);
                    v___x_2131_ = l_Nat_reprFast(v_i_2121_);
                    v___x_2132_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                    v___x_2133_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2133_, 0, v___x_2130_);
                    lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                    v___x_2134_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2135_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2135_, 0, v___x_2133_);
                    lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                    v___x_2136_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_2122_);
                    v___x_2137_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2137_, 0, v___x_2135_);
                    lean_ctor_set(v___x_2137_, 1, v___x_2136_);
                    return v___x_2137_;
                }
                3 => {
                    v_x_2138_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2138_);
                    v_cidx_2139_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_cidx_2139_);
                    lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2140_ = l_Lean_IR_formatFnBodyHead___closed__12;
                    v___x_2141_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2142_ = l_Nat_reprFast(v_x_2138_);
                    v___x_2143_ = lean_string_append(v___x_2141_, v___x_2142_);
                    lean_dec_ref(v___x_2142_);
                    v___x_2144_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2144_, 0, v___x_2143_);
                    v___x_2145_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2145_, 0, v___x_2140_);
                    lean_ctor_set(v___x_2145_, 1, v___x_2144_);
                    v___x_2146_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2147_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                    lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                    v___x_2148_ = l_Nat_reprFast(v_cidx_2139_);
                    v___x_2149_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2149_, 0, v___x_2148_);
                    v___x_2150_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2150_, 0, v___x_2147_);
                    lean_ctor_set(v___x_2150_, 1, v___x_2149_);
                    return v___x_2150_;
                }
                4 => {
                    v_x_2151_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2151_);
                    v_i_2152_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_i_2152_);
                    v_y_2153_ = lean_ctor_get(v_x_2092_, 2);
                    lean_inc(v_y_2153_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2154_ = l_Lean_IR_formatFnBodyHead___closed__14;
                    v___x_2155_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2156_ = l_Nat_reprFast(v_x_2151_);
                    v___x_2157_ = lean_string_append(v___x_2155_, v___x_2156_);
                    lean_dec_ref(v___x_2156_);
                    v___x_2158_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2158_, 0, v___x_2157_);
                    v___x_2159_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2159_, 0, v___x_2154_);
                    lean_ctor_set(v___x_2159_, 1, v___x_2158_);
                    v___x_2160_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2161_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2161_, 0, v___x_2159_);
                    lean_ctor_set(v___x_2161_, 1, v___x_2160_);
                    v___x_2162_ = l_Nat_reprFast(v_i_2152_);
                    v___x_2163_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2163_, 0, v___x_2162_);
                    v___x_2164_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2164_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2164_, 1, v___x_2163_);
                    v___x_2165_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2166_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2166_, 0, v___x_2164_);
                    lean_ctor_set(v___x_2166_, 1, v___x_2165_);
                    v___x_2167_ = l_Nat_reprFast(v_y_2153_);
                    v___x_2168_ = lean_string_append(v___x_2155_, v___x_2167_);
                    lean_dec_ref(v___x_2167_);
                    v___x_2169_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2169_, 0, v___x_2168_);
                    v___x_2170_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2170_, 0, v___x_2166_);
                    lean_ctor_set(v___x_2170_, 1, v___x_2169_);
                    return v___x_2170_;
                }
                5 => {
                    v_x_2171_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2171_);
                    v_i_2172_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_i_2172_);
                    v_offset_2173_ = lean_ctor_get(v_x_2092_, 2);
                    lean_inc(v_offset_2173_);
                    v_y_2174_ = lean_ctor_get(v_x_2092_, 3);
                    lean_inc(v_y_2174_);
                    v_ty_2175_ = lean_ctor_get(v_x_2092_, 4);
                    lean_inc(v_ty_2175_);
                    lean_dec_ref_known(v_x_2092_, 6);
                    v___x_2176_ = l_Lean_IR_formatFnBodyHead___closed__16;
                    v___x_2177_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2178_ = l_Nat_reprFast(v_x_2171_);
                    v___x_2179_ = lean_string_append(v___x_2177_, v___x_2178_);
                    lean_dec_ref(v___x_2178_);
                    v___x_2180_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2180_, 0, v___x_2179_);
                    v___x_2181_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2181_, 0, v___x_2176_);
                    lean_ctor_set(v___x_2181_, 1, v___x_2180_);
                    v___x_2182_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2183_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2183_, 0, v___x_2181_);
                    lean_ctor_set(v___x_2183_, 1, v___x_2182_);
                    v___x_2184_ = l_Nat_reprFast(v_i_2172_);
                    v___x_2185_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2185_, 0, v___x_2184_);
                    v___x_2186_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2186_, 0, v___x_2183_);
                    lean_ctor_set(v___x_2186_, 1, v___x_2185_);
                    v___x_2187_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                    v___x_2188_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2188_, 0, v___x_2186_);
                    lean_ctor_set(v___x_2188_, 1, v___x_2187_);
                    v___x_2189_ = l_Nat_reprFast(v_offset_2173_);
                    v___x_2190_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2190_, 0, v___x_2189_);
                    v___x_2191_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2191_, 0, v___x_2188_);
                    lean_ctor_set(v___x_2191_, 1, v___x_2190_);
                    v___x_2192_ = l_Lean_IR_formatFnBodyHead___closed__18;
                    v___x_2193_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2193_, 0, v___x_2191_);
                    lean_ctor_set(v___x_2193_, 1, v___x_2192_);
                    v___x_2194_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2175_);
                    v___x_2195_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2195_, 0, v___x_2193_);
                    lean_ctor_set(v___x_2195_, 1, v___x_2194_);
                    v___x_2196_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2197_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2197_, 0, v___x_2195_);
                    lean_ctor_set(v___x_2197_, 1, v___x_2196_);
                    v___x_2198_ = l_Nat_reprFast(v_y_2174_);
                    v___x_2199_ = lean_string_append(v___x_2177_, v___x_2198_);
                    lean_dec_ref(v___x_2198_);
                    v___x_2200_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                    v___x_2201_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2201_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                    return v___x_2201_;
                }
                6 => {
                    v_x_2202_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2202_);
                    v_n_2203_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_n_2203_);
                    lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2204_ = l_Lean_IR_formatFnBodyHead___closed__20;
                    v___x_2215_ = lean_unsigned_to_nat(1);
                    v___x_2216_ = lean_nat_dec_eq(v_n_2203_, v___x_2215_);
                    if v___x_2216_ == 0 {
                        v___x_2217_ = l_Nat_reprFast(v_n_2203_);
                        v___x_2218_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_2218_, 0, v___x_2217_);
                        v___x_2219_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2220_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2221_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2221_, 0, v___x_2220_);
                        lean_ctor_set(v___x_2221_, 1, v___x_2218_);
                        v___x_2222_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2223_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2223_, 0, v___x_2221_);
                        lean_ctor_set(v___x_2223_, 1, v___x_2222_);
                        v___x_2224_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v___x_2224_, 0, v___x_2219_);
                        lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                        v___x_2225_ = 0;
                        v___x_2226_ = lean_alloc_ctor(6, 1, (1) as u32);
                        lean_ctor_set(v___x_2226_, 0, v___x_2224_);
                        lean_ctor_set_uint8(
                            v___x_2226_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2225_,
                        );
                        v___y_2206_ = v___x_2226_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_n_2203_);
                        v___x_2227_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2206_ = v___x_2227_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_x_2228_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2228_);
                    v_n_2229_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_n_2229_);
                    lean_dec_ref_known(v_x_2092_, 3);
                    v___x_2230_ = l_Lean_IR_formatFnBodyHead___closed__25;
                    v___x_2241_ = lean_unsigned_to_nat(1);
                    v___x_2242_ = lean_nat_dec_eq(v_n_2229_, v___x_2241_);
                    if v___x_2242_ == 0 {
                        v___x_2243_ = l_Nat_reprFast(v_n_2229_);
                        v___x_2244_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_2244_, 0, v___x_2243_);
                        v___x_2245_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2246_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2247_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2247_, 0, v___x_2246_);
                        lean_ctor_set(v___x_2247_, 1, v___x_2244_);
                        v___x_2248_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2249_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2249_, 0, v___x_2247_);
                        lean_ctor_set(v___x_2249_, 1, v___x_2248_);
                        v___x_2250_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v___x_2250_, 0, v___x_2245_);
                        lean_ctor_set(v___x_2250_, 1, v___x_2249_);
                        v___x_2251_ = 0;
                        v___x_2252_ = lean_alloc_ctor(6, 1, (1) as u32);
                        lean_ctor_set(v___x_2252_, 0, v___x_2250_);
                        lean_ctor_set_uint8(
                            v___x_2252_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2251_,
                        );
                        v___y_2232_ = v___x_2252_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_n_2229_);
                        v___x_2253_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2232_ = v___x_2253_;
                        state = 2;
                        continue;
                    }
                }
                8 => {
                    v_x_2254_ = lean_ctor_get(v_x_2092_, 0);
                    v_isSharedCheck_2266_ = (!lean_is_exclusive(v_x_2092_)) as u8;
                    if v_isSharedCheck_2266_ == 0 {
                        v_unused_2267_ = lean_ctor_get(v_x_2092_, 1);
                        lean_dec(v_unused_2267_);
                        v___x_2256_ = v_x_2092_;
                        v_isShared_2257_ = v_isSharedCheck_2266_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_x_2254_);
                        lean_dec(v_x_2092_);
                        v___x_2256_ = lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2266_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_x_2268_ = lean_ctor_get(v_x_2092_, 1);
                    lean_inc(v_x_2268_);
                    lean_dec_ref_known(v_x_2092_, 4);
                    v___x_2269_ = l_Lean_IR_formatFnBodyHead___closed__29;
                    v___x_2270_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2271_ = l_Nat_reprFast(v_x_2268_);
                    v___x_2272_ = lean_string_append(v___x_2270_, v___x_2271_);
                    lean_dec_ref(v___x_2271_);
                    v___x_2273_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2273_, 0, v___x_2272_);
                    v___x_2274_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2274_, 0, v___x_2269_);
                    lean_ctor_set(v___x_2274_, 1, v___x_2273_);
                    v___x_2275_ = l_Lean_IR_formatFnBodyHead___closed__31;
                    v___x_2276_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2276_, 0, v___x_2274_);
                    lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    return v___x_2276_;
                }
                10 => {
                    v_x_2277_ = lean_ctor_get(v_x_2092_, 0);
                    lean_inc(v_x_2277_);
                    lean_dec_ref_known(v_x_2092_, 1);
                    v___x_2278_ = l_Lean_IR_formatFnBodyHead___closed__33;
                    v___x_2279_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_2277_);
                    v___x_2280_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2280_, 0, v___x_2278_);
                    lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                    return v___x_2280_;
                }
                11 => {
                    v_j_2281_ = lean_ctor_get(v_x_2092_, 0);
                    v_ys_2282_ = lean_ctor_get(v_x_2092_, 1);
                    v_isSharedCheck_2296_ = (!lean_is_exclusive(v_x_2092_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2284_ = v_x_2092_;
                        v_isShared_2285_ = v_isSharedCheck_2296_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_ys_2282_);
                        lean_inc(v_j_2281_);
                        lean_dec(v_x_2092_);
                        v___x_2284_ = lean_box(0);
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
                v___x_2207_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2207_, 0, v___x_2204_);
                lean_ctor_set(v___x_2207_, 1, v___y_2206_);
                v___x_2208_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2209_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2209_, 0, v___x_2207_);
                lean_ctor_set(v___x_2209_, 1, v___x_2208_);
                v___x_2210_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2211_ = l_Nat_reprFast(v_x_2202_);
                v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
                lean_dec_ref(v___x_2211_);
                v___x_2213_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2213_, 0, v___x_2212_);
                v___x_2214_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2214_, 0, v___x_2209_);
                lean_ctor_set(v___x_2214_, 1, v___x_2213_);
                return v___x_2214_;
            }
            2 => {
                v___x_2233_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2233_, 0, v___x_2230_);
                lean_ctor_set(v___x_2233_, 1, v___y_2232_);
                v___x_2234_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2235_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2235_, 0, v___x_2233_);
                lean_ctor_set(v___x_2235_, 1, v___x_2234_);
                v___x_2236_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2237_ = l_Nat_reprFast(v_x_2228_);
                v___x_2238_ = lean_string_append(v___x_2236_, v___x_2237_);
                lean_dec_ref(v___x_2237_);
                v___x_2239_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                v___x_2240_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2240_, 0, v___x_2235_);
                lean_ctor_set(v___x_2240_, 1, v___x_2239_);
                return v___x_2240_;
            }
            3 => {
                v___x_2258_ = l_Lean_IR_formatFnBodyHead___closed__27;
                v___x_2259_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2260_ = l_Nat_reprFast(v_x_2254_);
                v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
                lean_dec_ref(v___x_2260_);
                v___x_2262_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2262_, 0, v___x_2261_);
                if v_isShared_2257_ == 0 {
                    lean_ctor_set_tag(v___x_2256_, 5);
                    lean_ctor_set(v___x_2256_, 1, v___x_2262_);
                    lean_ctor_set(v___x_2256_, 0, v___x_2258_);
                    v___x_2264_ = v___x_2256_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2258_);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
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
                lean_dec_ref(v___x_2288_);
                v___x_2290_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2290_, 0, v___x_2289_);
                if v_isShared_2285_ == 0 {
                    lean_ctor_set_tag(v___x_2284_, 5);
                    lean_ctor_set(v___x_2284_, 1, v___x_2290_);
                    lean_ctor_set(v___x_2284_, 0, v___x_2286_);
                    v___x_2292_ = v___x_2284_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2290_);
                    v___x_2292_ = v_reuseFailAlloc_2295_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2293_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_2282_);
                lean_dec_ref(v_ys_2282_);
                v___x_2294_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2294_, 0, v___x_2292_);
                lean_ctor_set(v___x_2294_, 1, v___x_2293_);
                return v___x_2294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_ir_format_fn_body_head(mut v_fn_2298_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_IR_formatFnBodyHead(v_fn_2298_);
    v___x_2300_ = l_Std_Format_defWidth;
    v___x_2301_ = lean_unsigned_to_nat(0);
    v___x_2302_ = l_Std_Format_pretty(v___x_2299_, v___x_2300_, v___x_2301_, v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
    mut v_indent_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u8 = 0;
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2556_: u8 = 0;
    let mut v_x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xType_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_2313_) {
                0 => {
                    v_x_2314_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2314_);
                    v_ty_2315_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_ty_2315_);
                    v_e_2316_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc_ref(v_e_2316_);
                    v_b_2317_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc(v_b_2317_);
                    lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2318_ = l_Lean_IR_formatFnBodyHead___closed__1;
                    v___x_2319_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2320_ = l_Nat_reprFast(v_x_2314_);
                    v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
                    lean_dec_ref(v___x_2320_);
                    v___x_2322_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2322_, 0, v___x_2321_);
                    v___x_2323_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2323_, 0, v___x_2318_);
                    lean_ctor_set(v___x_2323_, 1, v___x_2322_);
                    v___x_2324_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2325_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2325_, 0, v___x_2323_);
                    lean_ctor_set(v___x_2325_, 1, v___x_2324_);
                    v___x_2326_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2315_);
                    v___x_2327_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2327_, 0, v___x_2325_);
                    lean_ctor_set(v___x_2327_, 1, v___x_2326_);
                    v___x_2328_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2329_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2329_, 0, v___x_2327_);
                    lean_ctor_set(v___x_2329_, 1, v___x_2328_);
                    v___x_2330_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(v_e_2316_);
                    v___x_2331_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2331_, 0, v___x_2329_);
                    lean_ctor_set(v___x_2331_, 1, v___x_2330_);
                    v___x_2332_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2333_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2333_, 0, v___x_2331_);
                    lean_ctor_set(v___x_2333_, 1, v___x_2332_);
                    v___x_2334_ = lean_box(1);
                    v___x_2335_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2335_, 0, v___x_2333_);
                    lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                    v___x_2336_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2317_,
                    );
                    v___x_2337_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                    lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                    return v___x_2337_;
                }
                1 => {
                    v_j_2338_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_j_2338_);
                    v_xs_2339_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc_ref(v_xs_2339_);
                    v_v_2340_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_v_2340_);
                    v_b_2341_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc(v_b_2341_);
                    lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2342_ = l_Lean_IR_formatFnBodyHead___closed__4;
                    v___x_2343_ = l_Nat_reprFast(v_j_2338_);
                    v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
                    lean_dec_ref(v___x_2343_);
                    v___x_2345_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2345_, 0, v___x_2344_);
                    v___x_2346_ =
                        l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2339_);
                    lean_dec_ref(v_xs_2339_);
                    v___x_2347_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2347_, 0, v___x_2345_);
                    lean_ctor_set(v___x_2347_, 1, v___x_2346_);
                    v___x_2348_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3;
                    v___x_2349_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2349_, 0, v___x_2347_);
                    lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                    lean_inc_n(v_indent_2312_, 2);
                    v___x_2350_ = lean_nat_to_int(v_indent_2312_);
                    v___x_2351_ = lean_box(1);
                    v___x_2352_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_v_2340_,
                    );
                    v___x_2353_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2353_, 0, v___x_2351_);
                    lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v___x_2354_, 0, v___x_2350_);
                    lean_ctor_set(v___x_2354_, 1, v___x_2353_);
                    v___x_2355_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2355_, 0, v___x_2349_);
                    lean_ctor_set(v___x_2355_, 1, v___x_2354_);
                    v___x_2356_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2357_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                    lean_ctor_set(v___x_2357_, 1, v___x_2356_);
                    v___x_2358_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2358_, 0, v___x_2357_);
                    lean_ctor_set(v___x_2358_, 1, v___x_2351_);
                    v___x_2359_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2341_,
                    );
                    v___x_2360_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2360_, 0, v___x_2358_);
                    lean_ctor_set(v___x_2360_, 1, v___x_2359_);
                    return v___x_2360_;
                }
                2 => {
                    v_x_2361_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2361_);
                    v_i_2362_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_i_2362_);
                    v_y_2363_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_y_2363_);
                    v_b_2364_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc(v_b_2364_);
                    lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2365_ = l_Lean_IR_formatFnBodyHead___closed__8;
                    v___x_2366_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2367_ = l_Nat_reprFast(v_x_2361_);
                    v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
                    lean_dec_ref(v___x_2367_);
                    v___x_2369_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2369_, 0, v___x_2368_);
                    v___x_2370_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2370_, 0, v___x_2365_);
                    lean_ctor_set(v___x_2370_, 1, v___x_2369_);
                    v___x_2371_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2372_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2372_, 0, v___x_2370_);
                    lean_ctor_set(v___x_2372_, 1, v___x_2371_);
                    v___x_2373_ = l_Nat_reprFast(v_i_2362_);
                    v___x_2374_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2374_, 0, v___x_2373_);
                    v___x_2375_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2375_, 0, v___x_2372_);
                    lean_ctor_set(v___x_2375_, 1, v___x_2374_);
                    v___x_2376_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2377_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2377_, 0, v___x_2375_);
                    lean_ctor_set(v___x_2377_, 1, v___x_2376_);
                    v___x_2378_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_y_2363_);
                    v___x_2379_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2379_, 0, v___x_2377_);
                    lean_ctor_set(v___x_2379_, 1, v___x_2378_);
                    v___x_2380_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2381_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2381_, 0, v___x_2379_);
                    lean_ctor_set(v___x_2381_, 1, v___x_2380_);
                    v___x_2382_ = lean_box(1);
                    v___x_2383_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2383_, 0, v___x_2381_);
                    lean_ctor_set(v___x_2383_, 1, v___x_2382_);
                    v___x_2384_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2364_,
                    );
                    v___x_2385_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2385_, 0, v___x_2383_);
                    lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                    return v___x_2385_;
                }
                3 => {
                    v_x_2386_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2386_);
                    v_cidx_2387_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_cidx_2387_);
                    v_b_2388_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_b_2388_);
                    lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2389_ = l_Lean_IR_formatFnBodyHead___closed__12;
                    v___x_2390_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2391_ = l_Nat_reprFast(v_x_2386_);
                    v___x_2392_ = lean_string_append(v___x_2390_, v___x_2391_);
                    lean_dec_ref(v___x_2391_);
                    v___x_2393_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    v___x_2394_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2394_, 0, v___x_2389_);
                    lean_ctor_set(v___x_2394_, 1, v___x_2393_);
                    v___x_2395_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2396_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2396_, 0, v___x_2394_);
                    lean_ctor_set(v___x_2396_, 1, v___x_2395_);
                    v___x_2397_ = l_Nat_reprFast(v_cidx_2387_);
                    v___x_2398_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2398_, 0, v___x_2397_);
                    v___x_2399_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2399_, 0, v___x_2396_);
                    lean_ctor_set(v___x_2399_, 1, v___x_2398_);
                    v___x_2400_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2401_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2401_, 0, v___x_2399_);
                    lean_ctor_set(v___x_2401_, 1, v___x_2400_);
                    v___x_2402_ = lean_box(1);
                    v___x_2403_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2403_, 0, v___x_2401_);
                    lean_ctor_set(v___x_2403_, 1, v___x_2402_);
                    v___x_2404_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2388_,
                    );
                    v___x_2405_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                    lean_ctor_set(v___x_2405_, 1, v___x_2404_);
                    return v___x_2405_;
                }
                4 => {
                    v_x_2406_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2406_);
                    v_i_2407_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_i_2407_);
                    v_y_2408_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_y_2408_);
                    v_b_2409_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc(v_b_2409_);
                    lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2410_ = l_Lean_IR_formatFnBodyHead___closed__14;
                    v___x_2411_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2412_ = l_Nat_reprFast(v_x_2406_);
                    v___x_2413_ = lean_string_append(v___x_2411_, v___x_2412_);
                    lean_dec_ref(v___x_2412_);
                    v___x_2414_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                    v___x_2415_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2415_, 0, v___x_2410_);
                    lean_ctor_set(v___x_2415_, 1, v___x_2414_);
                    v___x_2416_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2417_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2417_, 0, v___x_2415_);
                    lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                    v___x_2418_ = l_Nat_reprFast(v_i_2407_);
                    v___x_2419_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2419_, 0, v___x_2418_);
                    v___x_2420_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2420_, 0, v___x_2417_);
                    lean_ctor_set(v___x_2420_, 1, v___x_2419_);
                    v___x_2421_ = l_Lean_IR_formatFnBodyHead___closed__10;
                    v___x_2422_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2422_, 0, v___x_2420_);
                    lean_ctor_set(v___x_2422_, 1, v___x_2421_);
                    v___x_2423_ = l_Nat_reprFast(v_y_2408_);
                    v___x_2424_ = lean_string_append(v___x_2411_, v___x_2423_);
                    lean_dec_ref(v___x_2423_);
                    v___x_2425_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                    v___x_2426_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2426_, 0, v___x_2422_);
                    lean_ctor_set(v___x_2426_, 1, v___x_2425_);
                    v___x_2427_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2428_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2428_, 0, v___x_2426_);
                    lean_ctor_set(v___x_2428_, 1, v___x_2427_);
                    v___x_2429_ = lean_box(1);
                    v___x_2430_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2430_, 0, v___x_2428_);
                    lean_ctor_set(v___x_2430_, 1, v___x_2429_);
                    v___x_2431_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2409_,
                    );
                    v___x_2432_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2432_, 0, v___x_2430_);
                    lean_ctor_set(v___x_2432_, 1, v___x_2431_);
                    return v___x_2432_;
                }
                5 => {
                    v_x_2433_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2433_);
                    v_i_2434_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_i_2434_);
                    v_offset_2435_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_offset_2435_);
                    v_y_2436_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc(v_y_2436_);
                    v_ty_2437_ = lean_ctor_get(v_a_2313_, 4);
                    lean_inc(v_ty_2437_);
                    v_b_2438_ = lean_ctor_get(v_a_2313_, 5);
                    lean_inc(v_b_2438_);
                    lean_dec_ref_known(v_a_2313_, 6);
                    v___x_2439_ = l_Lean_IR_formatFnBodyHead___closed__16;
                    v___x_2440_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2441_ = l_Nat_reprFast(v_x_2433_);
                    v___x_2442_ = lean_string_append(v___x_2440_, v___x_2441_);
                    lean_dec_ref(v___x_2441_);
                    v___x_2443_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                    v___x_2444_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2444_, 0, v___x_2439_);
                    lean_ctor_set(v___x_2444_, 1, v___x_2443_);
                    v___x_2445_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                    v___x_2446_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2446_, 0, v___x_2444_);
                    lean_ctor_set(v___x_2446_, 1, v___x_2445_);
                    v___x_2447_ = l_Nat_reprFast(v_i_2434_);
                    v___x_2448_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2448_, 0, v___x_2447_);
                    v___x_2449_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2449_, 0, v___x_2446_);
                    lean_ctor_set(v___x_2449_, 1, v___x_2448_);
                    v___x_2450_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___closed__17;
                    v___x_2451_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2451_, 0, v___x_2449_);
                    lean_ctor_set(v___x_2451_, 1, v___x_2450_);
                    v___x_2452_ = l_Nat_reprFast(v_offset_2435_);
                    v___x_2453_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2453_, 0, v___x_2452_);
                    v___x_2454_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2454_, 0, v___x_2451_);
                    lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                    v___x_2455_ = l_Lean_IR_formatFnBodyHead___closed__18;
                    v___x_2456_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                    lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    v___x_2457_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_ty_2437_);
                    v___x_2458_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2458_, 0, v___x_2456_);
                    lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                    v___x_2459_ = l_Lean_IR_formatFnBodyHead___closed__3;
                    v___x_2460_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2460_, 0, v___x_2458_);
                    lean_ctor_set(v___x_2460_, 1, v___x_2459_);
                    v___x_2461_ = l_Nat_reprFast(v_y_2436_);
                    v___x_2462_ = lean_string_append(v___x_2440_, v___x_2461_);
                    lean_dec_ref(v___x_2461_);
                    v___x_2463_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2463_, 0, v___x_2462_);
                    v___x_2464_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2464_, 0, v___x_2460_);
                    lean_ctor_set(v___x_2464_, 1, v___x_2463_);
                    v___x_2465_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                    v___x_2466_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2466_, 0, v___x_2464_);
                    lean_ctor_set(v___x_2466_, 1, v___x_2465_);
                    v___x_2467_ = lean_box(1);
                    v___x_2468_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2468_, 0, v___x_2466_);
                    lean_ctor_set(v___x_2468_, 1, v___x_2467_);
                    v___x_2469_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                        v_indent_2312_,
                        v_b_2438_,
                    );
                    v___x_2470_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2470_, 0, v___x_2468_);
                    lean_ctor_set(v___x_2470_, 1, v___x_2469_);
                    return v___x_2470_;
                }
                6 => {
                    v_x_2471_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2471_);
                    v_n_2472_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_n_2472_);
                    v_b_2473_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_b_2473_);
                    lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2474_ = l_Lean_IR_formatFnBodyHead___closed__20;
                    v___x_2491_ = lean_unsigned_to_nat(1);
                    v___x_2492_ = lean_nat_dec_eq(v_n_2472_, v___x_2491_);
                    if v___x_2492_ == 0 {
                        v___x_2493_ = l_Nat_reprFast(v_n_2472_);
                        v___x_2494_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_2494_, 0, v___x_2493_);
                        v___x_2495_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2496_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2497_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2497_, 0, v___x_2496_);
                        lean_ctor_set(v___x_2497_, 1, v___x_2494_);
                        v___x_2498_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2499_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2499_, 0, v___x_2497_);
                        lean_ctor_set(v___x_2499_, 1, v___x_2498_);
                        v___x_2500_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v___x_2500_, 0, v___x_2495_);
                        lean_ctor_set(v___x_2500_, 1, v___x_2499_);
                        v___x_2501_ = 0;
                        v___x_2502_ = lean_alloc_ctor(6, 1, (1) as u32);
                        lean_ctor_set(v___x_2502_, 0, v___x_2500_);
                        lean_ctor_set_uint8(
                            v___x_2502_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2501_,
                        );
                        v___y_2476_ = v___x_2502_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_n_2472_);
                        v___x_2503_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2476_ = v___x_2503_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_x_2504_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2504_);
                    v_n_2505_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_n_2505_);
                    v_b_2506_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_b_2506_);
                    lean_dec_ref_known(v_a_2313_, 3);
                    v___x_2507_ = l_Lean_IR_formatFnBodyHead___closed__25;
                    v___x_2524_ = lean_unsigned_to_nat(1);
                    v___x_2525_ = lean_nat_dec_eq(v_n_2505_, v___x_2524_);
                    if v___x_2525_ == 0 {
                        v___x_2526_ = l_Nat_reprFast(v_n_2505_);
                        v___x_2527_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_2527_, 0, v___x_2526_);
                        v___x_2528_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22),
                            core::ptr::addr_of_mut!(l_Lean_IR_formatFnBodyHead___closed__22_once),
                            _init_l_Lean_IR_formatFnBodyHead___closed__22,
                        );
                        v___x_2529_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__1;
                        v___x_2530_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2530_, 0, v___x_2529_);
                        lean_ctor_set(v___x_2530_, 1, v___x_2527_);
                        v___x_2531_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___closed__3;
                        v___x_2532_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2532_, 0, v___x_2530_);
                        lean_ctor_set(v___x_2532_, 1, v___x_2531_);
                        v___x_2533_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v___x_2533_, 0, v___x_2528_);
                        lean_ctor_set(v___x_2533_, 1, v___x_2532_);
                        v___x_2534_ = 0;
                        v___x_2535_ = lean_alloc_ctor(6, 1, (1) as u32);
                        lean_ctor_set(v___x_2535_, 0, v___x_2533_);
                        lean_ctor_set_uint8(
                            v___x_2535_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2534_,
                        );
                        v___y_2509_ = v___x_2535_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_n_2505_);
                        v___x_2536_ = l_Lean_IR_formatFnBodyHead___closed__23;
                        v___y_2509_ = v___x_2536_;
                        state = 2;
                        continue;
                    }
                }
                8 => {
                    v_x_2537_ = lean_ctor_get(v_a_2313_, 0);
                    v_b_2538_ = lean_ctor_get(v_a_2313_, 1);
                    v_isSharedCheck_2556_ = (!lean_is_exclusive(v_a_2313_)) as u8;
                    if v_isSharedCheck_2556_ == 0 {
                        v___x_2540_ = v_a_2313_;
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_b_2538_);
                        lean_inc(v_x_2537_);
                        lean_dec(v_a_2313_);
                        v___x_2540_ = lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2556_;
                        state = 3;
                        continue;
                    }
                }
                9 => {
                    v_x_2557_ = lean_ctor_get(v_a_2313_, 1);
                    lean_inc(v_x_2557_);
                    v_xType_2558_ = lean_ctor_get(v_a_2313_, 2);
                    lean_inc(v_xType_2558_);
                    v_cs_2559_ = lean_ctor_get(v_a_2313_, 3);
                    lean_inc_ref(v_cs_2559_);
                    lean_dec_ref_known(v_a_2313_, 4);
                    v___x_2560_ = l_Lean_IR_formatFnBodyHead___closed__29;
                    v___x_2561_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                    v___x_2562_ = l_Nat_reprFast(v_x_2557_);
                    v___x_2563_ = lean_string_append(v___x_2561_, v___x_2562_);
                    lean_dec_ref(v___x_2562_);
                    v___x_2564_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2564_, 0, v___x_2563_);
                    v___x_2565_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2565_, 0, v___x_2560_);
                    lean_ctor_set(v___x_2565_, 1, v___x_2564_);
                    v___x_2566_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
                    v___x_2567_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2567_, 0, v___x_2565_);
                    lean_ctor_set(v___x_2567_, 1, v___x_2566_);
                    v___x_2568_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_xType_2558_);
                    v___x_2569_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2569_, 0, v___x_2567_);
                    lean_ctor_set(v___x_2569_, 1, v___x_2568_);
                    v___x_2570_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__5;
                    v___x_2571_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2571_, 0, v___x_2569_);
                    lean_ctor_set(v___x_2571_, 1, v___x_2570_);
                    v___x_2572_ = lean_box(0);
                    v___x_2573_ = lean_unsigned_to_nat(0);
                    v___x_2574_ = lean_array_get_size(v_cs_2559_);
                    v___x_2575_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
                    if v___x_2575_ == 0 {
                        lean_dec_ref(v_cs_2559_);
                        lean_dec(v_indent_2312_);
                        v___x_2576_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_2576_, 0, v___x_2571_);
                        lean_ctor_set(v___x_2576_, 1, v___x_2572_);
                        return v___x_2576_;
                    } else {
                        v___x_2577_ = lean_nat_dec_le(v___x_2574_, v___x_2574_);
                        if v___x_2577_ == 0 {
                            if v___x_2575_ == 0 {
                                lean_dec_ref(v_cs_2559_);
                                lean_dec(v_indent_2312_);
                                v___x_2578_ = lean_alloc_ctor(5, 2, (0) as u32);
                                lean_ctor_set(v___x_2578_, 0, v___x_2571_);
                                lean_ctor_set(v___x_2578_, 1, v___x_2572_);
                                return v___x_2578_;
                            } else {
                                v___x_2579_ = 0usize;
                                v___x_2580_ = lean_usize_of_nat(v___x_2574_);
                                v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2312_, v_cs_2559_, v___x_2579_, v___x_2580_, v___x_2572_);
                                lean_dec_ref(v_cs_2559_);
                                v___x_2582_ = lean_alloc_ctor(5, 2, (0) as u32);
                                lean_ctor_set(v___x_2582_, 0, v___x_2571_);
                                lean_ctor_set(v___x_2582_, 1, v___x_2581_);
                                return v___x_2582_;
                            }
                        } else {
                            v___x_2583_ = 0usize;
                            v___x_2584_ = lean_usize_of_nat(v___x_2574_);
                            v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2312_, v_cs_2559_, v___x_2583_, v___x_2584_, v___x_2572_);
                            lean_dec_ref(v_cs_2559_);
                            v___x_2586_ = lean_alloc_ctor(5, 2, (0) as u32);
                            lean_ctor_set(v___x_2586_, 0, v___x_2571_);
                            lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                            return v___x_2586_;
                        }
                    }
                }
                10 => {
                    lean_dec(v_indent_2312_);
                    v_x_2587_ = lean_ctor_get(v_a_2313_, 0);
                    lean_inc(v_x_2587_);
                    lean_dec_ref_known(v_a_2313_, 1);
                    v___x_2588_ = l_Lean_IR_formatFnBodyHead___closed__33;
                    v___x_2589_ =
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(v_x_2587_);
                    v___x_2590_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2590_, 0, v___x_2588_);
                    lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                    return v___x_2590_;
                }
                11 => {
                    lean_dec(v_indent_2312_);
                    v_j_2591_ = lean_ctor_get(v_a_2313_, 0);
                    v_ys_2592_ = lean_ctor_get(v_a_2313_, 1);
                    v_isSharedCheck_2606_ = (!lean_is_exclusive(v_a_2313_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v___x_2594_ = v_a_2313_;
                        v_isShared_2595_ = v_isSharedCheck_2606_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_ys_2592_);
                        lean_inc(v_j_2591_);
                        lean_dec(v_a_2313_);
                        v___x_2594_ = lean_box(0);
                        v_isShared_2595_ = v_isSharedCheck_2606_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_indent_2312_);
                    v___x_2607_ = l_Lean_IR_formatFnBodyHead___closed__37;
                    return v___x_2607_;
                }
            },
            1 => {
                v___x_2477_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2477_, 0, v___x_2474_);
                lean_ctor_set(v___x_2477_, 1, v___y_2476_);
                v___x_2478_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2479_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2479_, 0, v___x_2477_);
                lean_ctor_set(v___x_2479_, 1, v___x_2478_);
                v___x_2480_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2481_ = l_Nat_reprFast(v_x_2471_);
                v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
                lean_dec_ref(v___x_2481_);
                v___x_2483_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                v___x_2484_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2484_, 0, v___x_2479_);
                lean_ctor_set(v___x_2484_, 1, v___x_2483_);
                v___x_2485_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2486_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2486_, 0, v___x_2484_);
                lean_ctor_set(v___x_2486_, 1, v___x_2485_);
                v___x_2487_ = lean_box(1);
                v___x_2488_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2488_, 0, v___x_2486_);
                lean_ctor_set(v___x_2488_, 1, v___x_2487_);
                v___x_2489_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2473_,
                );
                v___x_2490_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2490_, 0, v___x_2488_);
                lean_ctor_set(v___x_2490_, 1, v___x_2489_);
                return v___x_2490_;
            }
            2 => {
                v___x_2510_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2510_, 0, v___x_2507_);
                lean_ctor_set(v___x_2510_, 1, v___y_2509_);
                v___x_2511_ = l_Lean_IR_formatArray___redArg___lam__0___closed__1;
                v___x_2512_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2512_, 0, v___x_2510_);
                lean_ctor_set(v___x_2512_, 1, v___x_2511_);
                v___x_2513_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2514_ = l_Nat_reprFast(v_x_2504_);
                v___x_2515_ = lean_string_append(v___x_2513_, v___x_2514_);
                lean_dec_ref(v___x_2514_);
                v___x_2516_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                v___x_2517_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2517_, 0, v___x_2512_);
                lean_ctor_set(v___x_2517_, 1, v___x_2516_);
                v___x_2518_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2519_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2519_, 0, v___x_2517_);
                lean_ctor_set(v___x_2519_, 1, v___x_2518_);
                v___x_2520_ = lean_box(1);
                v___x_2521_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2521_, 0, v___x_2519_);
                lean_ctor_set(v___x_2521_, 1, v___x_2520_);
                v___x_2522_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2506_,
                );
                v___x_2523_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2523_, 0, v___x_2521_);
                lean_ctor_set(v___x_2523_, 1, v___x_2522_);
                return v___x_2523_;
            }
            3 => {
                v___x_2542_ = l_Lean_IR_formatFnBodyHead___closed__27;
                v___x_2543_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg___closed__0;
                v___x_2544_ = l_Nat_reprFast(v_x_2537_);
                v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
                lean_dec_ref(v___x_2544_);
                v___x_2546_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                if v_isShared_2541_ == 0 {
                    lean_ctor_set_tag(v___x_2540_, 5);
                    lean_ctor_set(v___x_2540_, 1, v___x_2546_);
                    lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2548_ = v___x_2540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2542_);
                    lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___x_2546_);
                    v___x_2548_ = v_reuseFailAlloc_2555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2549_ =
                    l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__1;
                v___x_2550_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2550_, 0, v___x_2548_);
                lean_ctor_set(v___x_2550_, 1, v___x_2549_);
                v___x_2551_ = lean_box(1);
                v___x_2552_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2552_, 0, v___x_2550_);
                lean_ctor_set(v___x_2552_, 1, v___x_2551_);
                v___x_2553_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
                    v_indent_2312_,
                    v_b_2538_,
                );
                v___x_2554_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2554_, 0, v___x_2552_);
                lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                return v___x_2554_;
            }
            5 => {
                v___x_2596_ = l_Lean_IR_formatFnBodyHead___closed__35;
                v___x_2597_ = l_Lean_IR_formatFnBodyHead___closed__4;
                v___x_2598_ = l_Nat_reprFast(v_j_2591_);
                v___x_2599_ = lean_string_append(v___x_2597_, v___x_2598_);
                lean_dec_ref(v___x_2598_);
                v___x_2600_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2600_, 0, v___x_2599_);
                if v_isShared_2595_ == 0 {
                    lean_ctor_set_tag(v___x_2594_, 5);
                    lean_ctor_set(v___x_2594_, 1, v___x_2600_);
                    lean_ctor_set(v___x_2594_, 0, v___x_2596_);
                    v___x_2602_ = v___x_2594_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2596_);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2600_);
                    v___x_2602_ = v_reuseFailAlloc_2605_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2603_ = l_Lean_IR_formatArray___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(v_ys_2592_);
                lean_dec_ref(v_ys_2592_);
                v___x_2604_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2604_, 0, v___x_2602_);
                lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(
    mut v_indent_2608_: *mut LeanObject,
    mut v_as_2609_: *mut LeanObject,
    mut v_i_2610_: usize,
    mut v_stop_2611_: usize,
    mut v_b_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2613_ = lean_usize_dec_eq(v_i_2610_, v_stop_2611_);
                if v___x_2613_ == 0 {
                    v___x_2614_ = lean_array_uget_borrowed(v_as_2609_, v_i_2610_);
                    v___x_2615_ = lean_box(1);
                    v___x_2616_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2616_, 0, v_b_2612_);
                    lean_ctor_set(v___x_2616_, 1, v___x_2615_);
                    lean_inc_n(v_indent_2608_, 2);
                    v___x_2617_ = lean_alloc_closure(
                        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___x_2617_, 0, v_indent_2608_);
                    lean_inc(v___x_2614_);
                    v___x_2618_ = l_Lean_IR_formatAlt(v___x_2617_, v_indent_2608_, v___x_2614_);
                    v___x_2619_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2619_, 0, v___x_2616_);
                    lean_ctor_set(v___x_2619_, 1, v___x_2618_);
                    v___x_2620_ = 1usize;
                    v___x_2621_ = lean_usize_add(v_i_2610_, v___x_2620_);
                    v_i_2610_ = v___x_2621_;
                    v_b_2612_ = v___x_2619_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_indent_2608_);
                    return v_b_2612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0___boxed(
    mut v_indent_2623_: *mut LeanObject,
    mut v_as_2624_: *mut LeanObject,
    mut v_i_2625_: *mut LeanObject,
    mut v_stop_2626_: *mut LeanObject,
    mut v_b_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2628_: usize = 0;
    let mut v_stop_boxed_2629_: usize = 0;
    let mut v_res_2630_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2628_ = lean_unbox_usize(v_i_2625_);
    lean_dec(v_i_2625_);
    v_stop_boxed_2629_ = lean_unbox_usize(v_stop_2626_);
    lean_dec(v_stop_2626_);
    v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop_spec__0(v_indent_2623_, v_as_2624_, v_i_boxed_2628_, v_stop_boxed_2629_, v_b_2627_);
    lean_dec_ref(v_as_2624_);
    return v_res_2630_;
}
pub unsafe fn l_Lean_IR_formatFnBody(
    mut v_fnBody_2631_: *mut LeanObject,
    mut v_indent_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v___x_2633_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
        v_indent_2632_,
        v_fnBody_2631_,
    );
    return v___x_2633_;
}
pub unsafe fn l_Lean_IR_instToFormatFnBody___lam__0(
    mut v_fnBody_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2635_ = lean_unsigned_to_nat(2);
    v___x_2636_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
        v___x_2635_,
        v_fnBody_2634_,
    );
    return v___x_2636_;
}
pub unsafe fn l_Lean_IR_instToStringFnBody___lam__0(
    mut v_b_2639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    v___x_2640_ = lean_unsigned_to_nat(2);
    v___x_2641_ =
        l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(v___x_2640_, v_b_2639_);
    v___x_2642_ = l_Std_Format_defWidth;
    v___x_2643_ = lean_unsigned_to_nat(0);
    v___x_2644_ = l_Std_Format_pretty(v___x_2641_, v___x_2642_, v___x_2643_, v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Lean_IR_formatDecl(
    mut v_decl_2653_: *mut LeanObject,
    mut v_indent_2654_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_decl_2653_) == 0 {
        let mut v_f_2655_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_2656_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2657_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2660_: u8 = 0;
        let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
        v_f_2655_ = lean_ctor_get(v_decl_2653_, 0);
        lean_inc(v_f_2655_);
        v_xs_2656_ = lean_ctor_get(v_decl_2653_, 1);
        lean_inc_ref(v_xs_2656_);
        v_type_2657_ = lean_ctor_get(v_decl_2653_, 2);
        lean_inc(v_type_2657_);
        v_body_2658_ = lean_ctor_get(v_decl_2653_, 3);
        lean_inc(v_body_2658_);
        lean_dec_ref_known(v_decl_2653_, 5);
        v___x_2659_ = l_Lean_IR_formatDecl___closed__1;
        v___x_2660_ = 1;
        v___x_2661_ = l_Lean_Name_toString(v_f_2655_, v___x_2660_);
        v___x_2662_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2662_, 0, v___x_2661_);
        v___x_2663_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2663_, 0, v___x_2659_);
        lean_ctor_set(v___x_2663_, 1, v___x_2662_);
        v___x_2664_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2656_);
        lean_dec_ref(v_xs_2656_);
        v___x_2665_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2665_, 0, v___x_2663_);
        lean_ctor_set(v___x_2665_, 1, v___x_2664_);
        v___x_2666_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
        v___x_2667_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2667_, 0, v___x_2665_);
        lean_ctor_set(v___x_2667_, 1, v___x_2666_);
        v___x_2668_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_2657_);
        v___x_2669_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2669_, 0, v___x_2667_);
        lean_ctor_set(v___x_2669_, 1, v___x_2668_);
        v___x_2670_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop___closed__3;
        v___x_2671_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2671_, 0, v___x_2669_);
        lean_ctor_set(v___x_2671_, 1, v___x_2670_);
        lean_inc(v_indent_2654_);
        v___x_2672_ = lean_nat_to_int(v_indent_2654_);
        v___x_2673_ = lean_box(1);
        v___x_2674_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatFnBody_loop(
            v_indent_2654_,
            v_body_2658_,
        );
        v___x_2675_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2675_, 0, v___x_2673_);
        lean_ctor_set(v___x_2675_, 1, v___x_2674_);
        v___x_2676_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2676_, 0, v___x_2672_);
        lean_ctor_set(v___x_2676_, 1, v___x_2675_);
        v___x_2677_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2677_, 0, v___x_2671_);
        lean_ctor_set(v___x_2677_, 1, v___x_2676_);
        return v___x_2677_;
    } else {
        let mut v_f_2678_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_2679_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_indent_2654_);
        v_f_2678_ = lean_ctor_get(v_decl_2653_, 0);
        lean_inc(v_f_2678_);
        v_xs_2679_ = lean_ctor_get(v_decl_2653_, 1);
        lean_inc_ref(v_xs_2679_);
        v_type_2680_ = lean_ctor_get(v_decl_2653_, 2);
        lean_inc(v_type_2680_);
        lean_dec_ref_known(v_decl_2653_, 4);
        v___x_2681_ = l_Lean_IR_formatDecl___closed__3;
        v___x_2682_ = 1;
        v___x_2683_ = l_Lean_Name_toString(v_f_2678_, v___x_2682_);
        v___x_2684_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2684_, 0, v___x_2683_);
        v___x_2685_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2685_, 0, v___x_2681_);
        lean_ctor_set(v___x_2685_, 1, v___x_2684_);
        v___x_2686_ = l_Lean_IR_formatArray___at___00Lean_IR_formatParams_spec__0(v_xs_2679_);
        lean_dec_ref(v_xs_2679_);
        v___x_2687_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2687_, 0, v___x_2685_);
        lean_ctor_set(v___x_2687_, 1, v___x_2686_);
        v___x_2688_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam___closed__3;
        v___x_2689_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2689_, 0, v___x_2687_);
        lean_ctor_set(v___x_2689_, 1, v___x_2688_);
        v___x_2690_ = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(v_type_2680_);
        v___x_2691_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2691_, 0, v___x_2689_);
        lean_ctor_set(v___x_2691_, 1, v___x_2690_);
        return v___x_2691_;
    }
}
pub unsafe fn l_Lean_IR_instToFormatDecl___lam__0(
    mut v_decl_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2693_ = lean_unsigned_to_nat(2);
    v___x_2694_ = l_Lean_IR_formatDecl(v_decl_2692_, v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_IR_declToString(mut v_d_2697_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    v___x_2698_ = lean_unsigned_to_nat(2);
    v___x_2699_ = l_Lean_IR_formatDecl(v_d_2697_, v___x_2698_);
    v___x_2700_ = l_Std_Format_defWidth;
    v___x_2701_ = lean_unsigned_to_nat(0);
    v___x_2702_ = l_Std_Format_pretty(v___x_2699_, v___x_2700_, v___x_2701_, v___x_2701_);
    return v___x_2702_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Format(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Format(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Format(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Format(builtin);
}
