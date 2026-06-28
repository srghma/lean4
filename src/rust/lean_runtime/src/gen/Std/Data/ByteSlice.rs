// Lean compiler output
// Module: Std.Data.ByteSlice
// Imports: Init.Data.ByteArray Init.Data.Slice.Basic Init.Data.Slice.Notation Init.Data.Range.Polymorphic.Nat Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_extract;
use crate::r#gen::Init::Data::ByteArray::{
    initialize_Init_Data_ByteArray, runtime_initialize_Init_Data_ByteArray,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Slice::Basic::{
    initialize_Init_Data_Slice_Basic, runtime_initialize_Init_Data_Slice_Basic,
};
use crate::r#gen::Init::Data::Slice::Notation::{
    initialize_Init_Data_Slice_Notation, runtime_initialize_Init_Data_Slice_Notation,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_fget;
use crate::lean_imports_rs::Init::Prelude::{
    lean_byte_array_mk, lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_uint8_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unbox, lean_unsigned_to_nat,
};
pub static l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteSlice_instGetElemNatUInt8LtSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value) as *mut LeanObject;
pub static mut l_ByteSlice_instGetElemNatUInt8LtSize: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value) as *mut LeanObject;
pub static l_ByteSlice_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_ByteSlice_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__0_value) as *mut LeanObject;
pub static l_ByteSlice_empty___closed__1_value: LeanScalarArrayObject<0> = LeanScalarArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>() * 2 + 0)
            as u16,
        other: 1,
        tag: 248,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_ByteSlice_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__1_value) as *mut LeanObject;
pub static l_ByteSlice_empty___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteSlice_empty___closed__1_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_ByteSlice_empty___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__2_value) as *mut LeanObject;
pub static mut l_ByteSlice_empty: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__2_value) as *mut LeanObject;
pub static mut l_ByteSlice_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__2_value) as *mut LeanObject;
pub static mut l_ByteSlice_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_empty___closed__2_value) as *mut LeanObject;
pub static l_ByteSlice_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteSlice_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteSlice_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_ByteSlice_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_instBEq___closed__0_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__0_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__1_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__2_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__3_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__4_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__5_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_ByteSlice_foldr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__6_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_ByteSlice_foldr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__7_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_ByteSlice_foldr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__8_value) as *mut LeanObject;
pub static l_ByteSlice_foldr___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_ByteSlice_foldr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_ByteSlice_foldr___redArg___closed__9_value) as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__1___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__1: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__1___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__2___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__2: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__2___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__3: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__3___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__4___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__4: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__4___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__5___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__5: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__5___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__6___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__6: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__6___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__7___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__7___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__7___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__7: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__7___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteArrayNatByteSlice__8___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteArrayNatByteSlice__8___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteArrayNatByteSlice__8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__8___closed__0_value)
        as *mut LeanObject;
pub static mut l_instSliceableByteArrayNatByteSlice__8: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteArrayNatByteSlice__8___closed__0_value)
        as *mut LeanObject;
pub static l_instSliceableByteSliceNat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__1___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__1: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__1___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__2___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__2: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__2___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__3___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__3: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__3___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__4___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__4___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__4: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__4___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__5___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__5: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__5___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__6___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__6: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__6___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__7___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__7___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__7___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__7___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__7: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__7___closed__0_value) as *mut LeanObject;
pub static l_instSliceableByteSliceNat__8___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceableByteSliceNat__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableByteSliceNat__8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__8___closed__0_value) as *mut LeanObject;
pub static mut l_instSliceableByteSliceNat__8: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceableByteSliceNat__8___closed__0_value) as *mut LeanObject;
pub unsafe fn l_ByteSlice_byteArray(mut v_xs_554_: *mut LeanObject) -> *mut LeanObject {
    let mut v_byteArray_555_: *mut LeanObject = core::ptr::null_mut();
    v_byteArray_555_ = lean_ctor_get(v_xs_554_, 0);
    lean_inc_ref(v_byteArray_555_);
    return v_byteArray_555_;
}
pub unsafe fn l_ByteSlice_byteArray___boxed(mut v_xs_556_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_ByteSlice_byteArray(v_xs_556_);
    lean_dec_ref(v_xs_556_);
    return v_res_557_;
}
pub unsafe fn l_ByteSlice_start(mut v_xs_558_: *mut LeanObject) -> *mut LeanObject {
    let mut v_start_559_: *mut LeanObject = core::ptr::null_mut();
    v_start_559_ = lean_ctor_get(v_xs_558_, 1);
    lean_inc(v_start_559_);
    return v_start_559_;
}
pub unsafe fn l_ByteSlice_start___boxed(mut v_xs_560_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_561_: *mut LeanObject = core::ptr::null_mut();
    v_res_561_ = l_ByteSlice_start(v_xs_560_);
    lean_dec_ref(v_xs_560_);
    return v_res_561_;
}
pub unsafe fn l_ByteSlice_stop(mut v_xs_562_: *mut LeanObject) -> *mut LeanObject {
    let mut v_stop_563_: *mut LeanObject = core::ptr::null_mut();
    v_stop_563_ = lean_ctor_get(v_xs_562_, 2);
    lean_inc(v_stop_563_);
    return v_stop_563_;
}
pub unsafe fn l_ByteSlice_stop___boxed(mut v_xs_564_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_565_ = l_ByteSlice_stop(v_xs_564_);
    lean_dec_ref(v_xs_564_);
    return v_res_565_;
}
pub unsafe fn l_ByteSlice_size(mut v_s_566_: *mut LeanObject) -> *mut LeanObject {
    let mut v_start_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    v_start_567_ = lean_ctor_get(v_s_566_, 1);
    v_stop_568_ = lean_ctor_get(v_s_566_, 2);
    v___x_569_ = lean_nat_sub(v_stop_568_, v_start_567_);
    return v___x_569_;
}
pub unsafe fn l_ByteSlice_size___boxed(mut v_s_570_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_571_: *mut LeanObject = core::ptr::null_mut();
    v_res_571_ = l_ByteSlice_size(v_s_570_);
    lean_dec_ref(v_s_570_);
    return v_res_571_;
}
pub unsafe fn l_ByteSlice_get(mut v_s_572_: *mut LeanObject, mut v_i_573_: *mut LeanObject) -> u8 {
    let mut v_byteArray_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: u8 = 0;
    v_byteArray_574_ = lean_ctor_get(v_s_572_, 0);
    v_start_575_ = lean_ctor_get(v_s_572_, 1);
    v___x_576_ = lean_nat_add(v_start_575_, v_i_573_);
    v___x_577_ = lean_byte_array_fget(v_byteArray_574_, v___x_576_);
    lean_dec(v___x_576_);
    return v___x_577_;
}
pub unsafe fn l_ByteSlice_get___boxed(
    mut v_s_578_: *mut LeanObject,
    mut v_i_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_580_: u8 = 0;
    let mut v_r_581_: *mut LeanObject = core::ptr::null_mut();
    v_res_580_ = l_ByteSlice_get(v_s_578_, v_i_579_);
    lean_dec(v_i_579_);
    lean_dec_ref(v_s_578_);
    v_r_581_ = lean_box((v_res_580_) as usize);
    return v_r_581_;
}
pub unsafe fn l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(
    mut v_xs_582_: *mut LeanObject,
    mut v_i_583_: *mut LeanObject,
    mut v_h_584_: *mut LeanObject,
) -> u8 {
    let mut v___x_585_: u8 = 0;
    v___x_585_ = l_ByteSlice_get(v_xs_582_, v_i_583_);
    return v___x_585_;
}
pub unsafe fn l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed(
    mut v_xs_586_: *mut LeanObject,
    mut v_i_587_: *mut LeanObject,
    mut v_h_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_589_: u8 = 0;
    let mut v_r_590_: *mut LeanObject = core::ptr::null_mut();
    v_res_589_ = l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(v_xs_586_, v_i_587_, v_h_588_);
    lean_dec(v_i_587_);
    lean_dec_ref(v_xs_586_);
    v_r_590_ = lean_box((v_res_589_) as usize);
    return v_r_590_;
}
pub unsafe fn l_ByteSlice_getD(
    mut v_s_593_: *mut LeanObject,
    mut v_i_594_: *mut LeanObject,
    mut v_v_u2080_595_: u8,
) -> u8 {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    v___x_596_ = l_ByteSlice_size(v_s_593_);
    v___x_597_ = lean_nat_dec_lt(v_i_594_, v___x_596_);
    lean_dec(v___x_596_);
    if v___x_597_ == 0 {
        return v_v_u2080_595_;
    } else {
        let mut v___x_598_: u8 = 0;
        v___x_598_ = l_ByteSlice_get(v_s_593_, v_i_594_);
        return v___x_598_;
    }
}
pub unsafe fn l_ByteSlice_getD___boxed(
    mut v_s_599_: *mut LeanObject,
    mut v_i_600_: *mut LeanObject,
    mut v_v_u2080_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_u2080_boxed_602_: u8 = 0;
    let mut v_res_603_: u8 = 0;
    let mut v_r_604_: *mut LeanObject = core::ptr::null_mut();
    v_v_u2080_boxed_602_ = (lean_unbox(v_v_u2080_601_) as u8);
    v_res_603_ = l_ByteSlice_getD(v_s_599_, v_i_600_, v_v_u2080_boxed_602_);
    lean_dec(v_i_600_);
    lean_dec_ref(v_s_599_);
    v_r_604_ = lean_box((v_res_603_) as usize);
    return v_r_604_;
}
pub unsafe fn l_ByteSlice_get_x21(
    mut v_s_605_: *mut LeanObject,
    mut v_i_606_: *mut LeanObject,
) -> u8 {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: u8 = 0;
    v___x_607_ = l_ByteSlice_size(v_s_605_);
    v___x_608_ = lean_nat_dec_lt(v_i_606_, v___x_607_);
    lean_dec(v___x_607_);
    if v___x_608_ == 0 {
        let mut v___x_609_: u8 = 0;
        v___x_609_ = 0;
        return v___x_609_;
    } else {
        let mut v___x_610_: u8 = 0;
        v___x_610_ = l_ByteSlice_get(v_s_605_, v_i_606_);
        return v___x_610_;
    }
}
pub unsafe fn l_ByteSlice_get_x21___boxed(
    mut v_s_611_: *mut LeanObject,
    mut v_i_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_613_: u8 = 0;
    let mut v_r_614_: *mut LeanObject = core::ptr::null_mut();
    v_res_613_ = l_ByteSlice_get_x21(v_s_611_, v_i_612_);
    lean_dec(v_i_612_);
    lean_dec_ref(v_s_611_);
    v_r_614_ = lean_box((v_res_613_) as usize);
    return v_r_614_;
}
pub unsafe fn l_ByteSlice_ofByteArray(mut v_ba_623_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = lean_unsigned_to_nat(0);
    v___x_625_ = lean_byte_array_size(v_ba_623_);
    v___x_626_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_626_, 0, v_ba_623_);
    lean_ctor_set(v___x_626_, 1, v___x_624_);
    lean_ctor_set(v___x_626_, 2, v___x_625_);
    return v___x_626_;
}
pub unsafe fn l_ByteSlice_toByteArray(mut v_s_629_: *mut LeanObject) -> *mut LeanObject {
    let mut v_byteArray_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    v_byteArray_630_ = lean_ctor_get(v_s_629_, 0);
    lean_inc_ref(v_byteArray_630_);
    v_start_631_ = lean_ctor_get(v_s_629_, 1);
    lean_inc(v_start_631_);
    v___x_632_ = l_ByteSlice_size(v_s_629_);
    lean_dec_ref(v_s_629_);
    v___x_633_ = lean_nat_add(v_start_631_, v___x_632_);
    lean_dec(v___x_632_);
    v___x_634_ = l_ByteArray_extract(v_byteArray_630_, v_start_631_, v___x_633_);
    lean_dec(v___x_633_);
    lean_dec_ref(v_byteArray_630_);
    return v___x_634_;
}
pub unsafe fn l_ByteSlice_beq___boxed(
    mut v_a_637_: *mut LeanObject,
    mut v_b_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_639_: u8 = 0;
    let mut v_r_640_: *mut LeanObject = core::ptr::null_mut();
    v_res_639_ = lean_byteslice_beq(v_a_637_, v_b_638_);
    lean_dec_ref(v_b_638_);
    lean_dec_ref(v_a_637_);
    v_r_640_ = lean_box((v_res_639_) as usize);
    return v_r_640_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed(
    mut v_i_643_: *mut LeanObject,
    mut v___x_644_: *mut LeanObject,
    mut v_inst_645_: *mut LeanObject,
    mut v_f_646_: *mut LeanObject,
    mut v_as_647_: *mut LeanObject,
    mut v_newAcc_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_649_: *mut LeanObject = core::ptr::null_mut();
    v_res_649_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(
        v_i_643_,
        v___x_644_,
        v_inst_645_,
        v_f_646_,
        v_as_647_,
        v_newAcc_648_,
    );
    lean_dec(v___x_644_);
    lean_dec(v_i_643_);
    return v_res_649_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
    mut v_inst_650_: *mut LeanObject,
    mut v_f_651_: *mut LeanObject,
    mut v_as_652_: *mut LeanObject,
    mut v_i_653_: *mut LeanObject,
    mut v_acc_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: u8 = 0;
    v___x_655_ = l_ByteSlice_size(v_as_652_);
    v___x_656_ = lean_nat_dec_lt(v_i_653_, v___x_655_);
    if v___x_656_ == 0 {
        let mut v_toApplicative_657_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_655_);
        lean_dec(v_i_653_);
        lean_dec_ref(v_as_652_);
        lean_dec(v_f_651_);
        v_toApplicative_657_ = lean_ctor_get(v_inst_650_, 0);
        lean_inc_ref(v_toApplicative_657_);
        lean_dec_ref(v_inst_650_);
        v_toPure_658_ = lean_ctor_get(v_toApplicative_657_, 1);
        lean_inc(v_toPure_658_);
        lean_dec_ref(v_toApplicative_657_);
        v___x_659_ = lean_apply_2(v_toPure_658_, lean_box(0), v_acc_654_);
        return v___x_659_;
    } else {
        let mut v_toBind_660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_665_: u8 = 0;
        let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_660_ = lean_ctor_get(v_inst_650_, 1);
        lean_inc(v_toBind_660_);
        v___x_661_ = lean_unsigned_to_nat(1);
        lean_inc_ref(v_as_652_);
        lean_inc(v_f_651_);
        lean_inc(v_i_653_);
        v___f_662_ = lean_alloc_closure(
            l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_662_, 0, v_i_653_);
        lean_closure_set(v___f_662_, 1, v___x_661_);
        lean_closure_set(v___f_662_, 2, v_inst_650_);
        lean_closure_set(v___f_662_, 3, v_f_651_);
        lean_closure_set(v___f_662_, 4, v_as_652_);
        v___x_663_ = lean_nat_sub(v___x_655_, v___x_661_);
        lean_dec(v___x_655_);
        v___x_664_ = lean_nat_sub(v___x_663_, v_i_653_);
        lean_dec(v_i_653_);
        lean_dec(v___x_663_);
        v___x_665_ = l_ByteSlice_get(v_as_652_, v___x_664_);
        lean_dec(v___x_664_);
        lean_dec_ref(v_as_652_);
        v___x_666_ = lean_box((v___x_665_) as usize);
        v___x_667_ = lean_apply_2(v_f_651_, v___x_666_, v_acc_654_);
        v___x_668_ = lean_apply_4(
            v_toBind_660_,
            lean_box(0),
            lean_box(0),
            v___x_667_,
            v___f_662_,
        );
        return v___x_668_;
    }
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(
    mut v_i_669_: *mut LeanObject,
    mut v___x_670_: *mut LeanObject,
    mut v_inst_671_: *mut LeanObject,
    mut v_f_672_: *mut LeanObject,
    mut v_as_673_: *mut LeanObject,
    mut v_newAcc_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___x_675_ = lean_nat_add(v_i_669_, v___x_670_);
    v___x_676_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v_inst_671_,
        v_f_672_,
        v_as_673_,
        v___x_675_,
        v_newAcc_674_,
    );
    return v___x_676_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop(
    mut v_00_u03b2_677_: *mut LeanObject,
    mut v_m_678_: *mut LeanObject,
    mut v_inst_679_: *mut LeanObject,
    mut v_f_680_: *mut LeanObject,
    mut v_as_681_: *mut LeanObject,
    mut v_i_682_: *mut LeanObject,
    mut v_acc_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v___x_684_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v_inst_679_,
        v_f_680_,
        v_as_681_,
        v_i_682_,
        v_acc_683_,
    );
    return v___x_684_;
}
pub unsafe fn l_ByteSlice_foldrM___redArg(
    mut v_inst_685_: *mut LeanObject,
    mut v_f_686_: *mut LeanObject,
    mut v_init_687_: *mut LeanObject,
    mut v_as_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = lean_unsigned_to_nat(0);
    v___x_690_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v_inst_685_,
        v_f_686_,
        v_as_688_,
        v___x_689_,
        v_init_687_,
    );
    return v___x_690_;
}
pub unsafe fn l_ByteSlice_foldrM(
    mut v_00_u03b2_691_: *mut LeanObject,
    mut v_m_692_: *mut LeanObject,
    mut v_inst_693_: *mut LeanObject,
    mut v_f_694_: *mut LeanObject,
    mut v_init_695_: *mut LeanObject,
    mut v_as_696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = lean_unsigned_to_nat(0);
    v___x_698_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v_inst_693_,
        v_f_694_,
        v_as_696_,
        v___x_697_,
        v_init_695_,
    );
    return v___x_698_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed(
    mut v_i_699_: *mut LeanObject,
    mut v_inst_700_: *mut LeanObject,
    mut v_f_701_: *mut LeanObject,
    mut v_as_702_: *mut LeanObject,
    mut v_____r_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(
        v_i_699_,
        v_inst_700_,
        v_f_701_,
        v_as_702_,
        v_____r_703_,
    );
    lean_dec(v_i_699_);
    return v_res_704_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(
    mut v_inst_705_: *mut LeanObject,
    mut v_f_706_: *mut LeanObject,
    mut v_as_707_: *mut LeanObject,
    mut v_i_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    v___x_709_ = l_ByteSlice_size(v_as_707_);
    v___x_710_ = lean_nat_dec_lt(v_i_708_, v___x_709_);
    lean_dec(v___x_709_);
    if v___x_710_ == 0 {
        let mut v_toApplicative_711_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_708_);
        lean_dec_ref(v_as_707_);
        lean_dec(v_f_706_);
        v_toApplicative_711_ = lean_ctor_get(v_inst_705_, 0);
        lean_inc_ref(v_toApplicative_711_);
        lean_dec_ref(v_inst_705_);
        v_toPure_712_ = lean_ctor_get(v_toApplicative_711_, 1);
        lean_inc(v_toPure_712_);
        lean_dec_ref(v_toApplicative_711_);
        v___x_713_ = lean_box(0);
        v___x_714_ = lean_apply_2(v_toPure_712_, lean_box(0), v___x_713_);
        return v___x_714_;
    } else {
        let mut v_toBind_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_717_: u8 = 0;
        let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_715_ = lean_ctor_get(v_inst_705_, 1);
        lean_inc(v_toBind_715_);
        lean_inc_ref(v_as_707_);
        lean_inc(v_f_706_);
        lean_inc(v_i_708_);
        v___f_716_ = lean_alloc_closure(
            l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_716_, 0, v_i_708_);
        lean_closure_set(v___f_716_, 1, v_inst_705_);
        lean_closure_set(v___f_716_, 2, v_f_706_);
        lean_closure_set(v___f_716_, 3, v_as_707_);
        v___x_717_ = l_ByteSlice_get(v_as_707_, v_i_708_);
        lean_dec(v_i_708_);
        lean_dec_ref(v_as_707_);
        v___x_718_ = lean_box((v___x_717_) as usize);
        v___x_719_ = lean_apply_1(v_f_706_, v___x_718_);
        v___x_720_ = lean_apply_4(
            v_toBind_715_,
            lean_box(0),
            lean_box(0),
            v___x_719_,
            v___f_716_,
        );
        return v___x_720_;
    }
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(
    mut v_i_721_: *mut LeanObject,
    mut v_inst_722_: *mut LeanObject,
    mut v_f_723_: *mut LeanObject,
    mut v_as_724_: *mut LeanObject,
    mut v_____r_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_726_ = lean_unsigned_to_nat(1);
    v___x_727_ = lean_nat_add(v_i_721_, v___x_726_);
    v___x_728_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(
        v_inst_722_,
        v_f_723_,
        v_as_724_,
        v___x_727_,
    );
    return v___x_728_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop(
    mut v_m_729_: *mut LeanObject,
    mut v_inst_730_: *mut LeanObject,
    mut v_f_731_: *mut LeanObject,
    mut v_as_732_: *mut LeanObject,
    mut v_i_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(
        v_inst_730_,
        v_f_731_,
        v_as_732_,
        v_i_733_,
    );
    return v___x_734_;
}
pub unsafe fn l_ByteSlice_forM___redArg(
    mut v_inst_735_: *mut LeanObject,
    mut v_f_736_: *mut LeanObject,
    mut v_as_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = lean_unsigned_to_nat(0);
    v___x_739_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(
        v_inst_735_,
        v_f_736_,
        v_as_737_,
        v___x_738_,
    );
    return v___x_739_;
}
pub unsafe fn l_ByteSlice_forM(
    mut v_m_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
    mut v_f_742_: *mut LeanObject,
    mut v_as_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = lean_unsigned_to_nat(0);
    v___x_745_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(
        v_inst_741_,
        v_f_742_,
        v_as_743_,
        v___x_744_,
    );
    return v___x_745_;
}
pub unsafe fn l_ByteSlice_foldr___redArg___lam__0(
    mut v_f_746_: *mut LeanObject,
    mut v_x1_747_: u8,
    mut v_x2_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    v___x_749_ = lean_box((v_x1_747_) as usize);
    v___x_750_ = lean_apply_2(v_f_746_, v___x_749_, v_x2_748_);
    return v___x_750_;
}
pub unsafe fn l_ByteSlice_foldr___redArg___lam__0___boxed(
    mut v_f_751_: *mut LeanObject,
    mut v_x1_752_: *mut LeanObject,
    mut v_x2_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x1_85__boxed_754_: u8 = 0;
    let mut v_res_755_: *mut LeanObject = core::ptr::null_mut();
    v_x1_85__boxed_754_ = (lean_unbox(v_x1_752_) as u8);
    v_res_755_ = l_ByteSlice_foldr___redArg___lam__0(v_f_751_, v_x1_85__boxed_754_, v_x2_753_);
    return v_res_755_;
}
pub unsafe fn l_ByteSlice_foldr___redArg(
    mut v_f_775_: *mut LeanObject,
    mut v_init_776_: *mut LeanObject,
    mut v_as_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___f_778_ = lean_alloc_closure(
        l_ByteSlice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_778_, 0, v_f_775_);
    v___x_779_ = l_ByteSlice_foldr___redArg___closed__9;
    v___x_780_ = lean_unsigned_to_nat(0);
    v___x_781_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v___x_779_,
        v___f_778_,
        v_as_777_,
        v___x_780_,
        v_init_776_,
    );
    return v___x_781_;
}
pub unsafe fn l_ByteSlice_foldr(
    mut v_00_u03b2_782_: *mut LeanObject,
    mut v_f_783_: *mut LeanObject,
    mut v_init_784_: *mut LeanObject,
    mut v_as_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    v___f_786_ = lean_alloc_closure(
        l_ByteSlice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_786_, 0, v_f_783_);
    v___x_787_ = l_ByteSlice_foldr___redArg___closed__9;
    v___x_788_ = lean_unsigned_to_nat(0);
    v___x_789_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(
        v___x_787_,
        v___f_786_,
        v_as_785_,
        v___x_788_,
        v_init_784_,
    );
    return v___x_789_;
}
pub unsafe fn l_ByteSlice_slice(
    mut v_s_790_: *mut LeanObject,
    mut v_start_791_: *mut LeanObject,
    mut v_stop_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_byteArray_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actualStop_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u8 = 0;
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actualStart_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: u8 = 0;
    let mut v___x_810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_byteArray_793_ = lean_ctor_get(v_s_790_, 0);
                v_start_794_ = lean_ctor_get(v_s_790_, 1);
                v___x_805_ = l_ByteSlice_size(v_s_790_);
                v___x_810_ = lean_nat_dec_le(v_start_791_, v___x_805_);
                if v___x_810_ == 0 {
                    lean_dec(v_start_791_);
                    lean_inc(v___x_805_);
                    v___y_807_ = v___x_805_;
                    state = 2;
                    continue;
                } else {
                    v___y_807_ = v_start_791_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v_actualStop_798_ = lean_nat_add(v_start_794_, v___y_797_);
                lean_dec(v___y_797_);
                v___x_799_ = lean_byte_array_size(v_byteArray_793_);
                v___x_800_ = lean_nat_dec_le(v_actualStop_798_, v___x_799_);
                if v___x_800_ == 0 {
                    lean_dec(v_actualStop_798_);
                    lean_dec(v___y_796_);
                    lean_inc_n(v_start_794_, 2);
                    lean_inc_ref(v_byteArray_793_);
                    v___x_801_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_801_, 0, v_byteArray_793_);
                    lean_ctor_set(v___x_801_, 1, v_start_794_);
                    lean_ctor_set(v___x_801_, 2, v_start_794_);
                    return v___x_801_;
                } else {
                    v___x_802_ = lean_nat_dec_le(v___y_796_, v_actualStop_798_);
                    if v___x_802_ == 0 {
                        lean_dec(v___y_796_);
                        lean_inc(v_actualStop_798_);
                        lean_inc_ref(v_byteArray_793_);
                        v___x_803_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_803_, 0, v_byteArray_793_);
                        lean_ctor_set(v___x_803_, 1, v_actualStop_798_);
                        lean_ctor_set(v___x_803_, 2, v_actualStop_798_);
                        return v___x_803_;
                    } else {
                        lean_inc_ref(v_byteArray_793_);
                        v___x_804_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_804_, 0, v_byteArray_793_);
                        lean_ctor_set(v___x_804_, 1, v___y_796_);
                        lean_ctor_set(v___x_804_, 2, v_actualStop_798_);
                        return v___x_804_;
                    }
                }
            }
            2 => {
                v_actualStart_808_ = lean_nat_add(v_start_794_, v___y_807_);
                lean_dec(v___y_807_);
                v___x_809_ = lean_nat_dec_le(v_stop_792_, v___x_805_);
                if v___x_809_ == 0 {
                    lean_dec(v_stop_792_);
                    v___y_796_ = v_actualStart_808_;
                    v___y_797_ = v___x_805_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_805_);
                    v___y_796_ = v_actualStart_808_;
                    v___y_797_ = v_stop_792_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteSlice_slice___boxed(
    mut v_s_811_: *mut LeanObject,
    mut v_start_812_: *mut LeanObject,
    mut v_stop_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_814_: *mut LeanObject = core::ptr::null_mut();
    v_res_814_ = l_ByteSlice_slice(v_s_811_, v_start_812_, v_stop_813_);
    lean_dec_ref(v_s_811_);
    return v_res_814_;
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(
    mut v_s_815_: *mut LeanObject,
    mut v_byte_816_: u8,
    mut v_i_817_: *mut LeanObject,
) -> u8 {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    let mut v___x_820_: u8 = 0;
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_818_ = l_ByteSlice_size(v_s_815_);
                v___x_819_ = lean_nat_dec_lt(v_i_817_, v___x_818_);
                lean_dec(v___x_818_);
                if v___x_819_ == 0 {
                    lean_dec(v_i_817_);
                    return v___x_819_;
                } else {
                    v___x_820_ = l_ByteSlice_get(v_s_815_, v_i_817_);
                    v___x_821_ = lean_uint8_dec_eq(v___x_820_, v_byte_816_);
                    if v___x_821_ == 0 {
                        v___x_822_ = lean_unsigned_to_nat(1);
                        v___x_823_ = lean_nat_add(v_i_817_, v___x_822_);
                        lean_dec(v_i_817_);
                        v_i_817_ = v___x_823_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_817_);
                        return v___x_821_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop___boxed(
    mut v_s_825_: *mut LeanObject,
    mut v_byte_826_: *mut LeanObject,
    mut v_i_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_byte_boxed_828_: u8 = 0;
    let mut v_res_829_: u8 = 0;
    let mut v_r_830_: *mut LeanObject = core::ptr::null_mut();
    v_byte_boxed_828_ = (lean_unbox(v_byte_826_) as u8);
    v_res_829_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(
        v_s_825_,
        v_byte_boxed_828_,
        v_i_827_,
    );
    lean_dec_ref(v_s_825_);
    v_r_830_ = lean_box((v_res_829_) as usize);
    return v_r_830_;
}
pub unsafe fn l_ByteSlice_contains(mut v_s_831_: *mut LeanObject, mut v_byte_832_: u8) -> u8 {
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    v___x_833_ = lean_unsigned_to_nat(0);
    v___x_834_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(
        v_s_831_,
        v_byte_832_,
        v___x_833_,
    );
    return v___x_834_;
}
pub unsafe fn l_ByteSlice_contains___boxed(
    mut v_s_835_: *mut LeanObject,
    mut v_byte_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_byte_boxed_837_: u8 = 0;
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut LeanObject = core::ptr::null_mut();
    v_byte_boxed_837_ = (lean_unbox(v_byte_836_) as u8);
    v_res_838_ = l_ByteSlice_contains(v_s_835_, v_byte_boxed_837_);
    lean_dec_ref(v_s_835_);
    v_r_839_ = lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_ByteArray_toByteSlice(
    mut v_as_840_: *mut LeanObject,
    mut v_start_841_: *mut LeanObject,
    mut v_stop_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    v___x_843_ = lean_byte_array_size(v_as_840_);
    v___x_844_ = lean_nat_dec_le(v_stop_842_, v___x_843_);
    if v___x_844_ == 0 {
        let mut v___x_845_: u8 = 0;
        lean_dec(v_stop_842_);
        v___x_845_ = lean_nat_dec_le(v_start_841_, v___x_843_);
        if v___x_845_ == 0 {
            let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_start_841_);
            v___x_846_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_846_, 0, v_as_840_);
            lean_ctor_set(v___x_846_, 1, v___x_843_);
            lean_ctor_set(v___x_846_, 2, v___x_843_);
            return v___x_846_;
        } else {
            let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
            v___x_847_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_847_, 0, v_as_840_);
            lean_ctor_set(v___x_847_, 1, v_start_841_);
            lean_ctor_set(v___x_847_, 2, v___x_843_);
            return v___x_847_;
        }
    } else {
        let mut v___x_848_: u8 = 0;
        v___x_848_ = lean_nat_dec_le(v_start_841_, v_stop_842_);
        if v___x_848_ == 0 {
            let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_start_841_);
            lean_inc(v_stop_842_);
            v___x_849_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_849_, 0, v_as_840_);
            lean_ctor_set(v___x_849_, 1, v_stop_842_);
            lean_ctor_set(v___x_849_, 2, v_stop_842_);
            return v___x_849_;
        } else {
            let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
            v___x_850_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_850_, 0, v_as_840_);
            lean_ctor_set(v___x_850_, 1, v_start_841_);
            lean_ctor_set(v___x_850_, 2, v_stop_842_);
            return v___x_850_;
        }
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice___lam__0(
    mut v_xs_851_: *mut LeanObject,
    mut v_range_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_853_ = lean_ctor_get(v_range_852_, 0);
                lean_inc(v_lower_853_);
                v_upper_854_ = lean_ctor_get(v_range_852_, 1);
                lean_inc(v_upper_854_);
                lean_dec_ref(v_range_852_);
                v___x_855_ = lean_unsigned_to_nat(0);
                v___x_856_ = lean_byte_array_size(v_xs_851_);
                v___x_864_ = lean_nat_dec_le(v_lower_853_, v___x_855_);
                if v___x_864_ == 0 {
                    v___y_858_ = v_lower_853_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_lower_853_);
                    v___y_858_ = v___x_855_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_859_ = lean_unsigned_to_nat(1);
                v___x_860_ = lean_nat_add(v_upper_854_, v___x_859_);
                lean_dec(v_upper_854_);
                v___x_861_ = lean_nat_dec_le(v___x_860_, v___x_856_);
                if v___x_861_ == 0 {
                    lean_dec(v___x_860_);
                    v___x_862_ = l_ByteArray_toByteSlice(v_xs_851_, v___y_858_, v___x_856_);
                    return v___x_862_;
                } else {
                    v___x_863_ = l_ByteArray_toByteSlice(v_xs_851_, v___y_858_, v___x_860_);
                    return v___x_863_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__1___lam__0(
    mut v_xs_867_: *mut LeanObject,
    mut v_range_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_869_ = lean_ctor_get(v_range_868_, 0);
                lean_inc(v_lower_869_);
                v_upper_870_ = lean_ctor_get(v_range_868_, 1);
                lean_inc(v_upper_870_);
                lean_dec_ref(v_range_868_);
                v___x_871_ = lean_unsigned_to_nat(0);
                v___x_872_ = lean_byte_array_size(v_xs_867_);
                v___x_878_ = lean_nat_dec_le(v_lower_869_, v___x_871_);
                if v___x_878_ == 0 {
                    v___y_874_ = v_lower_869_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_lower_869_);
                    v___y_874_ = v___x_871_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_875_ = lean_nat_dec_le(v_upper_870_, v___x_872_);
                if v___x_875_ == 0 {
                    lean_dec(v_upper_870_);
                    v___x_876_ = l_ByteArray_toByteSlice(v_xs_867_, v___y_874_, v___x_872_);
                    return v___x_876_;
                } else {
                    v___x_877_ = l_ByteArray_toByteSlice(v_xs_867_, v___y_874_, v_upper_870_);
                    return v___x_877_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__2___lam__0(
    mut v_xs_881_: *mut LeanObject,
    mut v_range_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    v___x_883_ = lean_unsigned_to_nat(0);
    v___x_884_ = lean_byte_array_size(v_xs_881_);
    v___x_885_ = lean_nat_dec_le(v_range_882_, v___x_883_);
    if v___x_885_ == 0 {
        let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
        v___x_886_ = l_ByteArray_toByteSlice(v_xs_881_, v_range_882_, v___x_884_);
        return v___x_886_;
    } else {
        let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_range_882_);
        v___x_887_ = l_ByteArray_toByteSlice(v_xs_881_, v___x_883_, v___x_884_);
        return v___x_887_;
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__3___lam__0(
    mut v_xs_890_: *mut LeanObject,
    mut v_range_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_892_ = lean_ctor_get(v_range_891_, 0);
                v_upper_893_ = lean_ctor_get(v_range_891_, 1);
                v___x_894_ = lean_unsigned_to_nat(0);
                v___x_895_ = lean_byte_array_size(v_xs_890_);
                v___x_896_ = lean_unsigned_to_nat(1);
                v___x_903_ = lean_nat_add(v_lower_892_, v___x_896_);
                v___x_904_ = lean_nat_dec_le(v___x_903_, v___x_894_);
                if v___x_904_ == 0 {
                    v___y_898_ = v___x_903_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_903_);
                    v___y_898_ = v___x_894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_899_ = lean_nat_add(v_upper_893_, v___x_896_);
                v___x_900_ = lean_nat_dec_le(v___x_899_, v___x_895_);
                if v___x_900_ == 0 {
                    lean_dec(v___x_899_);
                    v___x_901_ = l_ByteArray_toByteSlice(v_xs_890_, v___y_898_, v___x_895_);
                    return v___x_901_;
                } else {
                    v___x_902_ = l_ByteArray_toByteSlice(v_xs_890_, v___y_898_, v___x_899_);
                    return v___x_902_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed(
    mut v_xs_905_: *mut LeanObject,
    mut v_range_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_907_: *mut LeanObject = core::ptr::null_mut();
    v_res_907_ = l_instSliceableByteArrayNatByteSlice__3___lam__0(v_xs_905_, v_range_906_);
    lean_dec_ref(v_range_906_);
    return v_res_907_;
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__4___lam__0(
    mut v_xs_910_: *mut LeanObject,
    mut v_range_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_912_ = lean_ctor_get(v_range_911_, 0);
                lean_inc(v_lower_912_);
                v_upper_913_ = lean_ctor_get(v_range_911_, 1);
                lean_inc(v_upper_913_);
                lean_dec_ref(v_range_911_);
                v___x_914_ = lean_unsigned_to_nat(0);
                v___x_915_ = lean_byte_array_size(v_xs_910_);
                v___x_921_ = lean_unsigned_to_nat(1);
                v___x_922_ = lean_nat_add(v_lower_912_, v___x_921_);
                lean_dec(v_lower_912_);
                v___x_923_ = lean_nat_dec_le(v___x_922_, v___x_914_);
                if v___x_923_ == 0 {
                    v___y_917_ = v___x_922_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_922_);
                    v___y_917_ = v___x_914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_918_ = lean_nat_dec_le(v_upper_913_, v___x_915_);
                if v___x_918_ == 0 {
                    lean_dec(v_upper_913_);
                    v___x_919_ = l_ByteArray_toByteSlice(v_xs_910_, v___y_917_, v___x_915_);
                    return v___x_919_;
                } else {
                    v___x_920_ = l_ByteArray_toByteSlice(v_xs_910_, v___y_917_, v_upper_913_);
                    return v___x_920_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__5___lam__0(
    mut v_xs_926_: *mut LeanObject,
    mut v_range_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: u8 = 0;
    v___x_928_ = lean_unsigned_to_nat(0);
    v___x_929_ = lean_byte_array_size(v_xs_926_);
    v___x_930_ = lean_unsigned_to_nat(1);
    v___x_931_ = lean_nat_add(v_range_927_, v___x_930_);
    v___x_932_ = lean_nat_dec_le(v___x_931_, v___x_928_);
    if v___x_932_ == 0 {
        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
        v___x_933_ = l_ByteArray_toByteSlice(v_xs_926_, v___x_931_, v___x_929_);
        return v___x_933_;
    } else {
        let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_931_);
        v___x_934_ = l_ByteArray_toByteSlice(v_xs_926_, v___x_928_, v___x_929_);
        return v___x_934_;
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed(
    mut v_xs_935_: *mut LeanObject,
    mut v_range_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_937_: *mut LeanObject = core::ptr::null_mut();
    v_res_937_ = l_instSliceableByteArrayNatByteSlice__5___lam__0(v_xs_935_, v_range_936_);
    lean_dec(v_range_936_);
    return v_res_937_;
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__6___lam__0(
    mut v_xs_940_: *mut LeanObject,
    mut v_range_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: u8 = 0;
    v___x_942_ = lean_unsigned_to_nat(0);
    v___x_943_ = lean_byte_array_size(v_xs_940_);
    v___x_944_ = lean_unsigned_to_nat(1);
    v___x_945_ = lean_nat_add(v_range_941_, v___x_944_);
    v___x_946_ = lean_nat_dec_le(v___x_945_, v___x_943_);
    if v___x_946_ == 0 {
        let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_945_);
        v___x_947_ = l_ByteArray_toByteSlice(v_xs_940_, v___x_942_, v___x_943_);
        return v___x_947_;
    } else {
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        v___x_948_ = l_ByteArray_toByteSlice(v_xs_940_, v___x_942_, v___x_945_);
        return v___x_948_;
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed(
    mut v_xs_949_: *mut LeanObject,
    mut v_range_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_951_: *mut LeanObject = core::ptr::null_mut();
    v_res_951_ = l_instSliceableByteArrayNatByteSlice__6___lam__0(v_xs_949_, v_range_950_);
    lean_dec(v_range_950_);
    return v_res_951_;
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__7___lam__0(
    mut v_xs_954_: *mut LeanObject,
    mut v_range_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    v___x_956_ = lean_unsigned_to_nat(0);
    v___x_957_ = lean_byte_array_size(v_xs_954_);
    v___x_958_ = lean_nat_dec_le(v_range_955_, v___x_957_);
    if v___x_958_ == 0 {
        let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_range_955_);
        v___x_959_ = l_ByteArray_toByteSlice(v_xs_954_, v___x_956_, v___x_957_);
        return v___x_959_;
    } else {
        let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
        v___x_960_ = l_ByteArray_toByteSlice(v_xs_954_, v___x_956_, v_range_955_);
        return v___x_960_;
    }
}
pub unsafe fn l_instSliceableByteArrayNatByteSlice__8___lam__0(
    mut v_xs_963_: *mut LeanObject,
    mut v_x_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = lean_unsigned_to_nat(0);
    v___x_966_ = lean_byte_array_size(v_xs_963_);
    v___x_967_ = l_ByteArray_toByteSlice(v_xs_963_, v___x_965_, v___x_966_);
    return v___x_967_;
}
pub unsafe fn l_instSliceableByteSliceNat___lam__0(
    mut v_xs_970_: *mut LeanObject,
    mut v_range_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_972_ = lean_ctor_get(v_range_971_, 0);
                lean_inc(v_lower_972_);
                v_upper_973_ = lean_ctor_get(v_range_971_, 1);
                lean_inc(v_upper_973_);
                lean_dec_ref(v_range_971_);
                v___x_974_ = lean_unsigned_to_nat(0);
                v___x_975_ = l_ByteSlice_size(v_xs_970_);
                v___x_983_ = lean_nat_dec_le(v_lower_972_, v___x_974_);
                if v___x_983_ == 0 {
                    v___y_977_ = v_lower_972_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_lower_972_);
                    v___y_977_ = v___x_974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_978_ = lean_unsigned_to_nat(1);
                v___x_979_ = lean_nat_add(v_upper_973_, v___x_978_);
                lean_dec(v_upper_973_);
                v___x_980_ = lean_nat_dec_le(v___x_979_, v___x_975_);
                if v___x_980_ == 0 {
                    lean_dec(v___x_979_);
                    v___x_981_ = l_ByteSlice_slice(v_xs_970_, v___y_977_, v___x_975_);
                    return v___x_981_;
                } else {
                    lean_dec(v___x_975_);
                    v___x_982_ = l_ByteSlice_slice(v_xs_970_, v___y_977_, v___x_979_);
                    return v___x_982_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteSliceNat___lam__0___boxed(
    mut v_xs_984_: *mut LeanObject,
    mut v_range_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_986_: *mut LeanObject = core::ptr::null_mut();
    v_res_986_ = l_instSliceableByteSliceNat___lam__0(v_xs_984_, v_range_985_);
    lean_dec_ref(v_xs_984_);
    return v_res_986_;
}
pub unsafe fn l_instSliceableByteSliceNat__1___lam__0(
    mut v_xs_989_: *mut LeanObject,
    mut v_range_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: u8 = 0;
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_991_ = lean_ctor_get(v_range_990_, 0);
                lean_inc(v_lower_991_);
                v_upper_992_ = lean_ctor_get(v_range_990_, 1);
                lean_inc(v_upper_992_);
                lean_dec_ref(v_range_990_);
                v___x_993_ = lean_unsigned_to_nat(0);
                v___x_994_ = l_ByteSlice_size(v_xs_989_);
                v___x_1000_ = lean_nat_dec_le(v_lower_991_, v___x_993_);
                if v___x_1000_ == 0 {
                    v___y_996_ = v_lower_991_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_lower_991_);
                    v___y_996_ = v___x_993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_997_ = lean_nat_dec_le(v_upper_992_, v___x_994_);
                if v___x_997_ == 0 {
                    lean_dec(v_upper_992_);
                    v___x_998_ = l_ByteSlice_slice(v_xs_989_, v___y_996_, v___x_994_);
                    return v___x_998_;
                } else {
                    lean_dec(v___x_994_);
                    v___x_999_ = l_ByteSlice_slice(v_xs_989_, v___y_996_, v_upper_992_);
                    return v___x_999_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteSliceNat__1___lam__0___boxed(
    mut v_xs_1001_: *mut LeanObject,
    mut v_range_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_instSliceableByteSliceNat__1___lam__0(v_xs_1001_, v_range_1002_);
    lean_dec_ref(v_xs_1001_);
    return v_res_1003_;
}
pub unsafe fn l_instSliceableByteSliceNat__2___lam__0(
    mut v_xs_1006_: *mut LeanObject,
    mut v_range_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u8 = 0;
    v___x_1008_ = lean_unsigned_to_nat(0);
    v___x_1009_ = l_ByteSlice_size(v_xs_1006_);
    v___x_1010_ = lean_nat_dec_le(v_range_1007_, v___x_1008_);
    if v___x_1010_ == 0 {
        let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
        v___x_1011_ = l_ByteSlice_slice(v_xs_1006_, v_range_1007_, v___x_1009_);
        return v___x_1011_;
    } else {
        let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_range_1007_);
        v___x_1012_ = l_ByteSlice_slice(v_xs_1006_, v___x_1008_, v___x_1009_);
        return v___x_1012_;
    }
}
pub unsafe fn l_instSliceableByteSliceNat__2___lam__0___boxed(
    mut v_xs_1013_: *mut LeanObject,
    mut v_range_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_instSliceableByteSliceNat__2___lam__0(v_xs_1013_, v_range_1014_);
    lean_dec_ref(v_xs_1013_);
    return v_res_1015_;
}
pub unsafe fn l_instSliceableByteSliceNat__3___lam__0(
    mut v_xs_1018_: *mut LeanObject,
    mut v_range_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1020_ = lean_ctor_get(v_range_1019_, 0);
                v_upper_1021_ = lean_ctor_get(v_range_1019_, 1);
                v___x_1022_ = lean_unsigned_to_nat(0);
                v___x_1023_ = l_ByteSlice_size(v_xs_1018_);
                v___x_1024_ = lean_unsigned_to_nat(1);
                v___x_1031_ = lean_nat_add(v_lower_1020_, v___x_1024_);
                v___x_1032_ = lean_nat_dec_le(v___x_1031_, v___x_1022_);
                if v___x_1032_ == 0 {
                    v___y_1026_ = v___x_1031_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1031_);
                    v___y_1026_ = v___x_1022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1027_ = lean_nat_add(v_upper_1021_, v___x_1024_);
                v___x_1028_ = lean_nat_dec_le(v___x_1027_, v___x_1023_);
                if v___x_1028_ == 0 {
                    lean_dec(v___x_1027_);
                    v___x_1029_ = l_ByteSlice_slice(v_xs_1018_, v___y_1026_, v___x_1023_);
                    return v___x_1029_;
                } else {
                    lean_dec(v___x_1023_);
                    v___x_1030_ = l_ByteSlice_slice(v_xs_1018_, v___y_1026_, v___x_1027_);
                    return v___x_1030_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteSliceNat__3___lam__0___boxed(
    mut v_xs_1033_: *mut LeanObject,
    mut v_range_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_instSliceableByteSliceNat__3___lam__0(v_xs_1033_, v_range_1034_);
    lean_dec_ref(v_range_1034_);
    lean_dec_ref(v_xs_1033_);
    return v_res_1035_;
}
pub unsafe fn l_instSliceableByteSliceNat__4___lam__0(
    mut v_xs_1038_: *mut LeanObject,
    mut v_range_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_1040_ = lean_ctor_get(v_range_1039_, 0);
                lean_inc(v_lower_1040_);
                v_upper_1041_ = lean_ctor_get(v_range_1039_, 1);
                lean_inc(v_upper_1041_);
                lean_dec_ref(v_range_1039_);
                v___x_1042_ = lean_unsigned_to_nat(0);
                v___x_1043_ = l_ByteSlice_size(v_xs_1038_);
                v___x_1049_ = lean_unsigned_to_nat(1);
                v___x_1050_ = lean_nat_add(v_lower_1040_, v___x_1049_);
                lean_dec(v_lower_1040_);
                v___x_1051_ = lean_nat_dec_le(v___x_1050_, v___x_1042_);
                if v___x_1051_ == 0 {
                    v___y_1045_ = v___x_1050_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1050_);
                    v___y_1045_ = v___x_1042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1046_ = lean_nat_dec_le(v_upper_1041_, v___x_1043_);
                if v___x_1046_ == 0 {
                    lean_dec(v_upper_1041_);
                    v___x_1047_ = l_ByteSlice_slice(v_xs_1038_, v___y_1045_, v___x_1043_);
                    return v___x_1047_;
                } else {
                    lean_dec(v___x_1043_);
                    v___x_1048_ = l_ByteSlice_slice(v_xs_1038_, v___y_1045_, v_upper_1041_);
                    return v___x_1048_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableByteSliceNat__4___lam__0___boxed(
    mut v_xs_1052_: *mut LeanObject,
    mut v_range_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_instSliceableByteSliceNat__4___lam__0(v_xs_1052_, v_range_1053_);
    lean_dec_ref(v_xs_1052_);
    return v_res_1054_;
}
pub unsafe fn l_instSliceableByteSliceNat__5___lam__0(
    mut v_xs_1057_: *mut LeanObject,
    mut v_range_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: u8 = 0;
    v___x_1059_ = lean_unsigned_to_nat(0);
    v___x_1060_ = l_ByteSlice_size(v_xs_1057_);
    v___x_1061_ = lean_unsigned_to_nat(1);
    v___x_1062_ = lean_nat_add(v_range_1058_, v___x_1061_);
    v___x_1063_ = lean_nat_dec_le(v___x_1062_, v___x_1059_);
    if v___x_1063_ == 0 {
        let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
        v___x_1064_ = l_ByteSlice_slice(v_xs_1057_, v___x_1062_, v___x_1060_);
        return v___x_1064_;
    } else {
        let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1062_);
        v___x_1065_ = l_ByteSlice_slice(v_xs_1057_, v___x_1059_, v___x_1060_);
        return v___x_1065_;
    }
}
pub unsafe fn l_instSliceableByteSliceNat__5___lam__0___boxed(
    mut v_xs_1066_: *mut LeanObject,
    mut v_range_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_instSliceableByteSliceNat__5___lam__0(v_xs_1066_, v_range_1067_);
    lean_dec(v_range_1067_);
    lean_dec_ref(v_xs_1066_);
    return v_res_1068_;
}
pub unsafe fn l_instSliceableByteSliceNat__6___lam__0(
    mut v_xs_1071_: *mut LeanObject,
    mut v_range_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    v___x_1073_ = lean_unsigned_to_nat(0);
    v___x_1074_ = l_ByteSlice_size(v_xs_1071_);
    v___x_1075_ = lean_unsigned_to_nat(1);
    v___x_1076_ = lean_nat_add(v_range_1072_, v___x_1075_);
    v___x_1077_ = lean_nat_dec_le(v___x_1076_, v___x_1074_);
    if v___x_1077_ == 0 {
        let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1076_);
        v___x_1078_ = l_ByteSlice_slice(v_xs_1071_, v___x_1073_, v___x_1074_);
        return v___x_1078_;
    } else {
        let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1074_);
        v___x_1079_ = l_ByteSlice_slice(v_xs_1071_, v___x_1073_, v___x_1076_);
        return v___x_1079_;
    }
}
pub unsafe fn l_instSliceableByteSliceNat__6___lam__0___boxed(
    mut v_xs_1080_: *mut LeanObject,
    mut v_range_1081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1082_: *mut LeanObject = core::ptr::null_mut();
    v_res_1082_ = l_instSliceableByteSliceNat__6___lam__0(v_xs_1080_, v_range_1081_);
    lean_dec(v_range_1081_);
    lean_dec_ref(v_xs_1080_);
    return v_res_1082_;
}
pub unsafe fn l_instSliceableByteSliceNat__7___lam__0(
    mut v_xs_1085_: *mut LeanObject,
    mut v_range_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    v___x_1087_ = lean_unsigned_to_nat(0);
    v___x_1088_ = l_ByteSlice_size(v_xs_1085_);
    v___x_1089_ = lean_nat_dec_le(v_range_1086_, v___x_1088_);
    if v___x_1089_ == 0 {
        let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_range_1086_);
        v___x_1090_ = l_ByteSlice_slice(v_xs_1085_, v___x_1087_, v___x_1088_);
        return v___x_1090_;
    } else {
        let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1088_);
        v___x_1091_ = l_ByteSlice_slice(v_xs_1085_, v___x_1087_, v_range_1086_);
        return v___x_1091_;
    }
}
pub unsafe fn l_instSliceableByteSliceNat__7___lam__0___boxed(
    mut v_xs_1092_: *mut LeanObject,
    mut v_range_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1094_: *mut LeanObject = core::ptr::null_mut();
    v_res_1094_ = l_instSliceableByteSliceNat__7___lam__0(v_xs_1092_, v_range_1093_);
    lean_dec_ref(v_xs_1092_);
    return v_res_1094_;
}
pub unsafe fn l_instSliceableByteSliceNat__8___lam__0(
    mut v_xs_1097_: *mut LeanObject,
    mut v_x_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1099_ = lean_unsigned_to_nat(0);
    v___x_1100_ = l_ByteSlice_size(v_xs_1097_);
    v___x_1101_ = l_ByteSlice_slice(v_xs_1097_, v___x_1099_, v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_instSliceableByteSliceNat__8___lam__0___boxed(
    mut v_xs_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1104_: *mut LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_instSliceableByteSliceNat__8___lam__0(v_xs_1102_, v_x_1103_);
    lean_dec_ref(v_xs_1102_);
    return v_res_1104_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ByteSlice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ByteSlice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ByteSlice(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ByteSlice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_ByteSlice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_ByteSlice(builtin);
}
