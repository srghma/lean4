// Lean compiler output
// Module: Init.Data.Format.Basic
// Imports: Init.Data.Int.Basic Init.Data.String.Bootstrap Init.Control.State Init.Data.Nat.Bitwise.Basic
use crate::ffi::{
    lean_int_add, lean_int_dec_lt, lean_int_sub, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_string_append,
    lean_string_dec_eq, lean_string_length, lean_string_offsetofpos, lean_string_posof,
    lean_string_pushn, lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_next,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, l_StateT_bind, l_StateT_get,
    l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Data::Int::Basic::{
    initialize_Init_Data_Int_Basic, l_Int_toNat, runtime_initialize_Init_Data_Int_Basic,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::String::Bootstrap::{
    initialize_Init_Data_String_Bootstrap, runtime_initialize_Init_Data_String_Bootstrap,
};
use crate::r#gen::Init::Prelude::{
    l_List_foldl___redArg, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
pub static mut l_Std_Format_instInhabitedFlattenBehavior_default: u8 = 0;
pub static mut l_Std_Format_instInhabitedFlattenBehavior: u8 = 0;
pub static l_Std_Format_instBEqFlattenBehavior___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Format_instBEqFlattenBehavior_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Format_instBEqFlattenBehavior___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenBehavior___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_instBEqFlattenBehavior: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenBehavior___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_instInhabitedFormat_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_instInhabitedFormat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Format_isEmpty___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Std_Format_isEmpty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_isEmpty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_instAppend___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Format_instAppend___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Format_instAppend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_instAppend: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_instCoeString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Format_instCoeString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Format_instCoeString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instCoeString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_instCoeString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instCoeString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Format_join___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Std_Format_isEmpty___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Format_join___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_join___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_instInhabitedSpaceResult_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Format_instInhabitedSpaceResult_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_instInhabitedSpaceResult_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_instBEqFlattenAllowability___closed__0_value:
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
    m_fun: l_Std_Format_instBEqFlattenAllowability_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Format_instBEqFlattenAllowability___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenAllowability___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_instBEqFlattenAllowability: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenAllowability___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value:
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
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Format_paren___closed__0_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Std_Format_paren___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_paren___closed__1_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Std_Format_paren___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Format_paren___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Format_paren___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Format_paren___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Format_paren___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Format_paren___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Std_Format_paren___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Format_paren___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_paren___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Std_Format_paren___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Format_paren___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_sbracket___closed__0_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Std_Format_sbracket___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_sbracket___closed__1_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Std_Format_sbracket___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Format_sbracket___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Format_sbracket___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Format_sbracket___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Format_sbracket___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Format_sbracket___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Std_Format_sbracket___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Format_sbracket___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Format_sbracket___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Std_Format_sbracket___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Format_sbracket___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Format_defIndent: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Format_defUnicode: u8 = 0;
pub static mut l_Std_Format_defWidth: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Format_nestD___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Format_nestD___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_get as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value: crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 7, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_map as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_pure as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_instToFormatFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_instToFormatFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_instToFormatFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_instToFormatString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instToFormatString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToFormatString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_instToFormatString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Format_FlattenBehavior_ctorIdx(
    mut v_x_1608_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_1608_ == 0 {
        let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1609_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1609_;
    } else {
        let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1610_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1610_;
    }
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorIdx___boxed(
    mut v_x_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1612_: u8 = 0;
    let mut v_res_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1612_ = (crate::leanh::lean_unbox(v_x_1611_) as u8);
    v_res_1613_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_boxed_1612_);
    return v_res_1613_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_toCtorIdx(
    mut v_x_1614_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_toCtorIdx___boxed(
    mut v_x_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1617_ = (crate::leanh::lean_unbox(v_x_1616_) as u8);
    v_res_1618_ = l_Std_Format_FlattenBehavior_toCtorIdx(v_x_4__boxed_1617_);
    return v_res_1618_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___redArg(
    mut v_k_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1619_);
    return v_k_1619_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(
    mut v_k_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Std_Format_FlattenBehavior_ctorElim___redArg(v_k_1620_);
    crate::leanh::lean_dec(v_k_1620_);
    return v_res_1621_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim(
    mut v_motive_1622_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1623_: *mut crate::leanh::LeanObject,
    mut v_t_1624_: u8,
    mut v_h_1625_: *mut crate::leanh::LeanObject,
    mut v_k_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1626_);
    return v_k_1626_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___boxed(
    mut v_motive_1627_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1628_: *mut crate::leanh::LeanObject,
    mut v_t_1629_: *mut crate::leanh::LeanObject,
    mut v_h_1630_: *mut crate::leanh::LeanObject,
    mut v_k_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1632_ = (crate::leanh::lean_unbox(v_t_1629_) as u8);
    v_res_1633_ = l_Std_Format_FlattenBehavior_ctorElim(
        v_motive_1627_,
        v_ctorIdx_1628_,
        v_t_boxed_1632_,
        v_h_1630_,
        v_k_1631_,
    );
    crate::leanh::lean_dec(v_k_1631_);
    crate::leanh::lean_dec(v_ctorIdx_1628_);
    return v_res_1633_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(
    mut v_allOrNone_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_allOrNone_1634_);
    return v_allOrNone_1634_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(
    mut v_allOrNone_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(v_allOrNone_1635_);
    crate::leanh::lean_dec(v_allOrNone_1635_);
    return v_res_1636_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim(
    mut v_motive_1637_: *mut crate::leanh::LeanObject,
    mut v_t_1638_: u8,
    mut v_h_1639_: *mut crate::leanh::LeanObject,
    mut v_allOrNone_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_allOrNone_1640_);
    return v_allOrNone_1640_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(
    mut v_motive_1641_: *mut crate::leanh::LeanObject,
    mut v_t_1642_: *mut crate::leanh::LeanObject,
    mut v_h_1643_: *mut crate::leanh::LeanObject,
    mut v_allOrNone_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1645_ = (crate::leanh::lean_unbox(v_t_1642_) as u8);
    v_res_1646_ = l_Std_Format_FlattenBehavior_allOrNone_elim(
        v_motive_1641_,
        v_t_boxed_1645_,
        v_h_1643_,
        v_allOrNone_1644_,
    );
    crate::leanh::lean_dec(v_allOrNone_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___redArg(
    mut v_fill_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_fill_1647_);
    return v_fill_1647_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(
    mut v_fill_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Std_Format_FlattenBehavior_fill_elim___redArg(v_fill_1648_);
    crate::leanh::lean_dec(v_fill_1648_);
    return v_res_1649_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim(
    mut v_motive_1650_: *mut crate::leanh::LeanObject,
    mut v_t_1651_: u8,
    mut v_h_1652_: *mut crate::leanh::LeanObject,
    mut v_fill_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_fill_1653_);
    return v_fill_1653_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___boxed(
    mut v_motive_1654_: *mut crate::leanh::LeanObject,
    mut v_t_1655_: *mut crate::leanh::LeanObject,
    mut v_h_1656_: *mut crate::leanh::LeanObject,
    mut v_fill_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1658_: u8 = 0;
    let mut v_res_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1658_ = (crate::leanh::lean_unbox(v_t_1655_) as u8);
    v_res_1659_ = l_Std_Format_FlattenBehavior_fill_elim(
        v_motive_1654_,
        v_t_boxed_1658_,
        v_h_1656_,
        v_fill_1657_,
    );
    crate::leanh::lean_dec(v_fill_1657_);
    return v_res_1659_;
}
pub unsafe fn _init_l_Std_Format_instInhabitedFlattenBehavior_default() -> u8 {
    let mut v___x_1660_: u8 = 0;
    v___x_1660_ = 0;
    return v___x_1660_;
}
pub unsafe fn _init_l_Std_Format_instInhabitedFlattenBehavior() -> u8 {
    let mut v___x_1661_: u8 = 0;
    v___x_1661_ = 0;
    return v___x_1661_;
}
pub unsafe fn l_Std_Format_instBEqFlattenBehavior_beq(mut v_x_1662_: u8, mut v_y_1663_: u8) -> u8 {
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    v___x_1664_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_1662_);
    v___x_1665_ = l_Std_Format_FlattenBehavior_ctorIdx(v_y_1663_);
    v___x_1666_ = lean_nat_dec_eq(v___x_1664_, v___x_1665_);
    crate::leanh::lean_dec(v___x_1665_);
    crate::leanh::lean_dec(v___x_1664_);
    return v___x_1666_;
}
pub unsafe fn l_Std_Format_instBEqFlattenBehavior_beq___boxed(
    mut v_x_1667_: *mut crate::leanh::LeanObject,
    mut v_y_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1669_: u8 = 0;
    let mut v_y_18__boxed_1670_: u8 = 0;
    let mut v_res_1671_: u8 = 0;
    let mut v_r_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1669_ = (crate::leanh::lean_unbox(v_x_1667_) as u8);
    v_y_18__boxed_1670_ = (crate::leanh::lean_unbox(v_y_1668_) as u8);
    v_res_1671_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_17__boxed_1669_, v_y_18__boxed_1670_);
    v_r_1672_ = crate::leanh::lean_box((v_res_1671_) as usize);
    return v_r_1672_;
}
pub unsafe fn l_Std_Format_ctorIdx(
    mut v_x_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1675_) {
        0 => {
            let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1676_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1676_;
        }
        1 => {
            let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1677_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1677_;
        }
        2 => {
            let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1678_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1678_;
        }
        3 => {
            let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1679_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1679_;
        }
        4 => {
            let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1680_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1680_;
        }
        5 => {
            let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1681_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1681_;
        }
        6 => {
            let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1682_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1682_;
        }
        _ => {
            let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1683_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1683_;
        }
    }
}
pub unsafe fn l_Std_Format_ctorIdx___boxed(
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Std_Format_ctorIdx(v_x_1684_);
    crate::leanh::lean_dec(v_x_1684_);
    return v_res_1685_;
}
pub unsafe fn l_Std_Format_ctorElim___redArg(
    mut v_t_1686_: *mut crate::leanh::LeanObject,
    mut v_k_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1686_) {
        2 => {
            let mut v_force_1688_: u8 = 0;
            let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_force_1688_ = crate::leanh::lean_ctor_get_uint8(v_t_1686_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_t_1686_, 0);
            v___x_1689_ = crate::leanh::lean_box((v_force_1688_) as usize);
            v___x_1690_ = crate::leanh::lean_apply_1(v_k_1687_, v___x_1689_);
            return v___x_1690_;
        }
        3 => {
            let mut v_a_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1691_ = crate::leanh::lean_ctor_get(v_t_1686_, 0);
            crate::leanh::lean_inc_ref(v_a_1691_);
            crate::leanh::lean_dec_ref_known(v_t_1686_, 1);
            v___x_1692_ = crate::leanh::lean_apply_1(v_k_1687_, v_a_1691_);
            return v___x_1692_;
        }
        4 => {
            let mut v_indent_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_f_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_indent_1693_ = crate::leanh::lean_ctor_get(v_t_1686_, 0);
            crate::leanh::lean_inc(v_indent_1693_);
            v_f_1694_ = crate::leanh::lean_ctor_get(v_t_1686_, 1);
            crate::leanh::lean_inc(v_f_1694_);
            crate::leanh::lean_dec_ref_known(v_t_1686_, 2);
            v___x_1695_ = crate::leanh::lean_apply_2(v_k_1687_, v_indent_1693_, v_f_1694_);
            return v___x_1695_;
        }
        5 => {
            let mut v_a_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1696_ = crate::leanh::lean_ctor_get(v_t_1686_, 0);
            crate::leanh::lean_inc(v_a_1696_);
            v_a_1697_ = crate::leanh::lean_ctor_get(v_t_1686_, 1);
            crate::leanh::lean_inc(v_a_1697_);
            crate::leanh::lean_dec_ref_known(v_t_1686_, 2);
            v___x_1698_ = crate::leanh::lean_apply_2(v_k_1687_, v_a_1696_, v_a_1697_);
            return v___x_1698_;
        }
        6 => {
            let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_behavior_1700_: u8 = 0;
            let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1699_ = crate::leanh::lean_ctor_get(v_t_1686_, 0);
            crate::leanh::lean_inc(v_a_1699_);
            v_behavior_1700_ = crate::leanh::lean_ctor_get_uint8(
                v_t_1686_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_t_1686_, 1);
            v___x_1701_ = crate::leanh::lean_box((v_behavior_1700_) as usize);
            v___x_1702_ = crate::leanh::lean_apply_2(v_k_1687_, v_a_1699_, v___x_1701_);
            return v___x_1702_;
        }
        7 => {
            let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1703_ = crate::leanh::lean_ctor_get(v_t_1686_, 0);
            crate::leanh::lean_inc(v_a_1703_);
            v_a_1704_ = crate::leanh::lean_ctor_get(v_t_1686_, 1);
            crate::leanh::lean_inc(v_a_1704_);
            crate::leanh::lean_dec_ref_known(v_t_1686_, 2);
            v___x_1705_ = crate::leanh::lean_apply_2(v_k_1687_, v_a_1703_, v_a_1704_);
            return v___x_1705_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_1686_);
            return v_k_1687_;
        }
    }
}
pub unsafe fn l_Std_Format_ctorElim(
    mut v_motive_1706_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1707_: *mut crate::leanh::LeanObject,
    mut v_t_1708_: *mut crate::leanh::LeanObject,
    mut v_h_1709_: *mut crate::leanh::LeanObject,
    mut v_k_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_Format_ctorElim___redArg(v_t_1708_, v_k_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Format_ctorElim___boxed(
    mut v_motive_1712_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1713_: *mut crate::leanh::LeanObject,
    mut v_t_1714_: *mut crate::leanh::LeanObject,
    mut v_h_1715_: *mut crate::leanh::LeanObject,
    mut v_k_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Std_Format_ctorElim(
        v_motive_1712_,
        v_ctorIdx_1713_,
        v_t_1714_,
        v_h_1715_,
        v_k_1716_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1713_);
    return v_res_1717_;
}
pub unsafe fn l_Std_Format_nil_elim___redArg(
    mut v_t_1718_: *mut crate::leanh::LeanObject,
    mut v_nil_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Std_Format_ctorElim___redArg(v_t_1718_, v_nil_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Std_Format_nil_elim(
    mut v_motive_1721_: *mut crate::leanh::LeanObject,
    mut v_t_1722_: *mut crate::leanh::LeanObject,
    mut v_h_1723_: *mut crate::leanh::LeanObject,
    mut v_nil_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = l_Std_Format_ctorElim___redArg(v_t_1722_, v_nil_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_Format_line_elim___redArg(
    mut v_t_1726_: *mut crate::leanh::LeanObject,
    mut v_line_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Std_Format_ctorElim___redArg(v_t_1726_, v_line_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Std_Format_line_elim(
    mut v_motive_1729_: *mut crate::leanh::LeanObject,
    mut v_t_1730_: *mut crate::leanh::LeanObject,
    mut v_h_1731_: *mut crate::leanh::LeanObject,
    mut v_line_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Std_Format_ctorElim___redArg(v_t_1730_, v_line_1732_);
    return v___x_1733_;
}
pub unsafe fn l_Std_Format_align_elim___redArg(
    mut v_t_1734_: *mut crate::leanh::LeanObject,
    mut v_align_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = l_Std_Format_ctorElim___redArg(v_t_1734_, v_align_1735_);
    return v___x_1736_;
}
pub unsafe fn l_Std_Format_align_elim(
    mut v_motive_1737_: *mut crate::leanh::LeanObject,
    mut v_t_1738_: *mut crate::leanh::LeanObject,
    mut v_h_1739_: *mut crate::leanh::LeanObject,
    mut v_align_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Std_Format_ctorElim___redArg(v_t_1738_, v_align_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Format_text_elim___redArg(
    mut v_t_1742_: *mut crate::leanh::LeanObject,
    mut v_text_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Std_Format_ctorElim___redArg(v_t_1742_, v_text_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_Format_text_elim(
    mut v_motive_1745_: *mut crate::leanh::LeanObject,
    mut v_t_1746_: *mut crate::leanh::LeanObject,
    mut v_h_1747_: *mut crate::leanh::LeanObject,
    mut v_text_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = l_Std_Format_ctorElim___redArg(v_t_1746_, v_text_1748_);
    return v___x_1749_;
}
pub unsafe fn l_Std_Format_nest_elim___redArg(
    mut v_t_1750_: *mut crate::leanh::LeanObject,
    mut v_nest_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = l_Std_Format_ctorElim___redArg(v_t_1750_, v_nest_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Std_Format_nest_elim(
    mut v_motive_1753_: *mut crate::leanh::LeanObject,
    mut v_t_1754_: *mut crate::leanh::LeanObject,
    mut v_h_1755_: *mut crate::leanh::LeanObject,
    mut v_nest_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Std_Format_ctorElim___redArg(v_t_1754_, v_nest_1756_);
    return v___x_1757_;
}
pub unsafe fn l_Std_Format_append_elim___redArg(
    mut v_t_1758_: *mut crate::leanh::LeanObject,
    mut v_append_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = l_Std_Format_ctorElim___redArg(v_t_1758_, v_append_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Std_Format_append_elim(
    mut v_motive_1761_: *mut crate::leanh::LeanObject,
    mut v_t_1762_: *mut crate::leanh::LeanObject,
    mut v_h_1763_: *mut crate::leanh::LeanObject,
    mut v_append_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Std_Format_ctorElim___redArg(v_t_1762_, v_append_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_Format_group_elim___redArg(
    mut v_t_1766_: *mut crate::leanh::LeanObject,
    mut v_group_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_Format_ctorElim___redArg(v_t_1766_, v_group_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Std_Format_group_elim(
    mut v_motive_1769_: *mut crate::leanh::LeanObject,
    mut v_t_1770_: *mut crate::leanh::LeanObject,
    mut v_h_1771_: *mut crate::leanh::LeanObject,
    mut v_group_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Std_Format_ctorElim___redArg(v_t_1770_, v_group_1772_);
    return v___x_1773_;
}
pub unsafe fn l_Std_Format_tag_elim___redArg(
    mut v_t_1774_: *mut crate::leanh::LeanObject,
    mut v_tag_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = l_Std_Format_ctorElim___redArg(v_t_1774_, v_tag_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Std_Format_tag_elim(
    mut v_motive_1777_: *mut crate::leanh::LeanObject,
    mut v_t_1778_: *mut crate::leanh::LeanObject,
    mut v_h_1779_: *mut crate::leanh::LeanObject,
    mut v_tag_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Std_Format_ctorElim___redArg(v_t_1778_, v_tag_1780_);
    return v___x_1781_;
}
pub unsafe fn _init_l_Std_instInhabitedFormat_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = crate::leanh::lean_box(0);
    return v___x_1782_;
}
pub unsafe fn _init_l_Std_instInhabitedFormat() -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = crate::leanh::lean_box(0);
    return v___x_1783_;
}
pub unsafe fn l_Std_Format_isEmpty(mut v_x_1785_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1786_: u8 = 0;
    let mut v_a_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v_f_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v_a_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1785_) {
                1 => {
                    v___x_1786_ = 0;
                    return v___x_1786_;
                }
                3 => {
                    v_a_1787_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    v___x_1788_ = l_Std_Format_isEmpty___closed__0;
                    v___x_1789_ = lean_string_dec_eq(v_a_1787_, v___x_1788_);
                    return v___x_1789_;
                }
                4 => {
                    v_f_1790_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    v_x_1785_ = v_f_1790_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_1792_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    v_a_1793_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    v___x_1794_ = l_Std_Format_isEmpty(v_a_1792_);
                    if v___x_1794_ == 0 {
                        return v___x_1794_;
                    } else {
                        v_x_1785_ = v_a_1793_;
                        state = 0;
                        continue;
                    }
                }
                6 => {
                    v_a_1796_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    v_x_1785_ = v_a_1796_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_a_1798_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    v_x_1785_ = v_a_1798_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_1800_ = 1;
                    return v___x_1800_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_isEmpty___boxed(
    mut v_x_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: u8 = 0;
    let mut v_r_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Std_Format_isEmpty(v_x_1801_);
    crate::leanh::lean_dec(v_x_1801_);
    v_r_1803_ = crate::leanh::lean_box((v_res_1802_) as usize);
    return v_r_1803_;
}
pub unsafe fn l_Std_Format_fill(
    mut v_f_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = 1;
    v___x_1806_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1806_, 0, v_f_1804_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1806_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1805_,
    );
    return v___x_1806_;
}
pub unsafe fn l_Std_Format_instAppend___lam__0(
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1809_, 0, v_a_1807_);
    crate::leanh::lean_ctor_set(v___x_1809_, 1, v_a_1808_);
    return v___x_1809_;
}
pub unsafe fn l_Std_Format_instCoeString___lam__0(
    mut v_a_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v_a_1812_);
    return v___x_1813_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_join_spec__0(
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v_x_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1817_) == 0 {
                    return v_x_1816_;
                } else {
                    v_head_1818_ = crate::leanh::lean_ctor_get(v_x_1817_, 0);
                    v_tail_1819_ = crate::leanh::lean_ctor_get(v_x_1817_, 1);
                    v_isSharedCheck_1827_ = (!crate::leanh::lean_is_exclusive(v_x_1817_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1821_ = v_x_1817_;
                        v_isShared_1822_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1819_);
                        crate::leanh::lean_inc(v_head_1818_);
                        crate::leanh::lean_dec(v_x_1817_);
                        v___x_1821_ = crate::leanh::lean_box(0);
                        v_isShared_1822_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1822_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1821_, 5);
                    crate::leanh::lean_ctor_set(v___x_1821_, 1, v_head_1818_);
                    crate::leanh::lean_ctor_set(v___x_1821_, 0, v_x_1816_);
                    v___x_1824_ = v___x_1821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_x_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_head_1818_);
                    v___x_1824_ = v_reuseFailAlloc_1826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_1816_ = v___x_1824_;
                v_x_1817_ = v_tail_1819_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_join(
    mut v_xs_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = l_Std_Format_join___closed__0;
    v___x_1832_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_1831_, v_xs_1830_);
    return v___x_1832_;
}
pub unsafe fn l_Std_Format_isNil(mut v_x_1833_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1833_) == 0 {
        let mut v___x_1834_: u8 = 0;
        v___x_1834_ = 1;
        return v___x_1834_;
    } else {
        let mut v___x_1835_: u8 = 0;
        v___x_1835_ = 0;
        return v___x_1835_;
    }
}
pub unsafe fn l_Std_Format_isNil___boxed(
    mut v_x_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1837_: u8 = 0;
    let mut v_r_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Std_Format_isNil(v_x_1836_);
    crate::leanh::lean_dec(v_x_1836_);
    v_r_1838_ = crate::leanh::lean_box((v_res_1837_) as usize);
    return v_r_1838_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_merge(
    mut v_w_1844_: *mut crate::leanh::LeanObject,
    mut v_r_u2081_1845_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_foundLine_1847_: u8 = 0;
    let mut v_space_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1853_: u8 = 0;
    let mut v_foundFlattenedHardLine_1854_: u8 = 0;
    let mut v_space_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_foundLine_1847_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_u2081_1845_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_space_1848_ = crate::leanh::lean_ctor_get(v_r_u2081_1845_, 0);
                v___x_1864_ = lean_nat_dec_lt(v_w_1844_, v_space_1848_);
                if v___x_1864_ == 0 {
                    v___y_1850_ = v_foundLine_1847_;
                    state = 1;
                    continue;
                } else {
                    v___y_1850_ = v___x_1864_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1850_ == 0 {
                    v___x_1851_ = lean_nat_sub(v_w_1844_, v_space_1848_);
                    v_r_u2082_1852_ = crate::leanh::lean_apply_1(v_r_u2082_1846_, v___x_1851_);
                    v_foundLine_1853_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_1852_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_1854_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_1852_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_1855_ = crate::leanh::lean_ctor_get(v_r_u2082_1852_, 0);
                    v_isSharedCheck_1863_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_1852_)) as u8;
                    if v_isSharedCheck_1863_ == 0 {
                        v___x_1857_ = v_r_u2082_1852_;
                        v_isShared_1858_ = v_isSharedCheck_1863_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_1855_);
                        crate::leanh::lean_dec(v_r_u2082_1852_);
                        v___x_1857_ = crate::leanh::lean_box(0);
                        v_isShared_1858_ = v_isSharedCheck_1863_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_r_u2082_1846_);
                    crate::leanh::lean_inc_ref(v_r_u2081_1845_);
                    return v_r_u2081_1845_;
                }
            }
            2 => {
                v___x_1859_ = lean_nat_add(v_space_1848_, v_space_1855_);
                crate::leanh::lean_dec(v_space_1855_);
                if v_isShared_1858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1859_);
                    v___x_1861_ = v___x_1857_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1862_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_1853_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1862_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_1854_,
                    );
                    v___x_1861_ = v_reuseFailAlloc_1862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(
    mut v_w_1865_: *mut crate::leanh::LeanObject,
    mut v_r_u2081_1866_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(
        v_w_1865_,
        v_r_u2081_1866_,
        v_r_u2082_1867_,
    );
    crate::leanh::lean_dec_ref(v_r_u2081_1866_);
    crate::leanh::lean_dec(v_w_1865_);
    return v_res_1868_;
}
pub unsafe fn l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(
    mut v_a_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_nat_to_int(v_a_1869_);
    return v___x_1870_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
    mut v_x_1874_: *mut crate::leanh::LeanObject,
    mut v_x_1875_: u8,
    mut v_x_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: u8 = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_force_1893_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u32 = 0;
    let mut v_p_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_off_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: u8 = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: u8 = 0;
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: u8 = 0;
    let mut v_indent_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1916_: u8 = 0;
    let mut v_space_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1922_: u8 = 0;
    let mut v_foundFlattenedHardLine_1923_: u8 = 0;
    let mut v_space_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v___x_1933_: u8 = 0;
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1874_) {
                0 => {
                    crate::leanh::lean_dec(v_x_1877_);
                    crate::leanh::lean_dec(v_x_1876_);
                    v___x_1888_ = l_Std_Format_instInhabitedSpaceResult_default___closed__0;
                    return v___x_1888_;
                }
                1 => {
                    crate::leanh::lean_dec(v_x_1877_);
                    crate::leanh::lean_dec(v_x_1876_);
                    if v_x_1875_ == 0 {
                        v___x_1889_ = 1;
                        v___x_1890_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1890_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1891_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1889_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1891_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                            v_x_1875_,
                        );
                        return v___x_1891_;
                    } else {
                        v___x_1892_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0;
                        return v___x_1892_;
                    }
                }
                2 => {
                    if v_x_1875_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_1874_, 0);
                        v___y_1879_ = v_x_1875_;
                        state = 1;
                        continue;
                    } else {
                        v_force_1893_ = crate::leanh::lean_ctor_get_uint8(v_x_1874_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_x_1874_, 0);
                        if v_force_1893_ == 0 {
                            crate::leanh::lean_dec(v_x_1877_);
                            crate::leanh::lean_dec(v_x_1876_);
                            v___x_1894_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                            crate::leanh::lean_ctor_set(v___x_1895_, 0, v___x_1894_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1895_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v_force_1893_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1895_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1)
                                    as u32,
                                v_force_1893_,
                            );
                            return v___x_1895_;
                        } else {
                            v___x_1896_ = 0;
                            v___y_1879_ = v___x_1896_;
                            state = 1;
                            continue;
                        }
                    }
                }
                3 => {
                    crate::leanh::lean_dec(v_x_1877_);
                    crate::leanh::lean_dec(v_x_1876_);
                    v_a_1897_ = crate::leanh::lean_ctor_get(v_x_1874_, 0);
                    crate::leanh::lean_inc_ref_n(v_a_1897_, 3);
                    crate::leanh::lean_dec_ref_known(v_x_1874_, 1);
                    v___x_1898_ = 10;
                    v_p_1899_ = lean_string_posof(v_a_1897_, v___x_1898_);
                    crate::leanh::lean_inc(v_p_1899_);
                    v_off_1900_ = lean_string_offsetofpos(v_a_1897_, v_p_1899_);
                    v___x_1905_ = lean_string_utf8_byte_size(v_a_1897_);
                    crate::leanh::lean_dec_ref(v_a_1897_);
                    v___x_1906_ = lean_nat_dec_eq(v_p_1899_, v___x_1905_);
                    crate::leanh::lean_dec(v_p_1899_);
                    if v___x_1906_ == 0 {
                        v___x_1907_ = 1;
                        v___y_1902_ = v___x_1907_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1908_ = 0;
                        v___y_1902_ = v___x_1908_;
                        state = 2;
                        continue;
                    }
                }
                4 => {
                    v_indent_1909_ = crate::leanh::lean_ctor_get(v_x_1874_, 0);
                    crate::leanh::lean_inc(v_indent_1909_);
                    v_f_1910_ = crate::leanh::lean_ctor_get(v_x_1874_, 1);
                    crate::leanh::lean_inc(v_f_1910_);
                    crate::leanh::lean_dec_ref_known(v_x_1874_, 2);
                    v___x_1911_ = lean_int_sub(v_x_1876_, v_indent_1909_);
                    crate::leanh::lean_dec(v_indent_1909_);
                    crate::leanh::lean_dec(v_x_1876_);
                    v_x_1874_ = v_f_1910_;
                    v_x_1876_ = v___x_1911_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_1913_ = crate::leanh::lean_ctor_get(v_x_1874_, 0);
                    crate::leanh::lean_inc(v_a_1913_);
                    v_a_1914_ = crate::leanh::lean_ctor_get(v_x_1874_, 1);
                    crate::leanh::lean_inc(v_a_1914_);
                    crate::leanh::lean_dec_ref_known(v_x_1874_, 2);
                    crate::leanh::lean_inc(v_x_1877_);
                    crate::leanh::lean_inc(v_x_1876_);
                    v___x_1915_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                        v_a_1913_, v_x_1875_, v_x_1876_, v_x_1877_,
                    );
                    v_foundLine_1916_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1915_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_space_1917_ = crate::leanh::lean_ctor_get(v___x_1915_, 0);
                    crate::leanh::lean_inc(v_space_1917_);
                    v___x_1933_ = lean_nat_dec_lt(v_x_1877_, v_space_1917_);
                    if v___x_1933_ == 0 {
                        v___y_1919_ = v_foundLine_1916_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1919_ = v___x_1933_;
                        state = 3;
                        continue;
                    }
                }
                6 => {
                    v_a_1934_ = crate::leanh::lean_ctor_get(v_x_1874_, 0);
                    crate::leanh::lean_inc(v_a_1934_);
                    crate::leanh::lean_dec_ref_known(v_x_1874_, 1);
                    v___x_1935_ = 1;
                    v_x_1874_ = v_a_1934_;
                    v_x_1875_ = v___x_1935_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1937_ = crate::leanh::lean_ctor_get(v_x_1874_, 1);
                    crate::leanh::lean_inc(v_a_1937_);
                    crate::leanh::lean_dec_ref_known(v_x_1874_, 2);
                    v_x_1874_ = v_a_1937_;
                    state = 0;
                    continue;
                }
            },
            1 => {
                v___x_1880_ = lean_nat_to_int(v_x_1877_);
                v___x_1881_ = lean_int_dec_lt(v___x_1880_, v_x_1876_);
                if v___x_1881_ == 0 {
                    crate::leanh::lean_dec(v___x_1880_);
                    crate::leanh::lean_dec(v_x_1876_);
                    v___x_1882_ = 1;
                    v___x_1883_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1884_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1882_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1884_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v___y_1879_,
                    );
                    return v___x_1884_;
                } else {
                    v___x_1885_ = lean_int_sub(v_x_1876_, v___x_1880_);
                    crate::leanh::lean_dec(v___x_1880_);
                    crate::leanh::lean_dec(v_x_1876_);
                    v___x_1886_ = l_Int_toNat(v___x_1885_);
                    crate::leanh::lean_dec(v___x_1885_);
                    v___x_1887_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1887_, 0, v___x_1886_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1887_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___y_1879_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1887_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v___y_1879_,
                    );
                    return v___x_1887_;
                }
            }
            2 => {
                if v_x_1875_ == 0 {
                    v___x_1903_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1903_, 0, v_off_1900_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1903_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___y_1902_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1903_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_x_1875_,
                    );
                    return v___x_1903_;
                } else {
                    v___x_1904_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1904_, 0, v_off_1900_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1904_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___y_1902_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1904_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v___y_1902_,
                    );
                    return v___x_1904_;
                }
            }
            3 => {
                if v___y_1919_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1915_);
                    v___x_1920_ = lean_nat_sub(v_x_1877_, v_space_1917_);
                    crate::leanh::lean_dec(v_x_1877_);
                    v_r_u2082_1921_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                            v_a_1914_,
                            v_x_1875_,
                            v_x_1876_,
                            v___x_1920_,
                        );
                    v_foundLine_1922_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_1921_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_1923_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_1921_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_1924_ = crate::leanh::lean_ctor_get(v_r_u2082_1921_, 0);
                    v_isSharedCheck_1932_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_1921_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v___x_1926_ = v_r_u2082_1921_;
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_1924_);
                        crate::leanh::lean_dec(v_r_u2082_1921_);
                        v___x_1926_ = crate::leanh::lean_box(0);
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_space_1917_);
                    crate::leanh::lean_dec(v_a_1914_);
                    crate::leanh::lean_dec(v_x_1877_);
                    crate::leanh::lean_dec(v_x_1876_);
                    return v___x_1915_;
                }
            }
            4 => {
                v___x_1928_ = lean_nat_add(v_space_1917_, v_space_1924_);
                crate::leanh::lean_dec(v_space_1924_);
                crate::leanh::lean_dec(v_space_1917_);
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1931_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_1922_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1931_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_1923_,
                    );
                    v___x_1930_ = v_reuseFailAlloc_1931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
    mut v_x_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_415__boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_415__boxed_1943_ = (crate::leanh::lean_unbox(v_x_1940_) as u8);
    v_res_1944_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
        v_x_1939_,
        v_x_415__boxed_1943_,
        v_x_1941_,
        v_x_1942_,
    );
    return v_res_1944_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorIdx(
    mut v_x_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1945_) == 0 {
        let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1946_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1946_;
    } else {
        let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1947_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1947_;
    }
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorIdx___boxed(
    mut v_x_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_1948_);
    crate::leanh::lean_dec(v_x_1948_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___redArg(
    mut v_t_1950_: *mut crate::leanh::LeanObject,
    mut v_k_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1950_) == 0 {
        let mut v_fits_1952_: u8 = 0;
        let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fits_1952_ = crate::leanh::lean_ctor_get_uint8(v_t_1950_, 0 as u32);
        v___x_1953_ = crate::leanh::lean_box((v_fits_1952_) as usize);
        v___x_1954_ = crate::leanh::lean_apply_1(v_k_1951_, v___x_1953_);
        return v___x_1954_;
    } else {
        return v_k_1951_;
    }
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(
    mut v_t_1955_: *mut crate::leanh::LeanObject,
    mut v_k_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1955_, v_k_1956_);
    crate::leanh::lean_dec(v_t_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim(
    mut v_motive_1958_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1959_: *mut crate::leanh::LeanObject,
    mut v_t_1960_: *mut crate::leanh::LeanObject,
    mut v_h_1961_: *mut crate::leanh::LeanObject,
    mut v_k_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1960_, v_k_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___boxed(
    mut v_motive_1964_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1965_: *mut crate::leanh::LeanObject,
    mut v_t_1966_: *mut crate::leanh::LeanObject,
    mut v_h_1967_: *mut crate::leanh::LeanObject,
    mut v_k_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Std_Format_FlattenAllowability_ctorElim(
        v_motive_1964_,
        v_ctorIdx_1965_,
        v_t_1966_,
        v_h_1967_,
        v_k_1968_,
    );
    crate::leanh::lean_dec(v_t_1966_);
    crate::leanh::lean_dec(v_ctorIdx_1965_);
    return v_res_1969_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___redArg(
    mut v_t_1970_: *mut crate::leanh::LeanObject,
    mut v_allow_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1970_, v_allow_1971_);
    return v___x_1972_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(
    mut v_t_1973_: *mut crate::leanh::LeanObject,
    mut v_allow_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_1973_, v_allow_1974_);
    crate::leanh::lean_dec(v_t_1973_);
    return v_res_1975_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim(
    mut v_motive_1976_: *mut crate::leanh::LeanObject,
    mut v_t_1977_: *mut crate::leanh::LeanObject,
    mut v_h_1978_: *mut crate::leanh::LeanObject,
    mut v_allow_1979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1977_, v_allow_1979_);
    return v___x_1980_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___boxed(
    mut v_motive_1981_: *mut crate::leanh::LeanObject,
    mut v_t_1982_: *mut crate::leanh::LeanObject,
    mut v_h_1983_: *mut crate::leanh::LeanObject,
    mut v_allow_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Std_Format_FlattenAllowability_allow_elim(
        v_motive_1981_,
        v_t_1982_,
        v_h_1983_,
        v_allow_1984_,
    );
    crate::leanh::lean_dec(v_t_1982_);
    return v_res_1985_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___redArg(
    mut v_t_1986_: *mut crate::leanh::LeanObject,
    mut v_disallow_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1986_, v_disallow_1987_);
    return v___x_1988_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(
    mut v_t_1989_: *mut crate::leanh::LeanObject,
    mut v_disallow_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1991_ =
        l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_1989_, v_disallow_1990_);
    crate::leanh::lean_dec(v_t_1989_);
    return v_res_1991_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim(
    mut v_motive_1992_: *mut crate::leanh::LeanObject,
    mut v_t_1993_: *mut crate::leanh::LeanObject,
    mut v_h_1994_: *mut crate::leanh::LeanObject,
    mut v_disallow_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1993_, v_disallow_1995_);
    return v___x_1996_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___boxed(
    mut v_motive_1997_: *mut crate::leanh::LeanObject,
    mut v_t_1998_: *mut crate::leanh::LeanObject,
    mut v_h_1999_: *mut crate::leanh::LeanObject,
    mut v_disallow_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Std_Format_FlattenAllowability_disallow_elim(
        v_motive_1997_,
        v_t_1998_,
        v_h_1999_,
        v_disallow_2000_,
    );
    crate::leanh::lean_dec(v_t_1998_);
    return v_res_2001_;
}
pub unsafe fn l_Std_Format_instBEqFlattenAllowability_beq(
    mut v_x_2002_: *mut crate::leanh::LeanObject,
    mut v_x_2003_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2002_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_2003_) == 0 {
            let mut v_fits_2004_: u8 = 0;
            v_fits_2004_ = crate::leanh::lean_ctor_get_uint8(v_x_2002_, 0 as u32);
            if v_fits_2004_ == 0 {
                let mut v_fits_2005_: u8 = 0;
                v_fits_2005_ = crate::leanh::lean_ctor_get_uint8(v_x_2003_, 0 as u32);
                if v_fits_2005_ == 0 {
                    let mut v___x_2006_: u8 = 0;
                    v___x_2006_ = 1;
                    return v___x_2006_;
                } else {
                    return v_fits_2004_;
                }
            } else {
                let mut v_fits_2007_: u8 = 0;
                v_fits_2007_ = crate::leanh::lean_ctor_get_uint8(v_x_2003_, 0 as u32);
                return v_fits_2007_;
            }
        } else {
            let mut v___x_2008_: u8 = 0;
            v___x_2008_ = 0;
            return v___x_2008_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_2003_) == 1 {
            let mut v___x_2009_: u8 = 0;
            v___x_2009_ = 1;
            return v___x_2009_;
        } else {
            let mut v___x_2010_: u8 = 0;
            v___x_2010_ = 0;
            return v___x_2010_;
        }
    }
}
pub unsafe fn l_Std_Format_instBEqFlattenAllowability_beq___boxed(
    mut v_x_2011_: *mut crate::leanh::LeanObject,
    mut v_x_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2013_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_2011_, v_x_2012_);
    crate::leanh::lean_dec(v_x_2012_);
    crate::leanh::lean_dec(v_x_2011_);
    v_r_2014_ = crate::leanh::lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_shouldFlatten(
    mut v_x_2017_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2017_) == 0 {
        let mut v_fits_2018_: u8 = 0;
        v_fits_2018_ = crate::leanh::lean_ctor_get_uint8(v_x_2017_, 0 as u32);
        if v_fits_2018_ == 1 {
            return v_fits_2018_;
        } else {
            let mut v___x_2019_: u8 = 0;
            v___x_2019_ = 0;
            return v___x_2019_;
        }
    } else {
        let mut v___x_2020_: u8 = 0;
        v___x_2020_ = 0;
        return v___x_2020_;
    }
}
pub unsafe fn l_Std_Format_FlattenAllowability_shouldFlatten___boxed(
    mut v_x_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2022_: u8 = 0;
    let mut v_r_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_2021_);
    crate::leanh::lean_dec(v_x_2021_);
    v_r_2023_ = crate::leanh::lean_box((v_res_2022_) as usize);
    return v_r_2023_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
    mut v_x_2024_: *mut crate::leanh::LeanObject,
    mut v_x_2025_: *mut crate::leanh::LeanObject,
    mut v_x_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fla_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flb_2035_: u8 = 0;
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v_tail_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v_f_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2051_: u8 = 0;
    let mut v_space_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2061_: u8 = 0;
    let mut v_foundFlattenedHardLine_2062_: u8 = 0;
    let mut v_space_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_unused_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2024_) == 0 {
                    crate::leanh::lean_dec(v_x_2026_);
                    crate::leanh::lean_dec(v_x_2025_);
                    v___x_2027_ = l_Std_Format_instInhabitedSpaceResult_default___closed__0;
                    return v___x_2027_;
                } else {
                    v_head_2028_ = crate::leanh::lean_ctor_get(v_x_2024_, 0);
                    crate::leanh::lean_inc(v_head_2028_);
                    v_items_2029_ = crate::leanh::lean_ctor_get(v_head_2028_, 1);
                    crate::leanh::lean_inc(v_items_2029_);
                    if crate::leanh::lean_obj_tag(v_items_2029_) == 0 {
                        crate::leanh::lean_dec(v_head_2028_);
                        v_tail_2030_ = crate::leanh::lean_ctor_get(v_x_2024_, 1);
                        crate::leanh::lean_inc(v_tail_2030_);
                        crate::leanh::lean_dec_ref_known(v_x_2024_, 2);
                        v_x_2024_ = v_tail_2030_;
                        state = 0;
                        continue;
                    } else {
                        v_head_2032_ = crate::leanh::lean_ctor_get(v_items_2029_, 0);
                        crate::leanh::lean_inc(v_head_2032_);
                        v_tail_2033_ = crate::leanh::lean_ctor_get(v_x_2024_, 1);
                        crate::leanh::lean_inc(v_tail_2033_);
                        crate::leanh::lean_dec_ref_known(v_x_2024_, 2);
                        v_fla_2034_ = crate::leanh::lean_ctor_get(v_head_2028_, 0);
                        v_flb_2035_ = crate::leanh::lean_ctor_get_uint8(
                            v_head_2028_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_2077_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2028_)) as u8;
                        if v_isSharedCheck_2077_ == 0 {
                            v_unused_2078_ = crate::leanh::lean_ctor_get(v_head_2028_, 1);
                            crate::leanh::lean_dec(v_unused_2078_);
                            v___x_2037_ = v_head_2028_;
                            v_isShared_2038_ = v_isSharedCheck_2077_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fla_2034_);
                            crate::leanh::lean_dec(v_head_2028_);
                            v___x_2037_ = crate::leanh::lean_box(0);
                            v_isShared_2038_ = v_isSharedCheck_2077_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_tail_2039_ = crate::leanh::lean_ctor_get(v_items_2029_, 1);
                v_isSharedCheck_2075_ = (!crate::leanh::lean_is_exclusive(v_items_2029_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v_unused_2076_ = crate::leanh::lean_ctor_get(v_items_2029_, 0);
                    crate::leanh::lean_dec(v_unused_2076_);
                    v___x_2041_ = v_items_2029_;
                    v_isShared_2042_ = v_isSharedCheck_2075_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_2039_);
                    crate::leanh::lean_dec(v_items_2029_);
                    v___x_2041_ = crate::leanh::lean_box(0);
                    v_isShared_2042_ = v_isSharedCheck_2075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2043_ = crate::leanh::lean_ctor_get(v_head_2032_, 0);
                crate::leanh::lean_inc(v_f_2043_);
                v_indent_2044_ = crate::leanh::lean_ctor_get(v_head_2032_, 1);
                crate::leanh::lean_inc(v_indent_2044_);
                crate::leanh::lean_dec(v_head_2032_);
                v___x_2045_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2034_);
                crate::leanh::lean_inc_n(v_x_2026_, 2);
                v___x_2046_ = lean_nat_to_int(v_x_2026_);
                crate::leanh::lean_inc(v_x_2025_);
                v___x_2047_ = lean_nat_to_int(v_x_2025_);
                v___x_2048_ = lean_int_add(v___x_2046_, v___x_2047_);
                crate::leanh::lean_dec(v___x_2047_);
                crate::leanh::lean_dec(v___x_2046_);
                v___x_2049_ = lean_int_sub(v___x_2048_, v_indent_2044_);
                crate::leanh::lean_dec(v_indent_2044_);
                crate::leanh::lean_dec(v___x_2048_);
                v___x_2050_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                    v_f_2043_,
                    v___x_2045_,
                    v___x_2049_,
                    v_x_2026_,
                );
                v_foundLine_2051_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2050_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_space_2052_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                crate::leanh::lean_inc(v_space_2052_);
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2037_, 1, v_tail_2039_);
                    v___x_2054_ = v___x_2037_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fla_2034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_tail_2039_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2074_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_flb_2035_,
                    );
                    v___x_2054_ = v_reuseFailAlloc_2074_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2041_, 1, v_tail_2033_);
                    crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2041_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_tail_2033_);
                    v___x_2056_ = v_reuseFailAlloc_2073_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2072_ = lean_nat_dec_lt(v_x_2026_, v_space_2052_);
                if v___x_2072_ == 0 {
                    v___y_2058_ = v_foundLine_2051_;
                    state = 5;
                    continue;
                } else {
                    v___y_2058_ = v___x_2072_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_2058_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2050_);
                    v___x_2059_ = lean_nat_sub(v_x_2026_, v_space_2052_);
                    crate::leanh::lean_dec(v_x_2026_);
                    v_r_u2082_2060_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v___x_2056_,
                            v_x_2025_,
                            v___x_2059_,
                        );
                    v_foundLine_2061_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2060_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2062_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2060_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2063_ = crate::leanh::lean_ctor_get(v_r_u2082_2060_, 0);
                    v_isSharedCheck_2071_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_2060_)) as u8;
                    if v_isSharedCheck_2071_ == 0 {
                        v___x_2065_ = v_r_u2082_2060_;
                        v_isShared_2066_ = v_isSharedCheck_2071_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_2063_);
                        crate::leanh::lean_dec(v_r_u2082_2060_);
                        v___x_2065_ = crate::leanh::lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2071_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2056_);
                    crate::leanh::lean_dec(v_space_2052_);
                    crate::leanh::lean_dec(v_x_2026_);
                    crate::leanh::lean_dec(v_x_2025_);
                    return v___x_2050_;
                }
            }
            6 => {
                v___x_2067_ = lean_nat_add(v_space_2052_, v_space_2063_);
                crate::leanh::lean_dec(v_space_2063_);
                crate::leanh::lean_dec(v_space_2052_);
                if v_isShared_2066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_2067_);
                    v___x_2069_ = v___x_2065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2070_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_2061_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2070_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_2062_,
                    );
                    v___x_2069_ = v_reuseFailAlloc_2070_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(
    mut v_flb_2079_: u8,
    mut v_items_2080_: *mut crate::leanh::LeanObject,
    mut v_w_2081_: *mut crate::leanh::LeanObject,
    mut v_gs_2082_: *mut crate::leanh::LeanObject,
    mut v_toPure_2083_: *mut crate::leanh::LeanObject,
    mut v_k_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2086_: u8 = 0;
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2101_: u8 = 0;
    let mut v_space_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2104_: u8 = 0;
    let mut v_foundLine_2105_: u8 = 0;
    let mut v_space_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2111_: u8 = 0;
    let mut v_foundFlattenedHardLine_2112_: u8 = 0;
    let mut v_space_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2091_ = 0;
                v___x_2092_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2079_, v___x_2091_);
                v___x_2093_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2093_, 0 as u32, v___x_2092_);
                crate::leanh::lean_inc(v_items_2080_);
                v_g_2094_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v_g_2094_, 0, v___x_2093_);
                crate::leanh::lean_ctor_set(v_g_2094_, 1, v_items_2080_);
                crate::leanh::lean_ctor_set_uint8(
                    v_g_2094_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2079_,
                );
                v___x_2095_ = crate::leanh::lean_box(0);
                v___x_2096_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2096_, 0, v_g_2094_);
                crate::leanh::lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                v___x_2097_ = lean_nat_sub(v_w_2081_, v_k_2084_);
                crate::leanh::lean_inc(v___x_2097_);
                crate::leanh::lean_inc(v_k_2084_);
                v_r_2098_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2096_,
                    v_k_2084_,
                    v___x_2097_,
                );
                v_foundLine_2105_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2098_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_space_2106_ = crate::leanh::lean_ctor_get(v_r_2098_, 0);
                crate::leanh::lean_inc(v_space_2106_);
                v___x_2122_ = lean_nat_dec_lt(v___x_2097_, v_space_2106_);
                if v___x_2122_ == 0 {
                    v___y_2108_ = v_foundLine_2105_;
                    state = 3;
                    continue;
                } else {
                    v___y_2108_ = v___x_2122_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_2087_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2087_, 0 as u32, v___y_2086_);
                v___x_2088_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                crate::leanh::lean_ctor_set(v___x_2088_, 1, v_items_2080_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2088_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2079_,
                );
                v___x_2089_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2088_);
                crate::leanh::lean_ctor_set(v___x_2089_, 1, v_gs_2082_);
                v___x_2090_ = crate::leanh::lean_apply_2(
                    v_toPure_2083_,
                    crate::leanh::lean_box(0),
                    v___x_2089_,
                );
                return v___x_2090_;
            }
            2 => {
                v_foundFlattenedHardLine_2101_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2098_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_r_2098_);
                if v_foundFlattenedHardLine_2101_ == 0 {
                    v_space_2102_ = crate::leanh::lean_ctor_get(v___y_2100_, 0);
                    crate::leanh::lean_inc(v_space_2102_);
                    crate::leanh::lean_dec_ref(v___y_2100_);
                    v___x_2103_ = lean_nat_dec_le(v_space_2102_, v___x_2097_);
                    crate::leanh::lean_dec(v___x_2097_);
                    crate::leanh::lean_dec(v_space_2102_);
                    v___y_2086_ = v___x_2103_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2100_);
                    crate::leanh::lean_dec(v___x_2097_);
                    v___x_2104_ = 0;
                    v___y_2086_ = v___x_2104_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2108_ == 0 {
                    v___x_2109_ = lean_nat_sub(v___x_2097_, v_space_2106_);
                    crate::leanh::lean_inc(v_gs_2082_);
                    v_r_u2082_2110_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2082_,
                            v_k_2084_,
                            v___x_2109_,
                        );
                    v_foundLine_2111_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2110_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2112_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2110_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2113_ = crate::leanh::lean_ctor_get(v_r_u2082_2110_, 0);
                    v_isSharedCheck_2121_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_2110_)) as u8;
                    if v_isSharedCheck_2121_ == 0 {
                        v___x_2115_ = v_r_u2082_2110_;
                        v_isShared_2116_ = v_isSharedCheck_2121_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_2113_);
                        crate::leanh::lean_dec(v_r_u2082_2110_);
                        v___x_2115_ = crate::leanh::lean_box(0);
                        v_isShared_2116_ = v_isSharedCheck_2121_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_space_2106_);
                    crate::leanh::lean_dec(v_k_2084_);
                    crate::leanh::lean_inc_ref(v_r_2098_);
                    v___y_2100_ = v_r_2098_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2117_ = lean_nat_add(v_space_2106_, v_space_2113_);
                crate::leanh::lean_dec(v_space_2113_);
                crate::leanh::lean_dec(v_space_2106_);
                if v_isShared_2116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2115_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2120_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2120_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_2111_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2120_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_2112_,
                    );
                    v___x_2119_ = v_reuseFailAlloc_2120_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2100_ = v___x_2119_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(
    mut v_flb_2123_: *mut crate::leanh::LeanObject,
    mut v_items_2124_: *mut crate::leanh::LeanObject,
    mut v_w_2125_: *mut crate::leanh::LeanObject,
    mut v_gs_2126_: *mut crate::leanh::LeanObject,
    mut v_toPure_2127_: *mut crate::leanh::LeanObject,
    mut v_k_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_boxed_2129_: u8 = 0;
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2129_ = (crate::leanh::lean_unbox(v_flb_2123_) as u8);
    v_res_2130_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(
        v_flb_boxed_2129_,
        v_items_2124_,
        v_w_2125_,
        v_gs_2126_,
        v_toPure_2127_,
        v_k_2128_,
    );
    crate::leanh::lean_dec(v_w_2125_);
    return v_res_2130_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
    mut v_flb_2131_: u8,
    mut v_items_2132_: *mut crate::leanh::LeanObject,
    mut v_gs_2133_: *mut crate::leanh::LeanObject,
    mut v_w_2134_: *mut crate::leanh::LeanObject,
    mut v_inst_2135_: *mut crate::leanh::LeanObject,
    mut v_inst_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currColumn_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2137_ = crate::leanh::lean_ctor_get(v_inst_2135_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2137_);
    v_toBind_2138_ = crate::leanh::lean_ctor_get(v_inst_2135_, 1);
    crate::leanh::lean_inc(v_toBind_2138_);
    crate::leanh::lean_dec_ref(v_inst_2135_);
    v_currColumn_2139_ = crate::leanh::lean_ctor_get(v_inst_2136_, 2);
    crate::leanh::lean_inc(v_currColumn_2139_);
    crate::leanh::lean_dec_ref(v_inst_2136_);
    v_toPure_2140_ = crate::leanh::lean_ctor_get(v_toApplicative_2137_, 1);
    crate::leanh::lean_inc(v_toPure_2140_);
    crate::leanh::lean_dec_ref(v_toApplicative_2137_);
    v___x_2141_ = crate::leanh::lean_box((v_flb_2131_) as usize);
    v___f_2142_ = crate::leanh::lean_alloc_closure(
        l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2142_, 0, v___x_2141_);
    crate::leanh::lean_closure_set(v___f_2142_, 1, v_items_2132_);
    crate::leanh::lean_closure_set(v___f_2142_, 2, v_w_2134_);
    crate::leanh::lean_closure_set(v___f_2142_, 3, v_gs_2133_);
    crate::leanh::lean_closure_set(v___f_2142_, 4, v_toPure_2140_);
    v___x_2143_ = crate::leanh::lean_apply_4(
        v_toBind_2138_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_currColumn_2139_,
        v___f_2142_,
    );
    return v___x_2143_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(
    mut v_flb_2144_: *mut crate::leanh::LeanObject,
    mut v_items_2145_: *mut crate::leanh::LeanObject,
    mut v_gs_2146_: *mut crate::leanh::LeanObject,
    mut v_w_2147_: *mut crate::leanh::LeanObject,
    mut v_inst_2148_: *mut crate::leanh::LeanObject,
    mut v_inst_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2150_ = (crate::leanh::lean_unbox(v_flb_2144_) as u8);
    v_res_2151_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
        v_flb_boxed_2150_,
        v_items_2145_,
        v_gs_2146_,
        v_w_2147_,
        v_inst_2148_,
        v_inst_2149_,
    );
    return v_res_2151_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(
    mut v_m_2152_: *mut crate::leanh::LeanObject,
    mut v_flb_2153_: u8,
    mut v_items_2154_: *mut crate::leanh::LeanObject,
    mut v_gs_2155_: *mut crate::leanh::LeanObject,
    mut v_w_2156_: *mut crate::leanh::LeanObject,
    mut v_inst_2157_: *mut crate::leanh::LeanObject,
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
        v_flb_2153_,
        v_items_2154_,
        v_gs_2155_,
        v_w_2156_,
        v_inst_2157_,
        v_inst_2158_,
    );
    return v___x_2159_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(
    mut v_m_2160_: *mut crate::leanh::LeanObject,
    mut v_flb_2161_: *mut crate::leanh::LeanObject,
    mut v_items_2162_: *mut crate::leanh::LeanObject,
    mut v_gs_2163_: *mut crate::leanh::LeanObject,
    mut v_w_2164_: *mut crate::leanh::LeanObject,
    mut v_inst_2165_: *mut crate::leanh::LeanObject,
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_boxed_2167_: u8 = 0;
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2167_ = (crate::leanh::lean_unbox(v_flb_2161_) as u8);
    v_res_2168_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(
        v_m_2160_,
        v_flb_boxed_2167_,
        v_items_2162_,
        v_gs_2163_,
        v_w_2164_,
        v_inst_2165_,
        v_inst_2166_,
    );
    return v_res_2168_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
    mut v_fla_2169_: *mut crate::leanh::LeanObject,
    mut v_flb_2170_: u8,
    mut v_tail_2171_: *mut crate::leanh::LeanObject,
    mut v_is_x27_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2173_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2173_, 0, v_fla_2169_);
    crate::leanh::lean_ctor_set(v___x_2173_, 1, v_is_x27_2172_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_flb_2170_,
    );
    v___x_2174_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2173_);
    crate::leanh::lean_ctor_set(v___x_2174_, 1, v_tail_2171_);
    return v___x_2174_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(
    mut v_fla_2175_: *mut crate::leanh::LeanObject,
    mut v_flb_2176_: *mut crate::leanh::LeanObject,
    mut v_tail_2177_: *mut crate::leanh::LeanObject,
    mut v_is_x27_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_1984__boxed_2179_: u8 = 0;
    let mut v_res_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_1984__boxed_2179_ = (crate::leanh::lean_unbox(v_flb_2176_) as u8);
    v_res_2180_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
        v_fla_2175_,
        v_flb_1984__boxed_2179_,
        v_tail_2177_,
        v_is_x27_2178_,
    );
    return v_res_2180_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(
    mut v_endTags_2181_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2182_: *mut crate::leanh::LeanObject,
    mut v_toBind_2183_: *mut crate::leanh::LeanObject,
    mut v___f_2184_: *mut crate::leanh::LeanObject,
    mut v_____r_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = crate::leanh::lean_apply_1(v_endTags_2181_, v_activeTags_2182_);
    v___x_2187_ = crate::leanh::lean_apply_4(
        v_toBind_2183_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2186_,
        v___f_2184_,
    );
    return v___x_2187_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(
    mut v_indent_2188_: *mut crate::leanh::LeanObject,
    mut v_pushNewline_2189_: *mut crate::leanh::LeanObject,
    mut v_toBind_2190_: *mut crate::leanh::LeanObject,
    mut v___f_2191_: *mut crate::leanh::LeanObject,
    mut v_____r_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = l_Int_toNat(v_indent_2188_);
    v___x_2194_ = crate::leanh::lean_apply_1(v_pushNewline_2189_, v___x_2193_);
    v___x_2195_ = crate::leanh::lean_apply_4(
        v_toBind_2190_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2194_,
        v___f_2191_,
    );
    return v___x_2195_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(
    mut v_indent_2196_: *mut crate::leanh::LeanObject,
    mut v_pushNewline_2197_: *mut crate::leanh::LeanObject,
    mut v_toBind_2198_: *mut crate::leanh::LeanObject,
    mut v___f_2199_: *mut crate::leanh::LeanObject,
    mut v_____r_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(
        v_indent_2196_,
        v_pushNewline_2197_,
        v_toBind_2198_,
        v___f_2199_,
        v_____r_2200_,
    );
    crate::leanh::lean_dec(v_indent_2196_);
    return v_res_2201_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(
    mut v_indent_2202_: *mut crate::leanh::LeanObject,
    mut v_inst_2203_: *mut crate::leanh::LeanObject,
    mut v_toBind_2204_: *mut crate::leanh::LeanObject,
    mut v___f_2205_: *mut crate::leanh::LeanObject,
    mut v___f_2206_: *mut crate::leanh::LeanObject,
    mut v_k_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    v___x_2208_ = lean_nat_to_int(v_k_2207_);
    v___x_2209_ = lean_int_dec_lt(v___x_2208_, v_indent_2202_);
    if v___x_2209_ == 0 {
        let mut v_pushNewline_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2208_);
        crate::leanh::lean_dec(v___f_2206_);
        v_pushNewline_2210_ = crate::leanh::lean_ctor_get(v_inst_2203_, 1);
        crate::leanh::lean_inc(v_pushNewline_2210_);
        crate::leanh::lean_dec_ref(v_inst_2203_);
        v___x_2211_ = l_Int_toNat(v_indent_2202_);
        v___x_2212_ = crate::leanh::lean_apply_1(v_pushNewline_2210_, v___x_2211_);
        v___x_2213_ = crate::leanh::lean_apply_4(
            v_toBind_2204_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2212_,
            v___f_2205_,
        );
        return v___x_2213_;
    } else {
        let mut v_pushOutput_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: u32 = 0;
        let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2205_);
        v_pushOutput_2214_ = crate::leanh::lean_ctor_get(v_inst_2203_, 0);
        crate::leanh::lean_inc(v_pushOutput_2214_);
        crate::leanh::lean_dec_ref(v_inst_2203_);
        v___x_2215_ = l_Std_Format_isEmpty___closed__0;
        v___x_2216_ = 32;
        v___x_2217_ = lean_int_sub(v_indent_2202_, v___x_2208_);
        crate::leanh::lean_dec(v___x_2208_);
        v___x_2218_ = l_Int_toNat(v___x_2217_);
        crate::leanh::lean_dec(v___x_2217_);
        v___x_2219_ = lean_string_pushn(v___x_2215_, v___x_2216_, v___x_2218_);
        v___x_2220_ = crate::leanh::lean_apply_1(v_pushOutput_2214_, v___x_2219_);
        v___x_2221_ = crate::leanh::lean_apply_4(
            v_toBind_2204_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2220_,
            v___f_2206_,
        );
        return v___x_2221_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(
    mut v_indent_2222_: *mut crate::leanh::LeanObject,
    mut v_inst_2223_: *mut crate::leanh::LeanObject,
    mut v_toBind_2224_: *mut crate::leanh::LeanObject,
    mut v___f_2225_: *mut crate::leanh::LeanObject,
    mut v___f_2226_: *mut crate::leanh::LeanObject,
    mut v_k_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(
        v_indent_2222_,
        v_inst_2223_,
        v_toBind_2224_,
        v___f_2225_,
        v___f_2226_,
        v_k_2227_,
    );
    crate::leanh::lean_dec(v_indent_2222_);
    return v_res_2228_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(
    mut v_inst_2229_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2230_: *mut crate::leanh::LeanObject,
    mut v_toBind_2231_: *mut crate::leanh::LeanObject,
    mut v___f_2232_: *mut crate::leanh::LeanObject,
    mut v_____r_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_endTags_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_endTags_2234_ = crate::leanh::lean_ctor_get(v_inst_2229_, 4);
    crate::leanh::lean_inc(v_endTags_2234_);
    crate::leanh::lean_dec_ref(v_inst_2229_);
    v___x_2235_ = crate::leanh::lean_apply_1(v_endTags_2234_, v_activeTags_2230_);
    v___x_2236_ = crate::leanh::lean_apply_4(
        v_toBind_2231_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2235_,
        v___f_2232_,
    );
    return v___x_2236_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(
    mut v_gs_x27_2237_: *mut crate::leanh::LeanObject,
    mut v_tail_2238_: *mut crate::leanh::LeanObject,
    mut v_w_2239_: *mut crate::leanh::LeanObject,
    mut v_inst_2240_: *mut crate::leanh::LeanObject,
    mut v_inst_2241_: *mut crate::leanh::LeanObject,
    mut v_____r_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = crate::leanh::lean_apply_1(v_gs_x27_2237_, v_tail_2238_);
    v___x_2244_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2239_,
        v_inst_2240_,
        v_inst_2241_,
        v___x_2243_,
    );
    return v___x_2244_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(
    mut v_flb_2246_: u8,
    mut v_tail_2247_: *mut crate::leanh::LeanObject,
    mut v_tail_2248_: *mut crate::leanh::LeanObject,
    mut v_w_2249_: *mut crate::leanh::LeanObject,
    mut v_inst_2250_: *mut crate::leanh::LeanObject,
    mut v_inst_2251_: *mut crate::leanh::LeanObject,
    mut v_toBind_2252_: *mut crate::leanh::LeanObject,
    mut v_____r_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_2251_);
    crate::leanh::lean_inc_ref(v_inst_2250_);
    crate::leanh::lean_inc(v_w_2249_);
    v___x_2254_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
        v_flb_2246_,
        v_tail_2247_,
        v_tail_2248_,
        v_w_2249_,
        v_inst_2250_,
        v_inst_2251_,
    );
    v___x_2255_ = crate::leanh::lean_alloc_closure(
        l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2255_, 0, v_w_2249_);
    crate::leanh::lean_closure_set(v___x_2255_, 1, v_inst_2250_);
    crate::leanh::lean_closure_set(v___x_2255_, 2, v_inst_2251_);
    v___x_2256_ = crate::leanh::lean_apply_4(
        v_toBind_2252_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2254_,
        v___x_2255_,
    );
    return v___x_2256_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(
    mut v_flb_2257_: *mut crate::leanh::LeanObject,
    mut v_tail_2258_: *mut crate::leanh::LeanObject,
    mut v_tail_2259_: *mut crate::leanh::LeanObject,
    mut v_w_2260_: *mut crate::leanh::LeanObject,
    mut v_inst_2261_: *mut crate::leanh::LeanObject,
    mut v_inst_2262_: *mut crate::leanh::LeanObject,
    mut v_toBind_2263_: *mut crate::leanh::LeanObject,
    mut v_____r_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_2076__boxed_2265_: u8 = 0;
    let mut v_res_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_2076__boxed_2265_ = (crate::leanh::lean_unbox(v_flb_2257_) as u8);
    v_res_2266_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(
        v_flb_2076__boxed_2265_,
        v_tail_2258_,
        v_tail_2259_,
        v_w_2260_,
        v_inst_2261_,
        v_inst_2262_,
        v_toBind_2263_,
        v_____r_2264_,
    );
    return v_res_2266_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(
    mut v_breakHere_2268_: *mut crate::leanh::LeanObject,
    mut v_w_2269_: *mut crate::leanh::LeanObject,
    mut v_inst_2270_: *mut crate::leanh::LeanObject,
    mut v_inst_2271_: *mut crate::leanh::LeanObject,
    mut v_endTags_2272_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2273_: *mut crate::leanh::LeanObject,
    mut v_toBind_2274_: *mut crate::leanh::LeanObject,
    mut v_pushOutput_2275_: *mut crate::leanh::LeanObject,
    mut v___x_2276_: *mut crate::leanh::LeanObject,
    mut v_____x_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2277_) == 1 {
        let mut v_head_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fla_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: u8 = 0;
        v_head_2278_ = crate::leanh::lean_ctor_get(v_____x_2277_, 0);
        v_fla_2279_ = crate::leanh::lean_ctor_get(v_head_2278_, 0);
        v___x_2280_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2279_);
        if v___x_2280_ == 0 {
            crate::leanh::lean_dec_ref_known(v_____x_2277_, 2);
            crate::leanh::lean_dec_ref(v___x_2276_);
            crate::leanh::lean_dec(v_pushOutput_2275_);
            crate::leanh::lean_dec(v_toBind_2274_);
            crate::leanh::lean_dec(v_activeTags_2273_);
            crate::leanh::lean_dec(v_endTags_2272_);
            crate::leanh::lean_dec_ref(v_inst_2271_);
            crate::leanh::lean_dec_ref(v_inst_2270_);
            crate::leanh::lean_dec(v_w_2269_);
            crate::leanh::lean_inc(v_breakHere_2268_);
            return v_breakHere_2268_;
        } else {
            let mut v___f_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_2281_ = crate::leanh::lean_alloc_closure(
                l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_2281_, 0, v_w_2269_);
            crate::leanh::lean_closure_set(v___f_2281_, 1, v_inst_2270_);
            crate::leanh::lean_closure_set(v___f_2281_, 2, v_inst_2271_);
            crate::leanh::lean_closure_set(v___f_2281_, 3, v_____x_2277_);
            crate::leanh::lean_inc(v_toBind_2274_);
            v___f_2282_ = crate::leanh::lean_alloc_closure(
                l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_2282_, 0, v_endTags_2272_);
            crate::leanh::lean_closure_set(v___f_2282_, 1, v_activeTags_2273_);
            crate::leanh::lean_closure_set(v___f_2282_, 2, v_toBind_2274_);
            crate::leanh::lean_closure_set(v___f_2282_, 3, v___f_2281_);
            v___x_2283_ = crate::leanh::lean_apply_1(v_pushOutput_2275_, v___x_2276_);
            v___x_2284_ = crate::leanh::lean_apply_4(
                v_toBind_2274_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2283_,
                v___f_2282_,
            );
            return v___x_2284_;
        }
    } else {
        let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____x_2277_);
        crate::leanh::lean_dec_ref(v___x_2276_);
        crate::leanh::lean_dec(v_pushOutput_2275_);
        crate::leanh::lean_dec(v_toBind_2274_);
        crate::leanh::lean_dec(v_activeTags_2273_);
        crate::leanh::lean_dec(v_endTags_2272_);
        crate::leanh::lean_dec_ref(v_inst_2271_);
        crate::leanh::lean_dec(v_w_2269_);
        v___x_2285_ = crate::leanh::lean_box(0);
        v___x_2286_ = l_instInhabitedOfMonad___redArg(v_inst_2270_, v___x_2285_);
        v___x_2287_ =
            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0;
        v___x_2288_ = l_panic___redArg(v___x_2286_, v___x_2287_);
        crate::leanh::lean_dec(v___x_2286_);
        return v___x_2288_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(
    mut v_breakHere_2289_: *mut crate::leanh::LeanObject,
    mut v_w_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
    mut v_endTags_2293_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2294_: *mut crate::leanh::LeanObject,
    mut v_toBind_2295_: *mut crate::leanh::LeanObject,
    mut v_pushOutput_2296_: *mut crate::leanh::LeanObject,
    mut v___x_2297_: *mut crate::leanh::LeanObject,
    mut v_____x_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2299_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(
        v_breakHere_2289_,
        v_w_2290_,
        v_inst_2291_,
        v_inst_2292_,
        v_endTags_2293_,
        v_activeTags_2294_,
        v_toBind_2295_,
        v_pushOutput_2296_,
        v___x_2297_,
        v_____x_2298_,
    );
    crate::leanh::lean_dec(v_breakHere_2289_);
    return v_res_2299_;
}
pub unsafe fn _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
    v___x_2301_ = lean_string_length(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v_p_2303_: *mut crate::leanh::LeanObject,
    mut v___x_2304_: *mut crate::leanh::LeanObject,
    mut v_indent_2305_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2306_: *mut crate::leanh::LeanObject,
    mut v_tail_2307_: *mut crate::leanh::LeanObject,
    mut v_fla_2308_: *mut crate::leanh::LeanObject,
    mut v_flb_2309_: u8,
    mut v_tail_2310_: *mut crate::leanh::LeanObject,
    mut v_w_2311_: *mut crate::leanh::LeanObject,
    mut v_inst_2312_: *mut crate::leanh::LeanObject,
    mut v_inst_2313_: *mut crate::leanh::LeanObject,
    mut v_toBind_2314_: *mut crate::leanh::LeanObject,
    mut v_gs_x27_2315_: *mut crate::leanh::LeanObject,
    mut v_____r_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_is_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    v___x_2317_ = lean_string_utf8_next(v_a_2302_, v_p_2303_);
    v___x_2318_ = lean_string_utf8_extract(v_a_2302_, v___x_2317_, v___x_2304_);
    crate::leanh::lean_dec(v___x_2317_);
    v___x_2319_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    v___x_2320_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2319_);
    crate::leanh::lean_ctor_set(v___x_2320_, 1, v_indent_2305_);
    crate::leanh::lean_ctor_set(v___x_2320_, 2, v_activeTags_2306_);
    v_is_2321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_is_2321_, 0, v___x_2320_);
    crate::leanh::lean_ctor_set(v_is_2321_, 1, v_tail_2307_);
    v___x_2322_ = crate::leanh::lean_box(1);
    v___x_2323_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2308_, v___x_2322_);
    if v___x_2323_ == 0 {
        let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_gs_x27_2315_);
        crate::leanh::lean_inc_ref(v_inst_2313_);
        crate::leanh::lean_inc_ref(v_inst_2312_);
        crate::leanh::lean_inc(v_w_2311_);
        v___x_2324_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
            v_flb_2309_,
            v_is_2321_,
            v_tail_2310_,
            v_w_2311_,
            v_inst_2312_,
            v_inst_2313_,
        );
        v___x_2325_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___x_2325_, 0, v_w_2311_);
        crate::leanh::lean_closure_set(v___x_2325_, 1, v_inst_2312_);
        crate::leanh::lean_closure_set(v___x_2325_, 2, v_inst_2313_);
        v___x_2326_ = crate::leanh::lean_apply_4(
            v_toBind_2314_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2324_,
            v___x_2325_,
        );
        return v___x_2326_;
    } else {
        let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_2314_);
        crate::leanh::lean_dec(v_tail_2310_);
        v___x_2327_ = crate::leanh::lean_apply_1(v_gs_x27_2315_, v_is_2321_);
        v___x_2328_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
            v_w_2311_,
            v_inst_2312_,
            v_inst_2313_,
            v___x_2327_,
        );
        return v___x_2328_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_p_2330_: *mut crate::leanh::LeanObject,
    mut v___x_2331_: *mut crate::leanh::LeanObject,
    mut v_indent_2332_: *mut crate::leanh::LeanObject,
    mut v_activeTags_2333_: *mut crate::leanh::LeanObject,
    mut v_tail_2334_: *mut crate::leanh::LeanObject,
    mut v_fla_2335_: *mut crate::leanh::LeanObject,
    mut v_flb_2336_: *mut crate::leanh::LeanObject,
    mut v_tail_2337_: *mut crate::leanh::LeanObject,
    mut v_w_2338_: *mut crate::leanh::LeanObject,
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
    mut v_inst_2340_: *mut crate::leanh::LeanObject,
    mut v_toBind_2341_: *mut crate::leanh::LeanObject,
    mut v_gs_x27_2342_: *mut crate::leanh::LeanObject,
    mut v_____r_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_2100__boxed_2344_: u8 = 0;
    let mut v_res_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_2100__boxed_2344_ = (crate::leanh::lean_unbox(v_flb_2336_) as u8);
    v_res_2345_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(
        v_a_2329_,
        v_p_2330_,
        v___x_2331_,
        v_indent_2332_,
        v_activeTags_2333_,
        v_tail_2334_,
        v_fla_2335_,
        v_flb_2100__boxed_2344_,
        v_tail_2337_,
        v_w_2338_,
        v_inst_2339_,
        v_inst_2340_,
        v_toBind_2341_,
        v_gs_x27_2342_,
        v_____r_2343_,
    );
    crate::leanh::lean_dec(v_fla_2335_);
    crate::leanh::lean_dec(v___x_2331_);
    crate::leanh::lean_dec(v_p_2330_);
    crate::leanh::lean_dec_ref(v_a_2329_);
    return v_res_2345_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(
    mut v_activeTags_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_indent_2348_: *mut crate::leanh::LeanObject,
    mut v_tail_2349_: *mut crate::leanh::LeanObject,
    mut v_gs_x27_2350_: *mut crate::leanh::LeanObject,
    mut v_w_2351_: *mut crate::leanh::LeanObject,
    mut v_inst_2352_: *mut crate::leanh::LeanObject,
    mut v_inst_2353_: *mut crate::leanh::LeanObject,
    mut v_____r_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2356_ = lean_nat_add(v_activeTags_2346_, v___x_2355_);
    v___x_2357_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2357_, 0, v_a_2347_);
    crate::leanh::lean_ctor_set(v___x_2357_, 1, v_indent_2348_);
    crate::leanh::lean_ctor_set(v___x_2357_, 2, v___x_2356_);
    v___x_2358_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2358_, 0, v___x_2357_);
    crate::leanh::lean_ctor_set(v___x_2358_, 1, v_tail_2349_);
    v___x_2359_ = crate::leanh::lean_apply_1(v_gs_x27_2350_, v___x_2358_);
    v___x_2360_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2351_,
        v_inst_2352_,
        v_inst_2353_,
        v___x_2359_,
    );
    return v___x_2360_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(
    mut v_activeTags_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_indent_2363_: *mut crate::leanh::LeanObject,
    mut v_tail_2364_: *mut crate::leanh::LeanObject,
    mut v_gs_x27_2365_: *mut crate::leanh::LeanObject,
    mut v_w_2366_: *mut crate::leanh::LeanObject,
    mut v_inst_2367_: *mut crate::leanh::LeanObject,
    mut v_inst_2368_: *mut crate::leanh::LeanObject,
    mut v_____r_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(
        v_activeTags_2361_,
        v_a_2362_,
        v_indent_2363_,
        v_tail_2364_,
        v_gs_x27_2365_,
        v_w_2366_,
        v_inst_2367_,
        v_inst_2368_,
        v_____r_2369_,
    );
    crate::leanh::lean_dec(v_activeTags_2361_);
    return v_res_2370_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
    mut v_w_2371_: *mut crate::leanh::LeanObject,
    mut v_inst_2372_: *mut crate::leanh::LeanObject,
    mut v_inst_2373_: *mut crate::leanh::LeanObject,
    mut v_x_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v_fla_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flb_2390_: u8 = 0;
    let mut v_tail_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v_f_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gs_x27_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endTags_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v_pushNewline_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endTags_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endTags_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pushNewline_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endTags_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_breakHere_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_force_2438_: u8 = 0;
    let mut v___f_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currColumn_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: u8 = 0;
    let mut v_endTags_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u32 = 0;
    let mut v_p_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v_pushOutput_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pushNewline_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endTags_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_behavior_2498_: u8 = 0;
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startTag_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_unused_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut v_unused_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2374_) == 0 {
                    v_toApplicative_2375_ = crate::leanh::lean_ctor_get(v_inst_2372_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_2375_);
                    crate::leanh::lean_dec_ref(v_inst_2373_);
                    crate::leanh::lean_dec_ref(v_inst_2372_);
                    crate::leanh::lean_dec(v_w_2371_);
                    v_toPure_2376_ = crate::leanh::lean_ctor_get(v_toApplicative_2375_, 1);
                    crate::leanh::lean_inc(v_toPure_2376_);
                    crate::leanh::lean_dec_ref(v_toApplicative_2375_);
                    v___x_2377_ = crate::leanh::lean_box(0);
                    v___x_2378_ = crate::leanh::lean_apply_2(
                        v_toPure_2376_,
                        crate::leanh::lean_box(0),
                        v___x_2377_,
                    );
                    return v___x_2378_;
                } else {
                    v_head_2379_ = crate::leanh::lean_ctor_get(v_x_2374_, 0);
                    v_items_2380_ = crate::leanh::lean_ctor_get(v_head_2379_, 1);
                    crate::leanh::lean_inc(v_items_2380_);
                    if crate::leanh::lean_obj_tag(v_items_2380_) == 0 {
                        v_tail_2381_ = crate::leanh::lean_ctor_get(v_x_2374_, 1);
                        crate::leanh::lean_inc(v_tail_2381_);
                        crate::leanh::lean_dec_ref_known(v_x_2374_, 2);
                        v_x_2374_ = v_tail_2381_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_2379_);
                        v_head_2383_ = crate::leanh::lean_ctor_get(v_items_2380_, 0);
                        crate::leanh::lean_inc(v_head_2383_);
                        v_toBind_2384_ = crate::leanh::lean_ctor_get(v_inst_2372_, 1);
                        v_tail_2385_ = crate::leanh::lean_ctor_get(v_x_2374_, 1);
                        v_isSharedCheck_2528_ = (!crate::leanh::lean_is_exclusive(v_x_2374_)) as u8;
                        if v_isSharedCheck_2528_ == 0 {
                            v_unused_2529_ = crate::leanh::lean_ctor_get(v_x_2374_, 0);
                            crate::leanh::lean_dec(v_unused_2529_);
                            v___x_2387_ = v_x_2374_;
                            v_isShared_2388_ = v_isSharedCheck_2528_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_2385_);
                            crate::leanh::lean_dec(v_x_2374_);
                            v___x_2387_ = crate::leanh::lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2528_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2389_ = crate::leanh::lean_ctor_get(v_head_2379_, 0);
                crate::leanh::lean_inc(v_fla_2389_);
                v_flb_2390_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_2379_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec(v_head_2379_);
                v_tail_2391_ = crate::leanh::lean_ctor_get(v_items_2380_, 1);
                v_isSharedCheck_2526_ = (!crate::leanh::lean_is_exclusive(v_items_2380_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v_unused_2527_ = crate::leanh::lean_ctor_get(v_items_2380_, 0);
                    crate::leanh::lean_dec(v_unused_2527_);
                    v___x_2393_ = v_items_2380_;
                    v_isShared_2394_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_2391_);
                    crate::leanh::lean_dec(v_items_2380_);
                    v___x_2393_ = crate::leanh::lean_box(0);
                    v_isShared_2394_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2395_ = crate::leanh::lean_ctor_get(v_head_2383_, 0);
                v_indent_2396_ = crate::leanh::lean_ctor_get(v_head_2383_, 1);
                v_activeTags_2397_ = crate::leanh::lean_ctor_get(v_head_2383_, 2);
                v_isSharedCheck_2525_ = (!crate::leanh::lean_is_exclusive(v_head_2383_)) as u8;
                if v_isSharedCheck_2525_ == 0 {
                    v___x_2399_ = v_head_2383_;
                    v_isShared_2400_ = v_isSharedCheck_2525_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeTags_2397_);
                    crate::leanh::lean_inc(v_indent_2396_);
                    crate::leanh::lean_inc(v_f_2395_);
                    crate::leanh::lean_dec(v_head_2383_);
                    v___x_2399_ = crate::leanh::lean_box(0);
                    v_isShared_2400_ = v_isSharedCheck_2525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2401_ = crate::leanh::lean_box((v_flb_2390_) as usize);
                crate::leanh::lean_inc(v_tail_2385_);
                crate::leanh::lean_inc(v_fla_2389_);
                v_gs_x27_2402_ = crate::leanh::lean_alloc_closure(
                    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v_gs_x27_2402_, 0, v_fla_2389_);
                crate::leanh::lean_closure_set(v_gs_x27_2402_, 1, v___x_2401_);
                crate::leanh::lean_closure_set(v_gs_x27_2402_, 2, v_tail_2385_);
                match crate::leanh::lean_obj_tag(v_f_2395_) {
                    0 => {
                        crate::leanh::lean_inc(v_toBind_2384_);
                        crate::leanh::lean_del_object(v___x_2399_);
                        crate::leanh::lean_dec(v_indent_2396_);
                        crate::leanh::lean_del_object(v___x_2393_);
                        crate::leanh::lean_dec(v_fla_2389_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        crate::leanh::lean_dec(v_tail_2385_);
                        v_endTags_2403_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                        crate::leanh::lean_inc(v_endTags_2403_);
                        v___f_2404_ = crate::leanh::lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_2404_, 0, v_gs_x27_2402_);
                        crate::leanh::lean_closure_set(v___f_2404_, 1, v_tail_2391_);
                        crate::leanh::lean_closure_set(v___f_2404_, 2, v_w_2371_);
                        crate::leanh::lean_closure_set(v___f_2404_, 3, v_inst_2372_);
                        crate::leanh::lean_closure_set(v___f_2404_, 4, v_inst_2373_);
                        v___x_2405_ =
                            crate::leanh::lean_apply_1(v_endTags_2403_, v_activeTags_2397_);
                        v___x_2406_ = crate::leanh::lean_apply_4(
                            v_toBind_2384_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2405_,
                            v___f_2404_,
                        );
                        return v___x_2406_;
                    }
                    1 => {
                        crate::leanh::lean_inc(v_toBind_2384_);
                        crate::leanh::lean_del_object(v___x_2399_);
                        crate::leanh::lean_del_object(v___x_2393_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        if v_flb_2390_ == 0 {
                            crate::leanh::lean_dec(v_tail_2385_);
                            v___x_2407_ =
                                l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                            crate::leanh::lean_dec(v_fla_2389_);
                            if v___x_2407_ == 0 {
                                v_pushNewline_2408_ = crate::leanh::lean_ctor_get(v_inst_2373_, 1);
                                crate::leanh::lean_inc(v_pushNewline_2408_);
                                v_endTags_2409_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                                crate::leanh::lean_inc(v_endTags_2409_);
                                v___f_2410_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                                crate::leanh::lean_closure_set(v___f_2410_, 0, v_gs_x27_2402_);
                                crate::leanh::lean_closure_set(v___f_2410_, 1, v_tail_2391_);
                                crate::leanh::lean_closure_set(v___f_2410_, 2, v_w_2371_);
                                crate::leanh::lean_closure_set(v___f_2410_, 3, v_inst_2372_);
                                crate::leanh::lean_closure_set(v___f_2410_, 4, v_inst_2373_);
                                crate::leanh::lean_inc(v_toBind_2384_);
                                v___f_2411_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                                crate::leanh::lean_closure_set(v___f_2411_, 0, v_endTags_2409_);
                                crate::leanh::lean_closure_set(v___f_2411_, 1, v_activeTags_2397_);
                                crate::leanh::lean_closure_set(v___f_2411_, 2, v_toBind_2384_);
                                crate::leanh::lean_closure_set(v___f_2411_, 3, v___f_2410_);
                                v___x_2412_ = l_Int_toNat(v_indent_2396_);
                                crate::leanh::lean_dec(v_indent_2396_);
                                v___x_2413_ =
                                    crate::leanh::lean_apply_1(v_pushNewline_2408_, v___x_2412_);
                                v___x_2414_ = crate::leanh::lean_apply_4(
                                    v_toBind_2384_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2413_,
                                    v___f_2411_,
                                );
                                return v___x_2414_;
                            } else {
                                crate::leanh::lean_dec(v_indent_2396_);
                                v_pushOutput_2415_ = crate::leanh::lean_ctor_get(v_inst_2373_, 0);
                                crate::leanh::lean_inc(v_pushOutput_2415_);
                                v_endTags_2416_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                                crate::leanh::lean_inc(v_endTags_2416_);
                                v___f_2417_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                                crate::leanh::lean_closure_set(v___f_2417_, 0, v_gs_x27_2402_);
                                crate::leanh::lean_closure_set(v___f_2417_, 1, v_tail_2391_);
                                crate::leanh::lean_closure_set(v___f_2417_, 2, v_w_2371_);
                                crate::leanh::lean_closure_set(v___f_2417_, 3, v_inst_2372_);
                                crate::leanh::lean_closure_set(v___f_2417_, 4, v_inst_2373_);
                                crate::leanh::lean_inc(v_toBind_2384_);
                                v___f_2418_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                                crate::leanh::lean_closure_set(v___f_2418_, 0, v_endTags_2416_);
                                crate::leanh::lean_closure_set(v___f_2418_, 1, v_activeTags_2397_);
                                crate::leanh::lean_closure_set(v___f_2418_, 2, v_toBind_2384_);
                                crate::leanh::lean_closure_set(v___f_2418_, 3, v___f_2417_);
                                v___x_2419_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                                v___x_2420_ =
                                    crate::leanh::lean_apply_1(v_pushOutput_2415_, v___x_2419_);
                                v___x_2421_ = crate::leanh::lean_apply_4(
                                    v_toBind_2384_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2420_,
                                    v___f_2418_,
                                );
                                return v___x_2421_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_gs_x27_2402_);
                            v_pushOutput_2422_ = crate::leanh::lean_ctor_get(v_inst_2373_, 0);
                            v_pushNewline_2423_ = crate::leanh::lean_ctor_get(v_inst_2373_, 1);
                            v_endTags_2424_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                            v___x_2425_ = crate::leanh::lean_box((v_flb_2390_) as usize);
                            crate::leanh::lean_inc_n(v_toBind_2384_, 3);
                            crate::leanh::lean_inc_ref(v_inst_2373_);
                            crate::leanh::lean_inc_ref(v_inst_2372_);
                            crate::leanh::lean_inc(v_w_2371_);
                            crate::leanh::lean_inc(v_tail_2385_);
                            crate::leanh::lean_inc(v_tail_2391_);
                            v___f_2426_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed as *mut core::ffi::c_void, 8, 7);
                            crate::leanh::lean_closure_set(v___f_2426_, 0, v___x_2425_);
                            crate::leanh::lean_closure_set(v___f_2426_, 1, v_tail_2391_);
                            crate::leanh::lean_closure_set(v___f_2426_, 2, v_tail_2385_);
                            crate::leanh::lean_closure_set(v___f_2426_, 3, v_w_2371_);
                            crate::leanh::lean_closure_set(v___f_2426_, 4, v_inst_2372_);
                            crate::leanh::lean_closure_set(v___f_2426_, 5, v_inst_2373_);
                            crate::leanh::lean_closure_set(v___f_2426_, 6, v_toBind_2384_);
                            crate::leanh::lean_inc(v_activeTags_2397_);
                            crate::leanh::lean_inc(v_endTags_2424_);
                            v___f_2427_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                            crate::leanh::lean_closure_set(v___f_2427_, 0, v_endTags_2424_);
                            crate::leanh::lean_closure_set(v___f_2427_, 1, v_activeTags_2397_);
                            crate::leanh::lean_closure_set(v___f_2427_, 2, v_toBind_2384_);
                            crate::leanh::lean_closure_set(v___f_2427_, 3, v___f_2426_);
                            v___x_2428_ = l_Int_toNat(v_indent_2396_);
                            crate::leanh::lean_dec(v_indent_2396_);
                            crate::leanh::lean_inc(v_pushNewline_2423_);
                            v___x_2429_ =
                                crate::leanh::lean_apply_1(v_pushNewline_2423_, v___x_2428_);
                            v_breakHere_2430_ = crate::leanh::lean_apply_4(
                                v_toBind_2384_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2429_,
                                v___f_2427_,
                            );
                            v___x_2431_ =
                                l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                            crate::leanh::lean_dec(v_fla_2389_);
                            if v___x_2431_ == 0 {
                                crate::leanh::lean_dec(v_activeTags_2397_);
                                crate::leanh::lean_dec(v_tail_2391_);
                                crate::leanh::lean_dec(v_tail_2385_);
                                crate::leanh::lean_dec(v_toBind_2384_);
                                crate::leanh::lean_dec_ref(v_inst_2373_);
                                crate::leanh::lean_dec_ref(v_inst_2372_);
                                crate::leanh::lean_dec(v_w_2371_);
                                return v_breakHere_2430_;
                            } else {
                                v___x_2432_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                                crate::leanh::lean_inc(v_pushOutput_2422_);
                                crate::leanh::lean_inc(v_toBind_2384_);
                                crate::leanh::lean_inc(v_endTags_2424_);
                                crate::leanh::lean_inc_ref(v_inst_2373_);
                                crate::leanh::lean_inc_ref(v_inst_2372_);
                                crate::leanh::lean_inc(v_w_2371_);
                                v___f_2433_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed as *mut core::ffi::c_void, 10, 9);
                                crate::leanh::lean_closure_set(v___f_2433_, 0, v_breakHere_2430_);
                                crate::leanh::lean_closure_set(v___f_2433_, 1, v_w_2371_);
                                crate::leanh::lean_closure_set(v___f_2433_, 2, v_inst_2372_);
                                crate::leanh::lean_closure_set(v___f_2433_, 3, v_inst_2373_);
                                crate::leanh::lean_closure_set(v___f_2433_, 4, v_endTags_2424_);
                                crate::leanh::lean_closure_set(v___f_2433_, 5, v_activeTags_2397_);
                                crate::leanh::lean_closure_set(v___f_2433_, 6, v_toBind_2384_);
                                crate::leanh::lean_closure_set(v___f_2433_, 7, v_pushOutput_2422_);
                                crate::leanh::lean_closure_set(v___f_2433_, 8, v___x_2432_);
                                v___x_2434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                                v___x_2435_ = lean_nat_sub(v_w_2371_, v___x_2434_);
                                crate::leanh::lean_dec(v_w_2371_);
                                v___x_2436_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_2390_, v_tail_2391_, v_tail_2385_, v___x_2435_, v_inst_2372_, v_inst_2373_);
                                v___x_2437_ = crate::leanh::lean_apply_4(
                                    v_toBind_2384_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2436_,
                                    v___f_2433_,
                                );
                                return v___x_2437_;
                            }
                        }
                    }
                    2 => {
                        crate::leanh::lean_inc_n(v_toBind_2384_, 3);
                        crate::leanh::lean_del_object(v___x_2399_);
                        crate::leanh::lean_del_object(v___x_2393_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        crate::leanh::lean_dec(v_tail_2385_);
                        v_force_2438_ = crate::leanh::lean_ctor_get_uint8(v_f_2395_, 0 as u32);
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 0);
                        crate::leanh::lean_inc_ref_n(v_inst_2373_, 3);
                        v___f_2439_ = crate::leanh::lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_2439_, 0, v_gs_x27_2402_);
                        crate::leanh::lean_closure_set(v___f_2439_, 1, v_tail_2391_);
                        crate::leanh::lean_closure_set(v___f_2439_, 2, v_w_2371_);
                        crate::leanh::lean_closure_set(v___f_2439_, 3, v_inst_2372_);
                        crate::leanh::lean_closure_set(v___f_2439_, 4, v_inst_2373_);
                        crate::leanh::lean_inc_ref(v___f_2439_);
                        crate::leanh::lean_inc(v_activeTags_2397_);
                        v___f_2440_ = crate::leanh::lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_2440_, 0, v_inst_2373_);
                        crate::leanh::lean_closure_set(v___f_2440_, 1, v_activeTags_2397_);
                        crate::leanh::lean_closure_set(v___f_2440_, 2, v_toBind_2384_);
                        crate::leanh::lean_closure_set(v___f_2440_, 3, v___f_2439_);
                        crate::leanh::lean_inc_ref(v___f_2440_);
                        v___f_2441_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 5);
                        crate::leanh::lean_closure_set(v___f_2441_, 0, v_indent_2396_);
                        crate::leanh::lean_closure_set(v___f_2441_, 1, v_inst_2373_);
                        crate::leanh::lean_closure_set(v___f_2441_, 2, v_toBind_2384_);
                        crate::leanh::lean_closure_set(v___f_2441_, 3, v___f_2440_);
                        crate::leanh::lean_closure_set(v___f_2441_, 4, v___f_2440_);
                        v___x_2450_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                        crate::leanh::lean_dec(v_fla_2389_);
                        if v___x_2450_ == 0 {
                            v___y_2446_ = v___x_2450_;
                            state = 5;
                            continue;
                        } else {
                            if v_force_2438_ == 0 {
                                v___y_2446_ = v___x_2450_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___f_2439_);
                                crate::leanh::lean_dec(v_activeTags_2397_);
                                state = 4;
                                continue;
                            }
                        }
                    }
                    3 => {
                        crate::leanh::lean_inc(v_toBind_2384_);
                        crate::leanh::lean_del_object(v___x_2399_);
                        crate::leanh::lean_del_object(v___x_2393_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        v_a_2451_ = crate::leanh::lean_ctor_get(v_f_2395_, 0);
                        crate::leanh::lean_inc_ref_n(v_a_2451_, 2);
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 1);
                        v___x_2452_ = 10;
                        v_p_2453_ = lean_string_posof(v_a_2451_, v___x_2452_);
                        v___x_2454_ = lean_string_utf8_byte_size(v_a_2451_);
                        v___x_2455_ = lean_nat_dec_eq(v_p_2453_, v___x_2454_);
                        if v___x_2455_ == 0 {
                            v_pushOutput_2456_ = crate::leanh::lean_ctor_get(v_inst_2373_, 0);
                            crate::leanh::lean_inc(v_pushOutput_2456_);
                            v_pushNewline_2457_ = crate::leanh::lean_ctor_get(v_inst_2373_, 1);
                            crate::leanh::lean_inc(v_pushNewline_2457_);
                            v___x_2458_ = crate::leanh::lean_box((v_flb_2390_) as usize);
                            crate::leanh::lean_inc_n(v_toBind_2384_, 2);
                            crate::leanh::lean_inc(v_indent_2396_);
                            crate::leanh::lean_inc(v_p_2453_);
                            crate::leanh::lean_inc_ref(v_a_2451_);
                            v___f_2459_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed as *mut core::ffi::c_void, 15, 14);
                            crate::leanh::lean_closure_set(v___f_2459_, 0, v_a_2451_);
                            crate::leanh::lean_closure_set(v___f_2459_, 1, v_p_2453_);
                            crate::leanh::lean_closure_set(v___f_2459_, 2, v___x_2454_);
                            crate::leanh::lean_closure_set(v___f_2459_, 3, v_indent_2396_);
                            crate::leanh::lean_closure_set(v___f_2459_, 4, v_activeTags_2397_);
                            crate::leanh::lean_closure_set(v___f_2459_, 5, v_tail_2391_);
                            crate::leanh::lean_closure_set(v___f_2459_, 6, v_fla_2389_);
                            crate::leanh::lean_closure_set(v___f_2459_, 7, v___x_2458_);
                            crate::leanh::lean_closure_set(v___f_2459_, 8, v_tail_2385_);
                            crate::leanh::lean_closure_set(v___f_2459_, 9, v_w_2371_);
                            crate::leanh::lean_closure_set(v___f_2459_, 10, v_inst_2372_);
                            crate::leanh::lean_closure_set(v___f_2459_, 11, v_inst_2373_);
                            crate::leanh::lean_closure_set(v___f_2459_, 12, v_toBind_2384_);
                            crate::leanh::lean_closure_set(v___f_2459_, 13, v_gs_x27_2402_);
                            v___f_2460_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed as *mut core::ffi::c_void, 5, 4);
                            crate::leanh::lean_closure_set(v___f_2460_, 0, v_indent_2396_);
                            crate::leanh::lean_closure_set(v___f_2460_, 1, v_pushNewline_2457_);
                            crate::leanh::lean_closure_set(v___f_2460_, 2, v_toBind_2384_);
                            crate::leanh::lean_closure_set(v___f_2460_, 3, v___f_2459_);
                            v___x_2461_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2462_ =
                                lean_string_utf8_extract(v_a_2451_, v___x_2461_, v_p_2453_);
                            crate::leanh::lean_dec(v_p_2453_);
                            crate::leanh::lean_dec_ref(v_a_2451_);
                            v___x_2463_ =
                                crate::leanh::lean_apply_1(v_pushOutput_2456_, v___x_2462_);
                            v___x_2464_ = crate::leanh::lean_apply_4(
                                v_toBind_2384_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2463_,
                                v___f_2460_,
                            );
                            return v___x_2464_;
                        } else {
                            crate::leanh::lean_dec(v_p_2453_);
                            crate::leanh::lean_dec(v_indent_2396_);
                            crate::leanh::lean_dec(v_fla_2389_);
                            crate::leanh::lean_dec(v_tail_2385_);
                            v_pushOutput_2465_ = crate::leanh::lean_ctor_get(v_inst_2373_, 0);
                            crate::leanh::lean_inc(v_pushOutput_2465_);
                            v_endTags_2466_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                            crate::leanh::lean_inc(v_endTags_2466_);
                            v___f_2467_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                            crate::leanh::lean_closure_set(v___f_2467_, 0, v_gs_x27_2402_);
                            crate::leanh::lean_closure_set(v___f_2467_, 1, v_tail_2391_);
                            crate::leanh::lean_closure_set(v___f_2467_, 2, v_w_2371_);
                            crate::leanh::lean_closure_set(v___f_2467_, 3, v_inst_2372_);
                            crate::leanh::lean_closure_set(v___f_2467_, 4, v_inst_2373_);
                            crate::leanh::lean_inc(v_toBind_2384_);
                            v___f_2468_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                            crate::leanh::lean_closure_set(v___f_2468_, 0, v_endTags_2466_);
                            crate::leanh::lean_closure_set(v___f_2468_, 1, v_activeTags_2397_);
                            crate::leanh::lean_closure_set(v___f_2468_, 2, v_toBind_2384_);
                            crate::leanh::lean_closure_set(v___f_2468_, 3, v___f_2467_);
                            v___x_2469_ = crate::leanh::lean_apply_1(v_pushOutput_2465_, v_a_2451_);
                            v___x_2470_ = crate::leanh::lean_apply_4(
                                v_toBind_2384_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2469_,
                                v___f_2468_,
                            );
                            return v___x_2470_;
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v_gs_x27_2402_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        v_indent_2471_ = crate::leanh::lean_ctor_get(v_f_2395_, 0);
                        crate::leanh::lean_inc(v_indent_2471_);
                        v_f_2472_ = crate::leanh::lean_ctor_get(v_f_2395_, 1);
                        crate::leanh::lean_inc(v_f_2472_);
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 2);
                        v___x_2473_ = lean_int_add(v_indent_2396_, v_indent_2471_);
                        crate::leanh::lean_dec(v_indent_2471_);
                        crate::leanh::lean_dec(v_indent_2396_);
                        if v_isShared_2400_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2399_, 1, v___x_2473_);
                            crate::leanh::lean_ctor_set(v___x_2399_, 0, v_f_2472_);
                            v___x_2475_ = v___x_2399_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2481_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_f_2472_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2473_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2481_,
                                2,
                                v_activeTags_2397_,
                            );
                            v___x_2475_ = v_reuseFailAlloc_2481_;
                            state = 6;
                            continue;
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v_gs_x27_2402_);
                        v_a_2482_ = crate::leanh::lean_ctor_get(v_f_2395_, 0);
                        crate::leanh::lean_inc(v_a_2482_);
                        v_a_2483_ = crate::leanh::lean_ctor_get(v_f_2395_, 1);
                        crate::leanh::lean_inc(v_a_2483_);
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 2);
                        v___x_2484_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v_indent_2396_);
                        if v_isShared_2400_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2399_, 2, v___x_2484_);
                            crate::leanh::lean_ctor_set(v___x_2399_, 0, v_a_2482_);
                            v___x_2486_ = v___x_2399_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2496_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2482_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_indent_2396_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 2, v___x_2484_);
                            v___x_2486_ = v_reuseFailAlloc_2496_;
                            state = 8;
                            continue;
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v_gs_x27_2402_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        v_a_2497_ = crate::leanh::lean_ctor_get(v_f_2395_, 0);
                        crate::leanh::lean_inc(v_a_2497_);
                        v_behavior_2498_ = crate::leanh::lean_ctor_get_uint8(
                            v_f_2395_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 1);
                        v___x_2499_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                        if v___x_2499_ == 0 {
                            crate::leanh::lean_inc(v_toBind_2384_);
                            if v_isShared_2400_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2399_, 0, v_a_2497_);
                                v___x_2501_ = v___x_2399_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2510_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2497_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2510_,
                                    1,
                                    v_indent_2396_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2510_,
                                    2,
                                    v_activeTags_2397_,
                                );
                                v___x_2501_ = v_reuseFailAlloc_2510_;
                                state = 11;
                                continue;
                            }
                        } else {
                            if v_isShared_2400_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2399_, 0, v_a_2497_);
                                v___x_2512_ = v___x_2399_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_2518_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2497_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2518_,
                                    1,
                                    v_indent_2396_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2518_,
                                    2,
                                    v_activeTags_2397_,
                                );
                                v___x_2512_ = v_reuseFailAlloc_2518_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_inc(v_toBind_2384_);
                        crate::leanh::lean_del_object(v___x_2399_);
                        crate::leanh::lean_del_object(v___x_2393_);
                        crate::leanh::lean_dec(v_fla_2389_);
                        crate::leanh::lean_del_object(v___x_2387_);
                        crate::leanh::lean_dec(v_tail_2385_);
                        v_a_2519_ = crate::leanh::lean_ctor_get(v_f_2395_, 0);
                        crate::leanh::lean_inc(v_a_2519_);
                        v_a_2520_ = crate::leanh::lean_ctor_get(v_f_2395_, 1);
                        crate::leanh::lean_inc(v_a_2520_);
                        crate::leanh::lean_dec_ref_known(v_f_2395_, 2);
                        v_startTag_2521_ = crate::leanh::lean_ctor_get(v_inst_2373_, 3);
                        crate::leanh::lean_inc(v_startTag_2521_);
                        v___f_2522_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed as *mut core::ffi::c_void, 9, 8);
                        crate::leanh::lean_closure_set(v___f_2522_, 0, v_activeTags_2397_);
                        crate::leanh::lean_closure_set(v___f_2522_, 1, v_a_2520_);
                        crate::leanh::lean_closure_set(v___f_2522_, 2, v_indent_2396_);
                        crate::leanh::lean_closure_set(v___f_2522_, 3, v_tail_2391_);
                        crate::leanh::lean_closure_set(v___f_2522_, 4, v_gs_x27_2402_);
                        crate::leanh::lean_closure_set(v___f_2522_, 5, v_w_2371_);
                        crate::leanh::lean_closure_set(v___f_2522_, 6, v_inst_2372_);
                        crate::leanh::lean_closure_set(v___f_2522_, 7, v_inst_2373_);
                        v___x_2523_ = crate::leanh::lean_apply_1(v_startTag_2521_, v_a_2519_);
                        v___x_2524_ = crate::leanh::lean_apply_4(
                            v_toBind_2384_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2523_,
                            v___f_2522_,
                        );
                        return v___x_2524_;
                    }
                }
            }
            4 => {
                v_currColumn_2443_ = crate::leanh::lean_ctor_get(v_inst_2373_, 2);
                crate::leanh::lean_inc(v_currColumn_2443_);
                crate::leanh::lean_dec_ref(v_inst_2373_);
                v___x_2444_ = crate::leanh::lean_apply_4(
                    v_toBind_2384_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_currColumn_2443_,
                    v___f_2441_,
                );
                return v___x_2444_;
            }
            5 => {
                if v___y_2446_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_2439_);
                    crate::leanh::lean_dec(v_activeTags_2397_);
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___f_2441_);
                    v_endTags_2447_ = crate::leanh::lean_ctor_get(v_inst_2373_, 4);
                    crate::leanh::lean_inc(v_endTags_2447_);
                    crate::leanh::lean_dec_ref(v_inst_2373_);
                    v___x_2448_ = crate::leanh::lean_apply_1(v_endTags_2447_, v_activeTags_2397_);
                    v___x_2449_ = crate::leanh::lean_apply_4(
                        v_toBind_2384_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2448_,
                        v___f_2439_,
                    );
                    return v___x_2449_;
                }
            }
            6 => {
                if v_isShared_2394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_tail_2391_);
                    v___x_2477_ = v_reuseFailAlloc_2480_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2478_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2389_,
                    v_flb_2390_,
                    v_tail_2385_,
                    v___x_2477_,
                );
                v_x_2374_ = v___x_2478_;
                state = 0;
                continue;
            }
            8 => {
                v___x_2487_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2487_, 0, v_a_2483_);
                crate::leanh::lean_ctor_set(v___x_2487_, 1, v_indent_2396_);
                crate::leanh::lean_ctor_set(v___x_2487_, 2, v_activeTags_2397_);
                if v_isShared_2394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2487_);
                    v___x_2489_ = v___x_2393_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_tail_2391_);
                    v___x_2489_ = v_reuseFailAlloc_2495_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2489_);
                    crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2486_);
                    v___x_2491_ = v___x_2387_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2489_);
                    v___x_2491_ = v_reuseFailAlloc_2494_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2492_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2389_,
                    v_flb_2390_,
                    v_tail_2385_,
                    v___x_2491_,
                );
                v_x_2374_ = v___x_2492_;
                state = 0;
                continue;
            }
            11 => {
                v___x_2502_ = crate::leanh::lean_box(0);
                if v_isShared_2394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2393_, 1, v___x_2502_);
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2501_);
                    v___x_2504_ = v___x_2393_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2502_);
                    v___x_2504_ = v_reuseFailAlloc_2509_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2505_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2389_,
                    v_flb_2390_,
                    v_tail_2385_,
                    v_tail_2391_,
                );
                crate::leanh::lean_inc_ref(v_inst_2373_);
                crate::leanh::lean_inc_ref(v_inst_2372_);
                crate::leanh::lean_inc(v_w_2371_);
                v___x_2506_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
                    v_behavior_2498_,
                    v___x_2504_,
                    v___x_2505_,
                    v_w_2371_,
                    v_inst_2372_,
                    v_inst_2373_,
                );
                v___x_2507_ = crate::leanh::lean_alloc_closure(
                    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2507_, 0, v_w_2371_);
                crate::leanh::lean_closure_set(v___x_2507_, 1, v_inst_2372_);
                crate::leanh::lean_closure_set(v___x_2507_, 2, v_inst_2373_);
                v___x_2508_ = crate::leanh::lean_apply_4(
                    v_toBind_2384_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2506_,
                    v___x_2507_,
                );
                return v___x_2508_;
            }
            13 => {
                if v_isShared_2394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2512_);
                    v___x_2514_ = v___x_2393_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_tail_2391_);
                    v___x_2514_ = v_reuseFailAlloc_2517_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2515_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2389_,
                    v_flb_2390_,
                    v_tail_2385_,
                    v___x_2514_,
                );
                v_x_2374_ = v___x_2515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(
    mut v_w_2530_: *mut crate::leanh::LeanObject,
    mut v_inst_2531_: *mut crate::leanh::LeanObject,
    mut v_inst_2532_: *mut crate::leanh::LeanObject,
    mut v_____x_2533_: *mut crate::leanh::LeanObject,
    mut v_____r_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2530_,
        v_inst_2531_,
        v_inst_2532_,
        v_____x_2533_,
    );
    return v___x_2535_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be(
    mut v_m_2536_: *mut crate::leanh::LeanObject,
    mut v_w_2537_: *mut crate::leanh::LeanObject,
    mut v_inst_2538_: *mut crate::leanh::LeanObject,
    mut v_inst_2539_: *mut crate::leanh::LeanObject,
    mut v_x_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2537_,
        v_inst_2538_,
        v_inst_2539_,
        v_x_2540_,
    );
    return v___x_2541_;
}
pub unsafe fn l_Std_Format_prettyM___redArg(
    mut v_f_2542_: *mut crate::leanh::LeanObject,
    mut v_w_2543_: *mut crate::leanh::LeanObject,
    mut v_indent_2544_: *mut crate::leanh::LeanObject,
    mut v_inst_2545_: *mut crate::leanh::LeanObject,
    mut v_inst_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = crate::leanh::lean_box(1);
    v___x_2548_ = 0;
    v___x_2549_ = lean_nat_to_int(v_indent_2544_);
    v___x_2550_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2551_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2551_, 0, v_f_2542_);
    crate::leanh::lean_ctor_set(v___x_2551_, 1, v___x_2549_);
    crate::leanh::lean_ctor_set(v___x_2551_, 2, v___x_2550_);
    v___x_2552_ = crate::leanh::lean_box(0);
    v___x_2553_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2553_, 0, v___x_2551_);
    crate::leanh::lean_ctor_set(v___x_2553_, 1, v___x_2552_);
    v___x_2554_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2547_);
    crate::leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2554_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2548_,
    );
    v___x_2555_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2554_);
    crate::leanh::lean_ctor_set(v___x_2555_, 1, v___x_2552_);
    v___x_2556_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2543_,
        v_inst_2545_,
        v_inst_2546_,
        v___x_2555_,
    );
    return v___x_2556_;
}
pub unsafe fn l_Std_Format_prettyM(
    mut v_m_2557_: *mut crate::leanh::LeanObject,
    mut v_f_2558_: *mut crate::leanh::LeanObject,
    mut v_w_2559_: *mut crate::leanh::LeanObject,
    mut v_indent_2560_: *mut crate::leanh::LeanObject,
    mut v_inst_2561_: *mut crate::leanh::LeanObject,
    mut v_inst_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = l_Std_Format_prettyM___redArg(
        v_f_2558_,
        v_w_2559_,
        v_indent_2560_,
        v_inst_2561_,
        v_inst_2562_,
    );
    return v___x_2563_;
}
pub unsafe fn l_Std_Format_bracket(
    mut v_l_2564_: *mut crate::leanh::LeanObject,
    mut v_f_2565_: *mut crate::leanh::LeanObject,
    mut v_r_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = lean_string_length(v_l_2564_);
    v___x_2568_ = lean_nat_to_int(v___x_2567_);
    v___x_2569_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2569_, 0, v_l_2564_);
    v___x_2570_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2569_);
    crate::leanh::lean_ctor_set(v___x_2570_, 1, v_f_2565_);
    v___x_2571_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2571_, 0, v_r_2566_);
    v___x_2572_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2572_, 0, v___x_2570_);
    crate::leanh::lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2573_, 0, v___x_2568_);
    crate::leanh::lean_ctor_set(v___x_2573_, 1, v___x_2572_);
    v___x_2574_ = 0;
    v___x_2575_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2573_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2575_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2574_,
    );
    return v___x_2575_;
}
pub unsafe fn _init_l_Std_Format_paren___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_Format_paren___closed__0;
    v___x_2579_ = lean_string_length(v___x_2578_);
    return v___x_2579_;
}
pub unsafe fn _init_l_Std_Format_paren___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__2),
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__2_once),
        _init_l_Std_Format_paren___closed__2,
    );
    v___x_2581_ = lean_nat_to_int(v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Std_Format_paren(
    mut v_f_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__3),
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__3_once),
        _init_l_Std_Format_paren___closed__3,
    );
    v___x_2588_ = l_Std_Format_paren___closed__4;
    v___x_2589_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2589_, 0, v___x_2588_);
    crate::leanh::lean_ctor_set(v___x_2589_, 1, v_f_2586_);
    v___x_2590_ = l_Std_Format_paren___closed__5;
    v___x_2591_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2591_, 0, v___x_2589_);
    crate::leanh::lean_ctor_set(v___x_2591_, 1, v___x_2590_);
    v___x_2592_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2592_, 0, v___x_2587_);
    crate::leanh::lean_ctor_set(v___x_2592_, 1, v___x_2591_);
    v___x_2593_ = 0;
    v___x_2594_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2594_, 0, v___x_2592_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2594_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2593_,
    );
    return v___x_2594_;
}
pub unsafe fn _init_l_Std_Format_sbracket___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Std_Format_sbracket___closed__0;
    v___x_2598_ = lean_string_length(v___x_2597_);
    return v___x_2598_;
}
pub unsafe fn _init_l_Std_Format_sbracket___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__2),
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__2_once),
        _init_l_Std_Format_sbracket___closed__2,
    );
    v___x_2600_ = lean_nat_to_int(v___x_2599_);
    return v___x_2600_;
}
pub unsafe fn l_Std_Format_sbracket(
    mut v_f_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2606_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__3),
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__3_once),
        _init_l_Std_Format_sbracket___closed__3,
    );
    v___x_2607_ = l_Std_Format_sbracket___closed__4;
    v___x_2608_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2607_);
    crate::leanh::lean_ctor_set(v___x_2608_, 1, v_f_2605_);
    v___x_2609_ = l_Std_Format_sbracket___closed__5;
    v___x_2610_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2610_, 0, v___x_2608_);
    crate::leanh::lean_ctor_set(v___x_2610_, 1, v___x_2609_);
    v___x_2611_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2611_, 0, v___x_2606_);
    crate::leanh::lean_ctor_set(v___x_2611_, 1, v___x_2610_);
    v___x_2612_ = 0;
    v___x_2613_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2613_, 0, v___x_2611_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2613_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2612_,
    );
    return v___x_2613_;
}
pub unsafe fn l_Std_Format_bracketFill(
    mut v_l_2614_: *mut crate::leanh::LeanObject,
    mut v_f_2615_: *mut crate::leanh::LeanObject,
    mut v_r_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2617_ = lean_string_length(v_l_2614_);
    v___x_2618_ = lean_nat_to_int(v___x_2617_);
    v___x_2619_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2619_, 0, v_l_2614_);
    v___x_2620_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 1, v_f_2615_);
    v___x_2621_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2621_, 0, v_r_2616_);
    v___x_2622_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2620_);
    crate::leanh::lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    v___x_2623_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2623_, 1, v___x_2622_);
    v___x_2624_ = l_Std_Format_fill(v___x_2623_);
    return v___x_2624_;
}
pub unsafe fn _init_l_Std_Format_defIndent() -> *mut crate::leanh::LeanObject {
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2625_ = crate::leanh::lean_unsigned_to_nat(2);
    return v___x_2625_;
}
pub unsafe fn _init_l_Std_Format_defUnicode() -> u8 {
    let mut v___x_2626_: u8 = 0;
    v___x_2626_ = 1;
    return v___x_2626_;
}
pub unsafe fn _init_l_Std_Format_defWidth() -> *mut crate::leanh::LeanObject {
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2627_ = crate::leanh::lean_unsigned_to_nat(120);
    return v___x_2627_;
}
pub unsafe fn _init_l_Std_Format_nestD___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2629_ = lean_nat_to_int(v___x_2628_);
    return v___x_2629_;
}
pub unsafe fn l_Std_Format_nestD(
    mut v_f_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_nestD___closed__0),
        core::ptr::addr_of_mut!(l_Std_Format_nestD___closed__0_once),
        _init_l_Std_Format_nestD___closed__0,
    );
    v___x_2632_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2631_);
    crate::leanh::lean_ctor_set(v___x_2632_, 1, v_f_2630_);
    return v___x_2632_;
}
pub unsafe fn l_Std_Format_indentD(
    mut v_f_2633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2634_ = crate::leanh::lean_box(1);
    v___x_2635_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2634_);
    crate::leanh::lean_ctor_set(v___x_2635_, 1, v_f_2633_);
    v___x_2636_ = l_Std_Format_nestD(v___x_2635_);
    return v___x_2636_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(
    mut v_s_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2639_ = crate::leanh::lean_ctor_get(v___y_2638_, 0);
                v_column_2640_ = crate::leanh::lean_ctor_get(v___y_2638_, 1);
                v_isSharedCheck_2652_ = (!crate::leanh::lean_is_exclusive(v___y_2638_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v___x_2642_ = v___y_2638_;
                    v_isShared_2643_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2640_);
                    crate::leanh::lean_inc(v_out_2639_);
                    crate::leanh::lean_dec(v___y_2638_);
                    v___x_2642_ = crate::leanh::lean_box(0);
                    v_isShared_2643_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2644_ = crate::leanh::lean_box(0);
                v___x_2645_ = lean_string_append(v_out_2639_, v_s_2637_);
                v___x_2646_ = lean_string_length(v_s_2637_);
                v___x_2647_ = lean_nat_add(v_column_2640_, v___x_2646_);
                crate::leanh::lean_dec(v___x_2646_);
                crate::leanh::lean_dec(v_column_2640_);
                if v_isShared_2643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2642_, 1, v___x_2647_);
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2645_);
                    v___x_2649_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2647_);
                    v___x_2649_ = v_reuseFailAlloc_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2650_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2650_, 0, v___x_2644_);
                crate::leanh::lean_ctor_set(v___x_2650_, 1, v___x_2649_);
                return v___x_2650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(
    mut v_s_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ =
        l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(
            v_s_2653_,
            v___y_2654_,
        );
    crate::leanh::lean_dec_ref(v_s_2653_);
    return v_res_2655_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(
    mut v_indent_2657_: *mut crate::leanh::LeanObject,
    mut v___y_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: u32 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_unused_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2659_ = crate::leanh::lean_ctor_get(v___y_2658_, 0);
                v_isSharedCheck_2672_ = (!crate::leanh::lean_is_exclusive(v___y_2658_)) as u8;
                if v_isSharedCheck_2672_ == 0 {
                    v_unused_2673_ = crate::leanh::lean_ctor_get(v___y_2658_, 1);
                    crate::leanh::lean_dec(v_unused_2673_);
                    v___x_2661_ = v___y_2658_;
                    v_isShared_2662_ = v_isSharedCheck_2672_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_out_2659_);
                    crate::leanh::lean_dec(v___y_2658_);
                    v___x_2661_ = crate::leanh::lean_box(0);
                    v_isShared_2662_ = v_isSharedCheck_2672_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2663_ = crate::leanh::lean_box(0);
                v___x_2664_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2665_ = 32;
                crate::leanh::lean_inc(v_indent_2657_);
                v___x_2666_ = lean_string_pushn(v___x_2664_, v___x_2665_, v_indent_2657_);
                v___x_2667_ = lean_string_append(v_out_2659_, v___x_2666_);
                crate::leanh::lean_dec_ref(v___x_2666_);
                if v_isShared_2662_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2661_, 1, v_indent_2657_);
                    crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_indent_2657_);
                    v___x_2669_ = v_reuseFailAlloc_2671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2670_, 0, v___x_2663_);
                crate::leanh::lean_ctor_set(v___x_2670_, 1, v___x_2669_);
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(
    mut v_____do__lift_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_column_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_unused_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2676_ = crate::leanh::lean_ctor_get(v_____do__lift_2674_, 1);
                v_isSharedCheck_2683_ =
                    (!crate::leanh::lean_is_exclusive(v_____do__lift_2674_)) as u8;
                if v_isSharedCheck_2683_ == 0 {
                    v_unused_2684_ = crate::leanh::lean_ctor_get(v_____do__lift_2674_, 0);
                    crate::leanh::lean_dec(v_unused_2684_);
                    v___x_2678_ = v_____do__lift_2674_;
                    v_isShared_2679_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2676_);
                    crate::leanh::lean_dec(v_____do__lift_2674_);
                    v___x_2678_ = crate::leanh::lean_box(0);
                    v_isShared_2679_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2678_, 1, v___y_2675_);
                    crate::leanh::lean_ctor_set(v___x_2678_, 0, v_column_2676_);
                    v___x_2681_ = v___x_2678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_column_2676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___y_2675_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(
    mut v_x_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = crate::leanh::lean_box(0);
    v___x_2688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2688_, 0, v___x_2687_);
    crate::leanh::lean_ctor_set(v___x_2688_, 1, v___y_2686_);
    return v___x_2688_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(
    mut v_x_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2691_ =
        l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(
            v_x_2689_,
            v___y_2690_,
        );
    crate::leanh::lean_dec(v_x_2689_);
    return v_res_2691_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(
    mut v_flb_2727_: u8,
    mut v_items_2728_: *mut crate::leanh::LeanObject,
    mut v_gs_2729_: *mut crate::leanh::LeanObject,
    mut v_w_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2733_: u8 = 0;
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2749_: u8 = 0;
    let mut v_space_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: u8 = 0;
    let mut v_foundLine_2753_: u8 = 0;
    let mut v_space_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2759_: u8 = 0;
    let mut v_foundFlattenedHardLine_2760_: u8 = 0;
    let mut v_space_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v___x_2770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2738_ = crate::leanh::lean_ctor_get(v___y_2731_, 1);
                v___x_2739_ = 0;
                v___x_2740_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2727_, v___x_2739_);
                v___x_2741_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2741_, 0 as u32, v___x_2740_);
                crate::leanh::lean_inc(v_items_2728_);
                v_g_2742_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v_g_2742_, 0, v___x_2741_);
                crate::leanh::lean_ctor_set(v_g_2742_, 1, v_items_2728_);
                crate::leanh::lean_ctor_set_uint8(
                    v_g_2742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2727_,
                );
                v___x_2743_ = crate::leanh::lean_box(0);
                v___x_2744_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2744_, 0, v_g_2742_);
                crate::leanh::lean_ctor_set(v___x_2744_, 1, v___x_2743_);
                v___x_2745_ = lean_nat_sub(v_w_2730_, v_column_2738_);
                crate::leanh::lean_inc(v___x_2745_);
                crate::leanh::lean_inc(v_column_2738_);
                v_r_2746_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2744_,
                    v_column_2738_,
                    v___x_2745_,
                );
                v_foundLine_2753_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_space_2754_ = crate::leanh::lean_ctor_get(v_r_2746_, 0);
                crate::leanh::lean_inc(v_space_2754_);
                v___x_2770_ = lean_nat_dec_lt(v___x_2745_, v_space_2754_);
                if v___x_2770_ == 0 {
                    v___y_2756_ = v_foundLine_2753_;
                    state = 3;
                    continue;
                } else {
                    v___y_2756_ = v___x_2770_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_2734_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2734_, 0 as u32, v___y_2733_);
                v___x_2735_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2734_);
                crate::leanh::lean_ctor_set(v___x_2735_, 1, v_items_2728_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2735_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_flb_2727_,
                );
                v___x_2736_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2736_, 0, v___x_2735_);
                crate::leanh::lean_ctor_set(v___x_2736_, 1, v_gs_2729_);
                v___x_2737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2736_);
                crate::leanh::lean_ctor_set(v___x_2737_, 1, v___y_2731_);
                return v___x_2737_;
            }
            2 => {
                v_foundFlattenedHardLine_2749_ = crate::leanh::lean_ctor_get_uint8(
                    v_r_2746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_r_2746_);
                if v_foundFlattenedHardLine_2749_ == 0 {
                    v_space_2750_ = crate::leanh::lean_ctor_get(v___y_2748_, 0);
                    crate::leanh::lean_inc(v_space_2750_);
                    crate::leanh::lean_dec_ref(v___y_2748_);
                    v___x_2751_ = lean_nat_dec_le(v_space_2750_, v___x_2745_);
                    crate::leanh::lean_dec(v___x_2745_);
                    crate::leanh::lean_dec(v_space_2750_);
                    v___y_2733_ = v___x_2751_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2748_);
                    crate::leanh::lean_dec(v___x_2745_);
                    v___x_2752_ = 0;
                    v___y_2733_ = v___x_2752_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2756_ == 0 {
                    v___x_2757_ = lean_nat_sub(v___x_2745_, v_space_2754_);
                    crate::leanh::lean_inc(v_column_2738_);
                    crate::leanh::lean_inc(v_gs_2729_);
                    v_r_u2082_2758_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2729_,
                            v_column_2738_,
                            v___x_2757_,
                        );
                    v_foundLine_2759_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2758_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2760_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_2758_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2761_ = crate::leanh::lean_ctor_get(v_r_u2082_2758_, 0);
                    v_isSharedCheck_2769_ =
                        (!crate::leanh::lean_is_exclusive(v_r_u2082_2758_)) as u8;
                    if v_isSharedCheck_2769_ == 0 {
                        v___x_2763_ = v_r_u2082_2758_;
                        v_isShared_2764_ = v_isSharedCheck_2769_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_space_2761_);
                        crate::leanh::lean_dec(v_r_u2082_2758_);
                        v___x_2763_ = crate::leanh::lean_box(0);
                        v_isShared_2764_ = v_isSharedCheck_2769_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_space_2754_);
                    crate::leanh::lean_inc_ref(v_r_2746_);
                    v___y_2748_ = v_r_2746_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2765_ = lean_nat_add(v_space_2754_, v_space_2761_);
                crate::leanh::lean_dec(v_space_2761_);
                crate::leanh::lean_dec(v_space_2754_);
                if v_isShared_2764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2763_, 0, v___x_2765_);
                    v___x_2767_ = v___x_2763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2768_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2768_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_foundLine_2759_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2768_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_foundFlattenedHardLine_2760_,
                    );
                    v___x_2767_ = v_reuseFailAlloc_2768_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2748_ = v___x_2767_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(
    mut v_flb_2771_: *mut crate::leanh::LeanObject,
    mut v_items_2772_: *mut crate::leanh::LeanObject,
    mut v_gs_2773_: *mut crate::leanh::LeanObject,
    mut v_w_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flb_boxed_2776_: u8 = 0;
    let mut v_res_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flb_boxed_2776_ = (crate::leanh::lean_unbox(v_flb_2771_) as u8);
    v_res_2777_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_2776_, v_items_2772_, v_gs_2773_, v_w_2774_, v___y_2775_);
    crate::leanh::lean_dec(v_w_2774_);
    return v_res_2777_;
}
pub unsafe fn l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(
    mut v_msg_2792_: *mut crate::leanh::LeanObject,
    mut v___y_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858__overap_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2794_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0;
    v___f_2795_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1;
    v___f_2796_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2;
    v___f_2797_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3;
    v___x_2798_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4;
    v___x_2799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2798_);
    crate::leanh::lean_ctor_set(v___x_2799_, 1, v___f_2794_);
    v___x_2800_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5;
    v___x_2801_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2801_, 0, v___x_2799_);
    crate::leanh::lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    crate::leanh::lean_ctor_set(v___x_2801_, 2, v___f_2795_);
    crate::leanh::lean_ctor_set(v___x_2801_, 3, v___f_2796_);
    crate::leanh::lean_ctor_set(v___x_2801_, 4, v___f_2797_);
    v___x_2802_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6;
    v___x_2803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2801_);
    crate::leanh::lean_ctor_set(v___x_2803_, 1, v___x_2802_);
    v___x_2804_ = crate::leanh::lean_box(0);
    v___x_2805_ = l_instInhabitedOfMonad___redArg(v___x_2803_, v___x_2804_);
    v___x_4858__overap_2806_ = lean_panic_fn_borrowed(v___x_2805_, v_msg_2792_);
    crate::leanh::lean_dec(v___x_2805_);
    v___x_2807_ = crate::leanh::lean_apply_1(v___x_4858__overap_2806_, v___y_2793_);
    return v___x_2807_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(
    mut v_w_2808_: *mut crate::leanh::LeanObject,
    mut v_x_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_fla_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flb_2823_: u8 = 0;
    let mut v_tail_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_f_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v_out_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u32 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u32 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v___y_2867_: u8 = 0;
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v_out_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u32 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_unused_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v_out_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u32 = 0;
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fla_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u8 = 0;
    let mut v_out_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u32 = 0;
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v_unused_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_snd_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_force_2964_: u8 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v_a_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: u32 = 0;
    let mut v_p_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: u8 = 0;
    let mut v_out_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u32 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_is_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v_unused_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut v_indent_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_behavior_3052_: u8 = 0;
    let mut v___x_3053_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_unused_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut v_unused_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2809_) == 0 {
                    v___x_2811_ = crate::leanh::lean_box(0);
                    v___x_2812_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2811_);
                    crate::leanh::lean_ctor_set(v___x_2812_, 1, v___y_2810_);
                    return v___x_2812_;
                } else {
                    v_head_2813_ = crate::leanh::lean_ctor_get(v_x_2809_, 0);
                    v_items_2814_ = crate::leanh::lean_ctor_get(v_head_2813_, 1);
                    crate::leanh::lean_inc(v_items_2814_);
                    if crate::leanh::lean_obj_tag(v_items_2814_) == 0 {
                        v_tail_2815_ = crate::leanh::lean_ctor_get(v_x_2809_, 1);
                        crate::leanh::lean_inc(v_tail_2815_);
                        crate::leanh::lean_dec_ref_known(v_x_2809_, 2);
                        v_x_2809_ = v_tail_2815_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_2813_);
                        v_head_2817_ = crate::leanh::lean_ctor_get(v_items_2814_, 0);
                        crate::leanh::lean_inc(v_head_2817_);
                        v_tail_2818_ = crate::leanh::lean_ctor_get(v_x_2809_, 1);
                        v_isSharedCheck_3088_ = (!crate::leanh::lean_is_exclusive(v_x_2809_)) as u8;
                        if v_isSharedCheck_3088_ == 0 {
                            v_unused_3089_ = crate::leanh::lean_ctor_get(v_x_2809_, 0);
                            crate::leanh::lean_dec(v_unused_3089_);
                            v___x_2820_ = v_x_2809_;
                            v_isShared_2821_ = v_isSharedCheck_3088_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_2818_);
                            crate::leanh::lean_dec(v_x_2809_);
                            v___x_2820_ = crate::leanh::lean_box(0);
                            v_isShared_2821_ = v_isSharedCheck_3088_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2822_ = crate::leanh::lean_ctor_get(v_head_2813_, 0);
                crate::leanh::lean_inc(v_fla_2822_);
                v_flb_2823_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_2813_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec(v_head_2813_);
                v_tail_2824_ = crate::leanh::lean_ctor_get(v_items_2814_, 1);
                v_isSharedCheck_3086_ = (!crate::leanh::lean_is_exclusive(v_items_2814_)) as u8;
                if v_isSharedCheck_3086_ == 0 {
                    v_unused_3087_ = crate::leanh::lean_ctor_get(v_items_2814_, 0);
                    crate::leanh::lean_dec(v_unused_3087_);
                    v___x_2826_ = v_items_2814_;
                    v_isShared_2827_ = v_isSharedCheck_3086_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_2824_);
                    crate::leanh::lean_dec(v_items_2814_);
                    v___x_2826_ = crate::leanh::lean_box(0);
                    v_isShared_2827_ = v_isSharedCheck_3086_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2828_ = crate::leanh::lean_ctor_get(v_head_2817_, 0);
                v_indent_2829_ = crate::leanh::lean_ctor_get(v_head_2817_, 1);
                v_activeTags_2830_ = crate::leanh::lean_ctor_get(v_head_2817_, 2);
                v_isSharedCheck_3085_ = (!crate::leanh::lean_is_exclusive(v_head_2817_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_2832_ = v_head_2817_;
                    v_isShared_2833_ = v_isSharedCheck_3085_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeTags_2830_);
                    crate::leanh::lean_inc(v_indent_2829_);
                    crate::leanh::lean_inc(v_f_2828_);
                    crate::leanh::lean_dec(v_head_2817_);
                    v___x_2832_ = crate::leanh::lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_3085_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_f_2828_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_activeTags_2830_);
                    crate::leanh::lean_dec(v_indent_2829_);
                    crate::leanh::lean_del_object(v___x_2826_);
                    crate::leanh::lean_del_object(v___x_2820_);
                    v___x_2870_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                            v_fla_2822_,
                            v_flb_2823_,
                            v_tail_2818_,
                            v_tail_2824_,
                        );
                    v_x_2809_ = v___x_2870_;
                    state = 0;
                    continue;
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_activeTags_2830_);
                    crate::leanh::lean_del_object(v___x_2826_);
                    crate::leanh::lean_del_object(v___x_2820_);
                    if v_flb_2823_ == 0 {
                        v___x_2872_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                        if v___x_2872_ == 0 {
                            v_out_2873_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                            v_isSharedCheck_2887_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2887_ == 0 {
                                v_unused_2888_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                                crate::leanh::lean_dec(v_unused_2888_);
                                v___x_2875_ = v___y_2810_;
                                v_isShared_2876_ = v_isSharedCheck_2887_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_out_2873_);
                                crate::leanh::lean_dec(v___y_2810_);
                                v___x_2875_ = crate::leanh::lean_box(0);
                                v_isShared_2876_ = v_isSharedCheck_2887_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_indent_2829_);
                            v_out_2889_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                            v_column_2890_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                            v_isSharedCheck_2903_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2903_ == 0 {
                                v___x_2892_ = v___y_2810_;
                                v_isShared_2893_ = v_isSharedCheck_2903_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_column_2890_);
                                crate::leanh::lean_inc(v_out_2889_);
                                crate::leanh::lean_dec(v___y_2810_);
                                v___x_2892_ = crate::leanh::lean_box(0);
                                v_isShared_2893_ = v_isSharedCheck_2903_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_2904_ = l_Int_toNat(v_indent_2829_);
                        crate::leanh::lean_dec(v_indent_2829_);
                        v___x_2905_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                        crate::leanh::lean_dec(v_fla_2822_);
                        if v___x_2905_ == 0 {
                            v_out_2906_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                            v_isSharedCheck_2921_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2921_ == 0 {
                                v_unused_2922_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                                crate::leanh::lean_dec(v_unused_2922_);
                                v___x_2908_ = v___y_2810_;
                                v_isShared_2909_ = v_isSharedCheck_2921_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_out_2906_);
                                crate::leanh::lean_dec(v___y_2810_);
                                v___x_2908_ = crate::leanh::lean_box(0);
                                v_isShared_2909_ = v_isSharedCheck_2921_;
                                state = 13;
                                continue;
                            }
                        } else {
                            v___x_2923_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                            v___x_2924_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                            v___x_2925_ = lean_nat_sub(v_w_2808_, v___x_2924_);
                            crate::leanh::lean_inc(v_tail_2818_);
                            crate::leanh::lean_inc(v_tail_2824_);
                            v___x_2926_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v___x_2925_, v___y_2810_);
                            crate::leanh::lean_dec(v___x_2925_);
                            v_fst_2927_ = crate::leanh::lean_ctor_get(v___x_2926_, 0);
                            crate::leanh::lean_inc(v_fst_2927_);
                            if crate::leanh::lean_obj_tag(v_fst_2927_) == 1 {
                                v_head_2928_ = crate::leanh::lean_ctor_get(v_fst_2927_, 0);
                                v_snd_2929_ = crate::leanh::lean_ctor_get(v___x_2926_, 1);
                                crate::leanh::lean_inc(v_snd_2929_);
                                crate::leanh::lean_dec_ref(v___x_2926_);
                                v_fla_2930_ = crate::leanh::lean_ctor_get(v_head_2928_, 0);
                                v___x_2931_ =
                                    l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2930_);
                                if v___x_2931_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v_fst_2927_, 2);
                                    v_out_2932_ = crate::leanh::lean_ctor_get(v_snd_2929_, 0);
                                    v_isSharedCheck_2947_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_2929_)) as u8;
                                    if v_isSharedCheck_2947_ == 0 {
                                        v_unused_2948_ =
                                            crate::leanh::lean_ctor_get(v_snd_2929_, 1);
                                        crate::leanh::lean_dec(v_unused_2948_);
                                        v___x_2934_ = v_snd_2929_;
                                        v_isShared_2935_ = v_isSharedCheck_2947_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_out_2932_);
                                        crate::leanh::lean_dec(v_snd_2929_);
                                        v___x_2934_ = crate::leanh::lean_box(0);
                                        v_isShared_2935_ = v_isSharedCheck_2947_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2904_);
                                    crate::leanh::lean_dec(v_tail_2824_);
                                    crate::leanh::lean_dec(v_tail_2818_);
                                    v_out_2949_ = crate::leanh::lean_ctor_get(v_snd_2929_, 0);
                                    v_column_2950_ = crate::leanh::lean_ctor_get(v_snd_2929_, 1);
                                    v_isSharedCheck_2960_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_2929_)) as u8;
                                    if v_isSharedCheck_2960_ == 0 {
                                        v___x_2952_ = v_snd_2929_;
                                        v_isShared_2953_ = v_isSharedCheck_2960_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_column_2950_);
                                        crate::leanh::lean_inc(v_out_2949_);
                                        crate::leanh::lean_dec(v_snd_2929_);
                                        v___x_2952_ = crate::leanh::lean_box(0);
                                        v_isShared_2953_ = v_isSharedCheck_2960_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_2927_);
                                crate::leanh::lean_dec(v___x_2904_);
                                crate::leanh::lean_dec(v_tail_2824_);
                                crate::leanh::lean_dec(v_tail_2818_);
                                v_snd_2961_ = crate::leanh::lean_ctor_get(v___x_2926_, 1);
                                crate::leanh::lean_inc(v_snd_2961_);
                                crate::leanh::lean_dec_ref(v___x_2926_);
                                v___x_2962_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0;
                                v___x_2963_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_2962_, v_snd_2961_);
                                return v___x_2963_;
                            }
                        }
                    }
                }
                2 => {
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_activeTags_2830_);
                    crate::leanh::lean_del_object(v___x_2826_);
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_force_2964_ = crate::leanh::lean_ctor_get_uint8(v_f_2828_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_f_2828_, 0);
                    v___x_2965_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                    if v___x_2965_ == 0 {
                        v___y_2867_ = v___x_2965_;
                        state = 8;
                        continue;
                    } else {
                        if v_force_2964_ == 0 {
                            v___y_2867_ = v___x_2965_;
                            state = 8;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    }
                }
                3 => {
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_a_2966_ = crate::leanh::lean_ctor_get(v_f_2828_, 0);
                    v_isSharedCheck_3024_ = (!crate::leanh::lean_is_exclusive(v_f_2828_)) as u8;
                    if v_isSharedCheck_3024_ == 0 {
                        v___x_2968_ = v_f_2828_;
                        v_isShared_2969_ = v_isSharedCheck_3024_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2966_);
                        crate::leanh::lean_dec(v_f_2828_);
                        v___x_2968_ = crate::leanh::lean_box(0);
                        v_isShared_2969_ = v_isSharedCheck_3024_;
                        state = 19;
                        continue;
                    }
                }
                4 => {
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_indent_3025_ = crate::leanh::lean_ctor_get(v_f_2828_, 0);
                    crate::leanh::lean_inc(v_indent_3025_);
                    v_f_3026_ = crate::leanh::lean_ctor_get(v_f_2828_, 1);
                    crate::leanh::lean_inc(v_f_3026_);
                    crate::leanh::lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3027_ = lean_int_add(v_indent_2829_, v_indent_3025_);
                    crate::leanh::lean_dec(v_indent_3025_);
                    crate::leanh::lean_dec(v_indent_2829_);
                    if v_isShared_2833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2832_, 1, v___x_3027_);
                        crate::leanh::lean_ctor_set(v___x_2832_, 0, v_f_3026_);
                        v___x_3029_ = v___x_2832_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_f_3026_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_activeTags_2830_);
                        v___x_3029_ = v_reuseFailAlloc_3035_;
                        state = 27;
                        continue;
                    }
                }
                5 => {
                    v_a_3036_ = crate::leanh::lean_ctor_get(v_f_2828_, 0);
                    crate::leanh::lean_inc(v_a_3036_);
                    v_a_3037_ = crate::leanh::lean_ctor_get(v_f_2828_, 1);
                    crate::leanh::lean_inc(v_a_3037_);
                    crate::leanh::lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3038_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_indent_2829_);
                    if v_isShared_2833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2832_, 2, v___x_3038_);
                        crate::leanh::lean_ctor_set(v___x_2832_, 0, v_a_3036_);
                        v___x_3040_ = v___x_2832_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3050_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_indent_2829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 2, v___x_3038_);
                        v___x_3040_ = v_reuseFailAlloc_3050_;
                        state = 29;
                        continue;
                    }
                }
                6 => {
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_a_3051_ = crate::leanh::lean_ctor_get(v_f_2828_, 0);
                    crate::leanh::lean_inc(v_a_3051_);
                    v_behavior_3052_ = crate::leanh::lean_ctor_get_uint8(
                        v_f_2828_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_f_2828_, 1);
                    v___x_3053_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                    if v___x_3053_ == 0 {
                        if v_isShared_2833_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2832_, 0, v_a_3051_);
                            v___x_3055_ = v___x_2832_;
                            state = 32;
                            continue;
                        } else {
                            v_reuseFailAlloc_3065_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3051_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_indent_2829_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3065_,
                                2,
                                v_activeTags_2830_,
                            );
                            v___x_3055_ = v_reuseFailAlloc_3065_;
                            state = 32;
                            continue;
                        }
                    } else {
                        if v_isShared_2833_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2832_, 0, v_a_3051_);
                            v___x_3067_ = v___x_2832_;
                            state = 34;
                            continue;
                        } else {
                            v_reuseFailAlloc_3073_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3051_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_indent_2829_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3073_,
                                2,
                                v_activeTags_2830_,
                            );
                            v___x_3067_ = v_reuseFailAlloc_3073_;
                            state = 34;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_2820_);
                    v_a_3074_ = crate::leanh::lean_ctor_get(v_f_2828_, 1);
                    crate::leanh::lean_inc(v_a_3074_);
                    crate::leanh::lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3075_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3076_ = lean_nat_add(v_activeTags_2830_, v___x_3075_);
                    crate::leanh::lean_dec(v_activeTags_2830_);
                    if v_isShared_2833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2832_, 2, v___x_3076_);
                        crate::leanh::lean_ctor_set(v___x_2832_, 0, v_a_3074_);
                        v___x_3078_ = v___x_2832_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3074_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_indent_2829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 2, v___x_3076_);
                        v___x_3078_ = v_reuseFailAlloc_3084_;
                        state = 36;
                        continue;
                    }
                }
            },
            4 => {
                v_out_2835_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                v_column_2836_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                v_isSharedCheck_2865_ = (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                if v_isSharedCheck_2865_ == 0 {
                    v___x_2838_ = v___y_2810_;
                    v_isShared_2839_ = v_isSharedCheck_2865_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_2836_);
                    crate::leanh::lean_inc(v_out_2835_);
                    crate::leanh::lean_dec(v___y_2810_);
                    v___x_2838_ = crate::leanh::lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2865_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_column_2836_);
                v___x_2840_ = lean_nat_to_int(v_column_2836_);
                v___x_2841_ = lean_int_dec_lt(v___x_2840_, v_indent_2829_);
                if v___x_2841_ == 0 {
                    crate::leanh::lean_dec(v___x_2840_);
                    crate::leanh::lean_dec(v_column_2836_);
                    v___x_2842_ = l_Int_toNat(v_indent_2829_);
                    crate::leanh::lean_dec(v_indent_2829_);
                    v___x_2843_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                    v___x_2844_ = 32;
                    crate::leanh::lean_inc(v___x_2842_);
                    v___x_2845_ = lean_string_pushn(v___x_2843_, v___x_2844_, v___x_2842_);
                    v___x_2846_ = lean_string_append(v_out_2835_, v___x_2845_);
                    crate::leanh::lean_dec_ref(v___x_2845_);
                    if v_isShared_2839_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2838_, 1, v___x_2842_);
                        crate::leanh::lean_ctor_set(v___x_2838_, 0, v___x_2846_);
                        v___x_2848_ = v___x_2838_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2846_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2842_);
                        v___x_2848_ = v_reuseFailAlloc_2851_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2852_ = l_Std_Format_isEmpty___closed__0;
                    v___x_2853_ = 32;
                    v___x_2854_ = lean_int_sub(v_indent_2829_, v___x_2840_);
                    crate::leanh::lean_dec(v___x_2840_);
                    crate::leanh::lean_dec(v_indent_2829_);
                    v___x_2855_ = l_Int_toNat(v___x_2854_);
                    crate::leanh::lean_dec(v___x_2854_);
                    v___x_2856_ = lean_string_pushn(v___x_2852_, v___x_2853_, v___x_2855_);
                    v___x_2857_ = lean_string_append(v_out_2835_, v___x_2856_);
                    v___x_2858_ = lean_string_length(v___x_2856_);
                    crate::leanh::lean_dec_ref(v___x_2856_);
                    v___x_2859_ = lean_nat_add(v_column_2836_, v___x_2858_);
                    crate::leanh::lean_dec(v___x_2858_);
                    crate::leanh::lean_dec(v_column_2836_);
                    if v_isShared_2839_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2838_, 1, v___x_2859_);
                        crate::leanh::lean_ctor_set(v___x_2838_, 0, v___x_2857_);
                        v___x_2861_ = v___x_2838_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2857_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2859_);
                        v___x_2861_ = v_reuseFailAlloc_2864_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2849_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v_x_2809_ = v___x_2849_;
                v___y_2810_ = v___x_2848_;
                state = 0;
                continue;
            }
            7 => {
                v___x_2862_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v_x_2809_ = v___x_2862_;
                v___y_2810_ = v___x_2861_;
                state = 0;
                continue;
            }
            8 => {
                if v___y_2867_ == 0 {
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_indent_2829_);
                    v___x_2868_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                            v_fla_2822_,
                            v_flb_2823_,
                            v_tail_2818_,
                            v_tail_2824_,
                        );
                    v_x_2809_ = v___x_2868_;
                    state = 0;
                    continue;
                }
            }
            9 => {
                v___x_2877_ = l_Int_toNat(v_indent_2829_);
                crate::leanh::lean_dec(v_indent_2829_);
                v___x_2878_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2879_ = 32;
                crate::leanh::lean_inc(v___x_2877_);
                v___x_2880_ = lean_string_pushn(v___x_2878_, v___x_2879_, v___x_2877_);
                v___x_2881_ = lean_string_append(v_out_2873_, v___x_2880_);
                crate::leanh::lean_dec_ref(v___x_2880_);
                if v_isShared_2876_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2875_, 1, v___x_2877_);
                    crate::leanh::lean_ctor_set(v___x_2875_, 0, v___x_2881_);
                    v___x_2883_ = v___x_2875_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2877_);
                    v___x_2883_ = v_reuseFailAlloc_2886_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2884_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v_x_2809_ = v___x_2884_;
                v___y_2810_ = v___x_2883_;
                state = 0;
                continue;
            }
            11 => {
                v___x_2894_ =
                    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                v___x_2895_ = lean_string_append(v_out_2889_, v___x_2894_);
                v___x_2896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                v___x_2897_ = lean_nat_add(v_column_2890_, v___x_2896_);
                crate::leanh::lean_dec(v_column_2890_);
                if v_isShared_2893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2892_, 1, v___x_2897_);
                    crate::leanh::lean_ctor_set(v___x_2892_, 0, v___x_2895_);
                    v___x_2899_ = v___x_2892_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2897_);
                    v___x_2899_ = v_reuseFailAlloc_2902_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2900_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v_x_2809_ = v___x_2900_;
                v___y_2810_ = v___x_2899_;
                state = 0;
                continue;
            }
            13 => {
                v___x_2910_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2911_ = 32;
                crate::leanh::lean_inc(v___x_2904_);
                v___x_2912_ = lean_string_pushn(v___x_2910_, v___x_2911_, v___x_2904_);
                v___x_2913_ = lean_string_append(v_out_2906_, v___x_2912_);
                crate::leanh::lean_dec_ref(v___x_2912_);
                if v_isShared_2909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2908_, 1, v___x_2904_);
                    crate::leanh::lean_ctor_set(v___x_2908_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2908_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2904_);
                    v___x_2915_ = v_reuseFailAlloc_2920_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2916_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v_w_2808_, v___x_2915_);
                v_fst_2917_ = crate::leanh::lean_ctor_get(v___x_2916_, 0);
                crate::leanh::lean_inc(v_fst_2917_);
                v_snd_2918_ = crate::leanh::lean_ctor_get(v___x_2916_, 1);
                crate::leanh::lean_inc(v_snd_2918_);
                crate::leanh::lean_dec_ref(v___x_2916_);
                v_x_2809_ = v_fst_2917_;
                v___y_2810_ = v_snd_2918_;
                state = 0;
                continue;
            }
            15 => {
                v___x_2936_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2937_ = 32;
                crate::leanh::lean_inc(v___x_2904_);
                v___x_2938_ = lean_string_pushn(v___x_2936_, v___x_2937_, v___x_2904_);
                v___x_2939_ = lean_string_append(v_out_2932_, v___x_2938_);
                crate::leanh::lean_dec_ref(v___x_2938_);
                if v_isShared_2935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2934_, 1, v___x_2904_);
                    crate::leanh::lean_ctor_set(v___x_2934_, 0, v___x_2939_);
                    v___x_2941_ = v___x_2934_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2904_);
                    v___x_2941_ = v_reuseFailAlloc_2946_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2942_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v_w_2808_, v___x_2941_);
                v_fst_2943_ = crate::leanh::lean_ctor_get(v___x_2942_, 0);
                crate::leanh::lean_inc(v_fst_2943_);
                v_snd_2944_ = crate::leanh::lean_ctor_get(v___x_2942_, 1);
                crate::leanh::lean_inc(v_snd_2944_);
                crate::leanh::lean_dec_ref(v___x_2942_);
                v_x_2809_ = v_fst_2943_;
                v___y_2810_ = v_snd_2944_;
                state = 0;
                continue;
            }
            17 => {
                v___x_2954_ = lean_string_append(v_out_2949_, v___x_2923_);
                v___x_2955_ = lean_nat_add(v_column_2950_, v___x_2924_);
                crate::leanh::lean_dec(v_column_2950_);
                if v_isShared_2953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2952_, 1, v___x_2955_);
                    crate::leanh::lean_ctor_set(v___x_2952_, 0, v___x_2954_);
                    v___x_2957_ = v___x_2952_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2955_);
                    v___x_2957_ = v_reuseFailAlloc_2959_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v_x_2809_ = v_fst_2927_;
                v___y_2810_ = v___x_2957_;
                state = 0;
                continue;
            }
            19 => {
                v___x_2970_ = 10;
                crate::leanh::lean_inc_ref(v_a_2966_);
                v_p_2971_ = lean_string_posof(v_a_2966_, v___x_2970_);
                v___x_2972_ = lean_string_utf8_byte_size(v_a_2966_);
                v___x_2973_ = lean_nat_dec_eq(v_p_2971_, v___x_2972_);
                if v___x_2973_ == 0 {
                    v_out_2974_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                    v_isSharedCheck_3008_ = (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v_unused_3009_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                        crate::leanh::lean_dec(v_unused_3009_);
                        v___x_2976_ = v___y_2810_;
                        v_isShared_2977_ = v_isSharedCheck_3008_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_2974_);
                        crate::leanh::lean_dec(v___y_2810_);
                        v___x_2976_ = crate::leanh::lean_box(0);
                        v_isShared_2977_ = v_isSharedCheck_3008_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_2971_);
                    crate::leanh::lean_del_object(v___x_2968_);
                    crate::leanh::lean_del_object(v___x_2832_);
                    crate::leanh::lean_dec(v_activeTags_2830_);
                    crate::leanh::lean_dec(v_indent_2829_);
                    crate::leanh::lean_del_object(v___x_2826_);
                    v_out_3010_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                    v_column_3011_ = crate::leanh::lean_ctor_get(v___y_2810_, 1);
                    v_isSharedCheck_3023_ = (!crate::leanh::lean_is_exclusive(v___y_2810_)) as u8;
                    if v_isSharedCheck_3023_ == 0 {
                        v___x_3013_ = v___y_2810_;
                        v_isShared_3014_ = v_isSharedCheck_3023_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_column_3011_);
                        crate::leanh::lean_inc(v_out_3010_);
                        crate::leanh::lean_dec(v___y_2810_);
                        v___x_3013_ = crate::leanh::lean_box(0);
                        v_isShared_3014_ = v_isSharedCheck_3023_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                v___x_2978_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2979_ = lean_string_utf8_extract(v_a_2966_, v___x_2978_, v_p_2971_);
                v___x_2980_ = lean_string_append(v_out_2974_, v___x_2979_);
                crate::leanh::lean_dec_ref(v___x_2979_);
                v___x_2981_ = l_Int_toNat(v_indent_2829_);
                v___x_2982_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2983_ = 32;
                crate::leanh::lean_inc(v___x_2981_);
                v___x_2984_ = lean_string_pushn(v___x_2982_, v___x_2983_, v___x_2981_);
                v___x_2985_ = lean_string_append(v___x_2980_, v___x_2984_);
                crate::leanh::lean_dec_ref(v___x_2984_);
                if v_isShared_2977_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2976_, 1, v___x_2981_);
                    crate::leanh::lean_ctor_set(v___x_2976_, 0, v___x_2985_);
                    v___x_2987_ = v___x_2976_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2981_);
                    v___x_2987_ = v_reuseFailAlloc_3007_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2988_ = lean_string_utf8_next(v_a_2966_, v_p_2971_);
                crate::leanh::lean_dec(v_p_2971_);
                v___x_2989_ = lean_string_utf8_extract(v_a_2966_, v___x_2988_, v___x_2972_);
                crate::leanh::lean_dec(v___x_2988_);
                crate::leanh::lean_dec_ref(v_a_2966_);
                if v_isShared_2969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2968_, 0, v___x_2989_);
                    v___x_2991_ = v___x_2968_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2989_);
                    v___x_2991_ = v_reuseFailAlloc_3006_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2833_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2832_, 0, v___x_2991_);
                    v___x_2993_ = v___x_2832_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_indent_2829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_activeTags_2830_);
                    v___x_2993_ = v_reuseFailAlloc_3005_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2993_);
                    v_is_2995_ = v___x_2826_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_tail_2824_);
                    v_is_2995_ = v_reuseFailAlloc_3004_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_2996_ = crate::leanh::lean_box(1);
                v___x_2997_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2822_, v___x_2996_);
                if v___x_2997_ == 0 {
                    crate::leanh::lean_dec(v_fla_2822_);
                    v___x_2998_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_is_2995_, v_tail_2818_, v_w_2808_, v___x_2987_);
                    v_fst_2999_ = crate::leanh::lean_ctor_get(v___x_2998_, 0);
                    crate::leanh::lean_inc(v_fst_2999_);
                    v_snd_3000_ = crate::leanh::lean_ctor_get(v___x_2998_, 1);
                    crate::leanh::lean_inc(v_snd_3000_);
                    crate::leanh::lean_dec_ref(v___x_2998_);
                    v_x_2809_ = v_fst_2999_;
                    v___y_2810_ = v_snd_3000_;
                    state = 0;
                    continue;
                } else {
                    v___x_3002_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                            v_fla_2822_,
                            v_flb_2823_,
                            v_tail_2818_,
                            v_is_2995_,
                        );
                    v_x_2809_ = v___x_3002_;
                    v___y_2810_ = v___x_2987_;
                    state = 0;
                    continue;
                }
            }
            25 => {
                v___x_3015_ = lean_string_append(v_out_3010_, v_a_2966_);
                v___x_3016_ = lean_string_length(v_a_2966_);
                crate::leanh::lean_dec_ref(v_a_2966_);
                v___x_3017_ = lean_nat_add(v_column_3011_, v___x_3016_);
                crate::leanh::lean_dec(v___x_3016_);
                crate::leanh::lean_dec(v_column_3011_);
                if v_isShared_3014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3013_, 1, v___x_3017_);
                    crate::leanh::lean_ctor_set(v___x_3013_, 0, v___x_3015_);
                    v___x_3019_ = v___x_3013_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3017_);
                    v___x_3019_ = v_reuseFailAlloc_3022_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3020_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v_x_2809_ = v___x_3020_;
                v___y_2810_ = v___x_3019_;
                state = 0;
                continue;
            }
            27 => {
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_3029_);
                    v___x_3031_ = v___x_2826_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_tail_2824_);
                    v___x_3031_ = v_reuseFailAlloc_3034_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3032_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v___x_3031_,
                );
                v_x_2809_ = v___x_3032_;
                state = 0;
                continue;
            }
            29 => {
                v___x_3041_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3041_, 0, v_a_3037_);
                crate::leanh::lean_ctor_set(v___x_3041_, 1, v_indent_2829_);
                crate::leanh::lean_ctor_set(v___x_3041_, 2, v_activeTags_2830_);
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_3041_);
                    v___x_3043_ = v___x_2826_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_tail_2824_);
                    v___x_3043_ = v_reuseFailAlloc_3049_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_2821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2820_, 1, v___x_3043_);
                    crate::leanh::lean_ctor_set(v___x_2820_, 0, v___x_3040_);
                    v___x_3045_ = v___x_2820_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3043_);
                    v___x_3045_ = v_reuseFailAlloc_3048_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_3046_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v___x_3045_,
                );
                v_x_2809_ = v___x_3046_;
                state = 0;
                continue;
            }
            32 => {
                v___x_3056_ = crate::leanh::lean_box(0);
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 1, v___x_3056_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_3055_);
                    v___x_3058_ = v___x_2826_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3064_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3056_);
                    v___x_3058_ = v_reuseFailAlloc_3064_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_3059_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v_tail_2824_,
                );
                v___x_3060_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_3052_, v___x_3058_, v___x_3059_, v_w_2808_, v___y_2810_);
                v_fst_3061_ = crate::leanh::lean_ctor_get(v___x_3060_, 0);
                crate::leanh::lean_inc(v_fst_3061_);
                v_snd_3062_ = crate::leanh::lean_ctor_get(v___x_3060_, 1);
                crate::leanh::lean_inc(v_snd_3062_);
                crate::leanh::lean_dec_ref(v___x_3060_);
                v_x_2809_ = v_fst_3061_;
                v___y_2810_ = v_snd_3062_;
                state = 0;
                continue;
            }
            34 => {
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_3067_);
                    v___x_3069_ = v___x_2826_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_tail_2824_);
                    v___x_3069_ = v_reuseFailAlloc_3072_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3070_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v___x_3069_,
                );
                v_x_2809_ = v___x_3070_;
                state = 0;
                continue;
            }
            36 => {
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_3078_);
                    v___x_3080_ = v___x_2826_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_tail_2824_);
                    v___x_3080_ = v_reuseFailAlloc_3083_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_3081_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
                    v_fla_2822_,
                    v_flb_2823_,
                    v_tail_2818_,
                    v___x_3080_,
                );
                v_x_2809_ = v___x_3081_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(
    mut v_w_3090_: *mut crate::leanh::LeanObject,
    mut v_x_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3093_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_3090_, v_x_3091_, v___y_3092_);
    crate::leanh::lean_dec(v_w_3090_);
    return v_res_3093_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
    mut v_f_3094_: *mut crate::leanh::LeanObject,
    mut v_w_3095_: *mut crate::leanh::LeanObject,
    mut v_indent_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3098_ = crate::leanh::lean_box(1);
    v___x_3099_ = 0;
    v___x_3100_ = lean_nat_to_int(v_indent_3096_);
    v___x_3101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3102_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3102_, 0, v_f_3094_);
    crate::leanh::lean_ctor_set(v___x_3102_, 1, v___x_3100_);
    crate::leanh::lean_ctor_set(v___x_3102_, 2, v___x_3101_);
    v___x_3103_ = crate::leanh::lean_box(0);
    v___x_3104_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3102_);
    crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3103_);
    v___x_3105_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3105_, 0, v___x_3098_);
    crate::leanh::lean_ctor_set(v___x_3105_, 1, v___x_3104_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3105_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_3099_,
    );
    v___x_3106_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3106_, 0, v___x_3105_);
    crate::leanh::lean_ctor_set(v___x_3106_, 1, v___x_3103_);
    v___x_3107_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_3095_, v___x_3106_, v___y_3097_);
    return v___x_3107_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(
    mut v_f_3108_: *mut crate::leanh::LeanObject,
    mut v_w_3109_: *mut crate::leanh::LeanObject,
    mut v_indent_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3112_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
        v_f_3108_,
        v_w_3109_,
        v_indent_3110_,
        v___y_3111_,
    );
    crate::leanh::lean_dec(v_w_3109_);
    return v_res_3112_;
}
pub unsafe fn l_Std_Format_pretty(
    mut v_f_3113_: *mut crate::leanh::LeanObject,
    mut v_width_3114_: *mut crate::leanh::LeanObject,
    mut v_indent_3115_: *mut crate::leanh::LeanObject,
    mut v_column_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3117_ = l_Std_Format_isEmpty___closed__0;
    v___x_3118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3118_, 0, v___x_3117_);
    crate::leanh::lean_ctor_set(v___x_3118_, 1, v_column_3116_);
    v___x_3119_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
        v_f_3113_,
        v_width_3114_,
        v_indent_3115_,
        v___x_3118_,
    );
    v_snd_3120_ = crate::leanh::lean_ctor_get(v___x_3119_, 1);
    crate::leanh::lean_inc(v_snd_3120_);
    crate::leanh::lean_dec_ref(v___x_3119_);
    v_out_3121_ = crate::leanh::lean_ctor_get(v_snd_3120_, 0);
    crate::leanh::lean_inc_ref(v_out_3121_);
    crate::leanh::lean_dec(v_snd_3120_);
    return v_out_3121_;
}
pub unsafe fn l_Std_Format_pretty___boxed(
    mut v_f_3122_: *mut crate::leanh::LeanObject,
    mut v_width_3123_: *mut crate::leanh::LeanObject,
    mut v_indent_3124_: *mut crate::leanh::LeanObject,
    mut v_column_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Std_Format_pretty(v_f_3122_, v_width_3123_, v_indent_3124_, v_column_3125_);
    crate::leanh::lean_dec(v_width_3123_);
    return v_res_3126_;
}
pub unsafe fn l_Std_instToFormatFormat___lam__0(
    mut v_f_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_f_3127_);
    return v_f_3127_;
}
pub unsafe fn l_Std_instToFormatFormat___lam__0___boxed(
    mut v_f_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_Std_instToFormatFormat___lam__0(v_f_3128_);
    crate::leanh::lean_dec(v_f_3128_);
    return v_res_3129_;
}
pub unsafe fn l_Std_instToFormatString___lam__0(
    mut v_s_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3133_, 0, v_s_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Std_Format_joinSep___redArg___lam__0(
    mut v_x_3136_: *mut crate::leanh::LeanObject,
    mut v_inst_3137_: *mut crate::leanh::LeanObject,
    mut v_x1_3138_: *mut crate::leanh::LeanObject,
    mut v_x2_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3140_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3140_, 0, v_x1_3138_);
    crate::leanh::lean_ctor_set(v___x_3140_, 1, v_x_3136_);
    v___x_3141_ = crate::leanh::lean_apply_1(v_inst_3137_, v_x2_3139_);
    v___x_3142_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3142_, 0, v___x_3140_);
    crate::leanh::lean_ctor_set(v___x_3142_, 1, v___x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_Format_joinSep___redArg(
    mut v_inst_3143_: *mut crate::leanh::LeanObject,
    mut v_x_3144_: *mut crate::leanh::LeanObject,
    mut v_x_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3144_) == 0 {
        let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3145_);
        crate::leanh::lean_dec_ref(v_inst_3143_);
        v___x_3146_ = crate::leanh::lean_box(0);
        return v___x_3146_;
    } else {
        let mut v_tail_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3147_ = crate::leanh::lean_ctor_get(v_x_3144_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3147_) == 0 {
            let mut v_head_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3145_);
            v_head_3148_ = crate::leanh::lean_ctor_get(v_x_3144_, 0);
            crate::leanh::lean_inc(v_head_3148_);
            crate::leanh::lean_dec_ref_known(v_x_3144_, 2);
            v___x_3149_ = crate::leanh::lean_apply_1(v_inst_3143_, v_head_3148_);
            return v___x_3149_;
        } else {
            let mut v_head_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3147_);
            v_head_3150_ = crate::leanh::lean_ctor_get(v_x_3144_, 0);
            crate::leanh::lean_inc(v_head_3150_);
            crate::leanh::lean_dec_ref_known(v_x_3144_, 2);
            crate::leanh::lean_inc_ref(v_inst_3143_);
            v___f_3151_ = crate::leanh::lean_alloc_closure(
                l_Std_Format_joinSep___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                2,
            );
            crate::leanh::lean_closure_set(v___f_3151_, 0, v_x_3145_);
            crate::leanh::lean_closure_set(v___f_3151_, 1, v_inst_3143_);
            v___x_3152_ = crate::leanh::lean_apply_1(v_inst_3143_, v_head_3150_);
            v___x_3153_ = l_List_foldl___redArg(v___f_3151_, v___x_3152_, v_tail_3147_);
            return v___x_3153_;
        }
    }
}
pub unsafe fn l_Std_Format_joinSep(
    mut v_00_u03b1_3154_: *mut crate::leanh::LeanObject,
    mut v_inst_3155_: *mut crate::leanh::LeanObject,
    mut v_x_3156_: *mut crate::leanh::LeanObject,
    mut v_x_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Std_Format_joinSep___redArg(v_inst_3155_, v_x_3156_, v_x_3157_);
    return v___x_3158_;
}
pub unsafe fn l_Std_Format_prefixJoin___redArg___lam__0(
    mut v_pre_3159_: *mut crate::leanh::LeanObject,
    mut v_inst_3160_: *mut crate::leanh::LeanObject,
    mut v_x1_3161_: *mut crate::leanh::LeanObject,
    mut v_x2_3162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3163_, 0, v_x1_3161_);
    crate::leanh::lean_ctor_set(v___x_3163_, 1, v_pre_3159_);
    v___x_3164_ = crate::leanh::lean_apply_1(v_inst_3160_, v_x2_3162_);
    v___x_3165_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3165_, 0, v___x_3163_);
    crate::leanh::lean_ctor_set(v___x_3165_, 1, v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_Format_prefixJoin___redArg(
    mut v_inst_3166_: *mut crate::leanh::LeanObject,
    mut v_pre_3167_: *mut crate::leanh::LeanObject,
    mut v_x_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___f_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3168_) == 0 {
                    crate::leanh::lean_dec(v_pre_3167_);
                    crate::leanh::lean_dec_ref(v_inst_3166_);
                    v___x_3169_ = crate::leanh::lean_box(0);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = crate::leanh::lean_ctor_get(v_x_3168_, 0);
                    v_tail_3171_ = crate::leanh::lean_ctor_get(v_x_3168_, 1);
                    v_isSharedCheck_3181_ = (!crate::leanh::lean_is_exclusive(v_x_3168_)) as u8;
                    if v_isSharedCheck_3181_ == 0 {
                        v___x_3173_ = v_x_3168_;
                        v_isShared_3174_ = v_isSharedCheck_3181_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3171_);
                        crate::leanh::lean_inc(v_head_3170_);
                        crate::leanh::lean_dec(v_x_3168_);
                        v___x_3173_ = crate::leanh::lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3181_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_3166_);
                crate::leanh::lean_inc(v_pre_3167_);
                v___f_3175_ = crate::leanh::lean_alloc_closure(
                    l_Std_Format_prefixJoin___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3175_, 0, v_pre_3167_);
                crate::leanh::lean_closure_set(v___f_3175_, 1, v_inst_3166_);
                v___x_3176_ = crate::leanh::lean_apply_1(v_inst_3166_, v_head_3170_);
                if v_isShared_3174_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3173_, 5);
                    crate::leanh::lean_ctor_set(v___x_3173_, 1, v___x_3176_);
                    crate::leanh::lean_ctor_set(v___x_3173_, 0, v_pre_3167_);
                    v___x_3178_ = v___x_3173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_pre_3167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3176_);
                    v___x_3178_ = v_reuseFailAlloc_3180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3179_ = l_List_foldl___redArg(v___f_3175_, v___x_3178_, v_tail_3171_);
                return v___x_3179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_prefixJoin(
    mut v_00_u03b1_3182_: *mut crate::leanh::LeanObject,
    mut v_inst_3183_: *mut crate::leanh::LeanObject,
    mut v_pre_3184_: *mut crate::leanh::LeanObject,
    mut v_x_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_Std_Format_prefixJoin___redArg(v_inst_3183_, v_pre_3184_, v_x_3185_);
    return v___x_3186_;
}
pub unsafe fn l_Std_Format_joinSuffix___redArg___lam__0(
    mut v_inst_3187_: *mut crate::leanh::LeanObject,
    mut v_x_3188_: *mut crate::leanh::LeanObject,
    mut v_x1_3189_: *mut crate::leanh::LeanObject,
    mut v_x2_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = crate::leanh::lean_apply_1(v_inst_3187_, v_x2_3190_);
    v___x_3192_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3192_, 0, v_x1_3189_);
    crate::leanh::lean_ctor_set(v___x_3192_, 1, v___x_3191_);
    v___x_3193_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    crate::leanh::lean_ctor_set(v___x_3193_, 1, v_x_3188_);
    return v___x_3193_;
}
pub unsafe fn l_Std_Format_joinSuffix___redArg(
    mut v_inst_3194_: *mut crate::leanh::LeanObject,
    mut v_x_3195_: *mut crate::leanh::LeanObject,
    mut v_x_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___f_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3195_) == 0 {
                    crate::leanh::lean_dec(v_x_3196_);
                    crate::leanh::lean_dec_ref(v_inst_3194_);
                    v___x_3197_ = crate::leanh::lean_box(0);
                    return v___x_3197_;
                } else {
                    v_head_3198_ = crate::leanh::lean_ctor_get(v_x_3195_, 0);
                    v_tail_3199_ = crate::leanh::lean_ctor_get(v_x_3195_, 1);
                    v_isSharedCheck_3209_ = (!crate::leanh::lean_is_exclusive(v_x_3195_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3201_ = v_x_3195_;
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3199_);
                        crate::leanh::lean_inc(v_head_3198_);
                        crate::leanh::lean_dec(v_x_3195_);
                        v___x_3201_ = crate::leanh::lean_box(0);
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3196_);
                crate::leanh::lean_inc_ref(v_inst_3194_);
                v___f_3203_ = crate::leanh::lean_alloc_closure(
                    l_Std_Format_joinSuffix___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3203_, 0, v_inst_3194_);
                crate::leanh::lean_closure_set(v___f_3203_, 1, v_x_3196_);
                v___x_3204_ = crate::leanh::lean_apply_1(v_inst_3194_, v_head_3198_);
                if v_isShared_3202_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3201_, 5);
                    crate::leanh::lean_ctor_set(v___x_3201_, 1, v_x_3196_);
                    crate::leanh::lean_ctor_set(v___x_3201_, 0, v___x_3204_);
                    v___x_3206_ = v___x_3201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_x_3196_);
                    v___x_3206_ = v_reuseFailAlloc_3208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3207_ = l_List_foldl___redArg(v___f_3203_, v___x_3206_, v_tail_3199_);
                return v___x_3207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSuffix(
    mut v_00_u03b1_3210_: *mut crate::leanh::LeanObject,
    mut v_inst_3211_: *mut crate::leanh::LeanObject,
    mut v_x_3212_: *mut crate::leanh::LeanObject,
    mut v_x_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3214_ = l_Std_Format_joinSuffix___redArg(v_inst_3211_, v_x_3212_, v_x_3213_);
    return v___x_3214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Format_instInhabitedFlattenBehavior_default =
        _init_l_Std_Format_instInhabitedFlattenBehavior_default();
    l_Std_Format_instInhabitedFlattenBehavior = _init_l_Std_Format_instInhabitedFlattenBehavior();
    l_Std_instInhabitedFormat_default = _init_l_Std_instInhabitedFormat_default();
    crate::leanh::lean_mark_persistent(l_Std_instInhabitedFormat_default);
    l_Std_instInhabitedFormat = _init_l_Std_instInhabitedFormat();
    crate::leanh::lean_mark_persistent(l_Std_instInhabitedFormat);
    l_Std_Format_defIndent = _init_l_Std_Format_defIndent();
    crate::leanh::lean_mark_persistent(l_Std_Format_defIndent);
    l_Std_Format_defUnicode = _init_l_Std_Format_defUnicode();
    l_Std_Format_defWidth = _init_l_Std_Format_defWidth();
    crate::leanh::lean_mark_persistent(l_Std_Format_defWidth);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Format_Basic(builtin);
}
