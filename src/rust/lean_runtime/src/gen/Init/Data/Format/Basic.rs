// Lean compiler output
// Module: Init.Data.Format.Basic
// Imports: Init.Data.Int.Basic Init.Data.String.Bootstrap Init.Control.State Init.Data.Nat.Bitwise.Basic
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_lt, lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_length, lean_string_offsetofpos, lean_string_posof,
    lean_string_pushn, lean_string_utf8_extract, lean_string_utf8_next,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static mut l_Std_Format_instInhabitedFlattenBehavior_default: u8 = 0;
pub static mut l_Std_Format_instInhabitedFlattenBehavior: u8 = 0;
pub static l_Std_Format_instBEqFlattenBehavior___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Format_instBEqFlattenBehavior_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Format_instBEqFlattenBehavior___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenBehavior___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Format_instBEqFlattenBehavior: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenBehavior___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instInhabitedFormat_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_instInhabitedFormat: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Format_isEmpty___closed__0_value: LeanStringObject<1> = LeanStringObject {
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
static mut l_Std_Format_isEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_isEmpty___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_instAppend___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Format_instAppend___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Format_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instAppend___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Format_instAppend: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instAppend___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_instCoeString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Format_instCoeString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Format_instCoeString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instCoeString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Format_instCoeString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instCoeString___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_join___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Format_isEmpty___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Format_join___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_join___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_instInhabitedSpaceResult_default___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Std_Format_instInhabitedSpaceResult_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Format_instInhabitedSpaceResult_default: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut LeanObject;
pub static mut l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult:
    *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instInhabitedSpaceResult_default___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value
) as *mut LeanObject;
pub static l_Std_Format_instBEqFlattenAllowability___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Format_instBEqFlattenAllowability_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Format_instBEqFlattenAllowability___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenAllowability___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Format_instBEqFlattenAllowability: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_instBEqFlattenAllowability___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value:
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
    m_data: [32, 0],
};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value
) as *mut LeanObject;
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Format_paren___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Format_paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_paren___closed__1_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Format_paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__1_value) as *mut LeanObject;
static mut l_Std_Format_paren___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Format_paren___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Format_paren___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Format_paren___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Format_paren___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Format_paren___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Format_paren___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__4_value) as *mut LeanObject;
pub static l_Std_Format_paren___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Format_paren___closed__1_value) as *mut LeanObject],
};
static mut l_Std_Format_paren___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_paren___closed__5_value) as *mut LeanObject;
pub static l_Std_Format_sbracket___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Format_sbracket___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__0_value) as *mut LeanObject;
pub static l_Std_Format_sbracket___closed__1_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Std_Format_sbracket___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__1_value) as *mut LeanObject;
static mut l_Std_Format_sbracket___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Format_sbracket___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Format_sbracket___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Format_sbracket___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Format_sbracket___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Format_sbracket___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Format_sbracket___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__4_value) as *mut LeanObject;
pub static l_Std_Format_sbracket___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Std_Format_sbracket___closed__1_value) as *mut LeanObject],
};
static mut l_Std_Format_sbracket___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Format_sbracket___closed__5_value) as *mut LeanObject;
pub static mut l_Std_Format_defIndent: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Format_defUnicode: u8 = 0;
pub static mut l_Std_Format_defWidth: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Format_nestD___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Format_nestD___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_get as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value: LeanClosureObject<7> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*7) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 7, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value) as *mut LeanObject] };
static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value) as *mut LeanObject;
pub static mut l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_map as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_pure as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value) as *mut LeanObject] };
static mut l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value) as *mut LeanObject;
pub static l_Std_instToFormatFormat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instToFormatFormat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatFormat___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instToFormatFormat: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatFormat___closed__0_value) as *mut LeanObject;
pub static l_Std_instToFormatString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_instToFormatString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instToFormatString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatString___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instToFormatString: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToFormatString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Format_FlattenBehavior_ctorIdx(mut v_x_1608_: u8) -> *mut LeanObject {
    if v_x_1608_ == 0 {
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        v___x_1609_ = lean_unsigned_to_nat(0);
        return v___x_1609_;
    } else {
        let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
        v___x_1610_ = lean_unsigned_to_nat(1);
        return v___x_1610_;
    }
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorIdx___boxed(
    mut v_x_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1612_: u8 = 0;
    let mut v_res_1613_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1612_ = (lean_unbox(v_x_1611_) as u8);
    v_res_1613_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_boxed_1612_);
    return v_res_1613_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_toCtorIdx(mut v_x_1614_: u8) -> *mut LeanObject {
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_toCtorIdx___boxed(
    mut v_x_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1617_ = (lean_unbox(v_x_1616_) as u8);
    v_res_1618_ = l_Std_Format_FlattenBehavior_toCtorIdx(v_x_4__boxed_1617_);
    return v_res_1618_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___redArg(
    mut v_k_1619_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1619_);
    return v_k_1619_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(
    mut v_k_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1621_: *mut LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Std_Format_FlattenBehavior_ctorElim___redArg(v_k_1620_);
    lean_dec(v_k_1620_);
    return v_res_1621_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim(
    mut v_motive_1622_: *mut LeanObject,
    mut v_ctorIdx_1623_: *mut LeanObject,
    mut v_t_1624_: u8,
    mut v_h_1625_: *mut LeanObject,
    mut v_k_1626_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1626_);
    return v_k_1626_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_ctorElim___boxed(
    mut v_motive_1627_: *mut LeanObject,
    mut v_ctorIdx_1628_: *mut LeanObject,
    mut v_t_1629_: *mut LeanObject,
    mut v_h_1630_: *mut LeanObject,
    mut v_k_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1632_: u8 = 0;
    let mut v_res_1633_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1632_ = (lean_unbox(v_t_1629_) as u8);
    v_res_1633_ = l_Std_Format_FlattenBehavior_ctorElim(
        v_motive_1627_,
        v_ctorIdx_1628_,
        v_t_boxed_1632_,
        v_h_1630_,
        v_k_1631_,
    );
    lean_dec(v_k_1631_);
    lean_dec(v_ctorIdx_1628_);
    return v_res_1633_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(
    mut v_allOrNone_1634_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_allOrNone_1634_);
    return v_allOrNone_1634_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(
    mut v_allOrNone_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1636_: *mut LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(v_allOrNone_1635_);
    lean_dec(v_allOrNone_1635_);
    return v_res_1636_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim(
    mut v_motive_1637_: *mut LeanObject,
    mut v_t_1638_: u8,
    mut v_h_1639_: *mut LeanObject,
    mut v_allOrNone_1640_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_allOrNone_1640_);
    return v_allOrNone_1640_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(
    mut v_motive_1641_: *mut LeanObject,
    mut v_t_1642_: *mut LeanObject,
    mut v_h_1643_: *mut LeanObject,
    mut v_allOrNone_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1645_ = (lean_unbox(v_t_1642_) as u8);
    v_res_1646_ = l_Std_Format_FlattenBehavior_allOrNone_elim(
        v_motive_1641_,
        v_t_boxed_1645_,
        v_h_1643_,
        v_allOrNone_1644_,
    );
    lean_dec(v_allOrNone_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___redArg(
    mut v_fill_1647_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fill_1647_);
    return v_fill_1647_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(
    mut v_fill_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Std_Format_FlattenBehavior_fill_elim___redArg(v_fill_1648_);
    lean_dec(v_fill_1648_);
    return v_res_1649_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim(
    mut v_motive_1650_: *mut LeanObject,
    mut v_t_1651_: u8,
    mut v_h_1652_: *mut LeanObject,
    mut v_fill_1653_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fill_1653_);
    return v_fill_1653_;
}
pub unsafe fn l_Std_Format_FlattenBehavior_fill_elim___boxed(
    mut v_motive_1654_: *mut LeanObject,
    mut v_t_1655_: *mut LeanObject,
    mut v_h_1656_: *mut LeanObject,
    mut v_fill_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1658_: u8 = 0;
    let mut v_res_1659_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1658_ = (lean_unbox(v_t_1655_) as u8);
    v_res_1659_ = l_Std_Format_FlattenBehavior_fill_elim(
        v_motive_1654_,
        v_t_boxed_1658_,
        v_h_1656_,
        v_fill_1657_,
    );
    lean_dec(v_fill_1657_);
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
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    v___x_1664_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_1662_);
    v___x_1665_ = l_Std_Format_FlattenBehavior_ctorIdx(v_y_1663_);
    v___x_1666_ = lean_nat_dec_eq(v___x_1664_, v___x_1665_);
    lean_dec(v___x_1665_);
    lean_dec(v___x_1664_);
    return v___x_1666_;
}
pub unsafe fn l_Std_Format_instBEqFlattenBehavior_beq___boxed(
    mut v_x_1667_: *mut LeanObject,
    mut v_y_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_1669_: u8 = 0;
    let mut v_y_18__boxed_1670_: u8 = 0;
    let mut v_res_1671_: u8 = 0;
    let mut v_r_1672_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1669_ = (lean_unbox(v_x_1667_) as u8);
    v_y_18__boxed_1670_ = (lean_unbox(v_y_1668_) as u8);
    v_res_1671_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_17__boxed_1669_, v_y_18__boxed_1670_);
    v_r_1672_ = lean_box((v_res_1671_) as usize);
    return v_r_1672_;
}
pub unsafe fn l_Std_Format_ctorIdx(mut v_x_1675_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1675_) {
        0 => {
            let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
            v___x_1676_ = lean_unsigned_to_nat(0);
            return v___x_1676_;
        }
        1 => {
            let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
            v___x_1677_ = lean_unsigned_to_nat(1);
            return v___x_1677_;
        }
        2 => {
            let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
            v___x_1678_ = lean_unsigned_to_nat(2);
            return v___x_1678_;
        }
        3 => {
            let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
            v___x_1679_ = lean_unsigned_to_nat(3);
            return v___x_1679_;
        }
        4 => {
            let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
            v___x_1680_ = lean_unsigned_to_nat(4);
            return v___x_1680_;
        }
        5 => {
            let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
            v___x_1681_ = lean_unsigned_to_nat(5);
            return v___x_1681_;
        }
        6 => {
            let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
            v___x_1682_ = lean_unsigned_to_nat(6);
            return v___x_1682_;
        }
        _ => {
            let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
            v___x_1683_ = lean_unsigned_to_nat(7);
            return v___x_1683_;
        }
    }
}
pub unsafe fn l_Std_Format_ctorIdx___boxed(mut v_x_1684_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1685_: *mut LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Std_Format_ctorIdx(v_x_1684_);
    lean_dec(v_x_1684_);
    return v_res_1685_;
}
pub unsafe fn l_Std_Format_ctorElim___redArg(
    mut v_t_1686_: *mut LeanObject,
    mut v_k_1687_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1686_) {
        2 => {
            let mut v_force_1688_: u8 = 0;
            let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
            v_force_1688_ = lean_ctor_get_uint8(v_t_1686_, 0 as u32);
            lean_dec_ref_known(v_t_1686_, 0);
            v___x_1689_ = lean_box((v_force_1688_) as usize);
            v___x_1690_ = lean_apply_1(v_k_1687_, v___x_1689_);
            return v___x_1690_;
        }
        3 => {
            let mut v_a_1691_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
            v_a_1691_ = lean_ctor_get(v_t_1686_, 0);
            lean_inc_ref(v_a_1691_);
            lean_dec_ref_known(v_t_1686_, 1);
            v___x_1692_ = lean_apply_1(v_k_1687_, v_a_1691_);
            return v___x_1692_;
        }
        4 => {
            let mut v_indent_1693_: *mut LeanObject = core::ptr::null_mut();
            let mut v_f_1694_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
            v_indent_1693_ = lean_ctor_get(v_t_1686_, 0);
            lean_inc(v_indent_1693_);
            v_f_1694_ = lean_ctor_get(v_t_1686_, 1);
            lean_inc(v_f_1694_);
            lean_dec_ref_known(v_t_1686_, 2);
            v___x_1695_ = lean_apply_2(v_k_1687_, v_indent_1693_, v_f_1694_);
            return v___x_1695_;
        }
        5 => {
            let mut v_a_1696_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
            v_a_1696_ = lean_ctor_get(v_t_1686_, 0);
            lean_inc(v_a_1696_);
            v_a_1697_ = lean_ctor_get(v_t_1686_, 1);
            lean_inc(v_a_1697_);
            lean_dec_ref_known(v_t_1686_, 2);
            v___x_1698_ = lean_apply_2(v_k_1687_, v_a_1696_, v_a_1697_);
            return v___x_1698_;
        }
        6 => {
            let mut v_a_1699_: *mut LeanObject = core::ptr::null_mut();
            let mut v_behavior_1700_: u8 = 0;
            let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
            v_a_1699_ = lean_ctor_get(v_t_1686_, 0);
            lean_inc(v_a_1699_);
            v_behavior_1700_ = lean_ctor_get_uint8(
                v_t_1686_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_1686_, 1);
            v___x_1701_ = lean_box((v_behavior_1700_) as usize);
            v___x_1702_ = lean_apply_2(v_k_1687_, v_a_1699_, v___x_1701_);
            return v___x_1702_;
        }
        7 => {
            let mut v_a_1703_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1704_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
            v_a_1703_ = lean_ctor_get(v_t_1686_, 0);
            lean_inc(v_a_1703_);
            v_a_1704_ = lean_ctor_get(v_t_1686_, 1);
            lean_inc(v_a_1704_);
            lean_dec_ref_known(v_t_1686_, 2);
            v___x_1705_ = lean_apply_2(v_k_1687_, v_a_1703_, v_a_1704_);
            return v___x_1705_;
        }
        _ => {
            lean_dec(v_t_1686_);
            return v_k_1687_;
        }
    }
}
pub unsafe fn l_Std_Format_ctorElim(
    mut v_motive_1706_: *mut LeanObject,
    mut v_ctorIdx_1707_: *mut LeanObject,
    mut v_t_1708_: *mut LeanObject,
    mut v_h_1709_: *mut LeanObject,
    mut v_k_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1711_ = l_Std_Format_ctorElim___redArg(v_t_1708_, v_k_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Format_ctorElim___boxed(
    mut v_motive_1712_: *mut LeanObject,
    mut v_ctorIdx_1713_: *mut LeanObject,
    mut v_t_1714_: *mut LeanObject,
    mut v_h_1715_: *mut LeanObject,
    mut v_k_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1717_: *mut LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Std_Format_ctorElim(
        v_motive_1712_,
        v_ctorIdx_1713_,
        v_t_1714_,
        v_h_1715_,
        v_k_1716_,
    );
    lean_dec(v_ctorIdx_1713_);
    return v_res_1717_;
}
pub unsafe fn l_Std_Format_nil_elim___redArg(
    mut v_t_1718_: *mut LeanObject,
    mut v_nil_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Std_Format_ctorElim___redArg(v_t_1718_, v_nil_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Std_Format_nil_elim(
    mut v_motive_1721_: *mut LeanObject,
    mut v_t_1722_: *mut LeanObject,
    mut v_h_1723_: *mut LeanObject,
    mut v_nil_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1725_ = l_Std_Format_ctorElim___redArg(v_t_1722_, v_nil_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_Format_line_elim___redArg(
    mut v_t_1726_: *mut LeanObject,
    mut v_line_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Std_Format_ctorElim___redArg(v_t_1726_, v_line_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Std_Format_line_elim(
    mut v_motive_1729_: *mut LeanObject,
    mut v_t_1730_: *mut LeanObject,
    mut v_h_1731_: *mut LeanObject,
    mut v_line_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Std_Format_ctorElim___redArg(v_t_1730_, v_line_1732_);
    return v___x_1733_;
}
pub unsafe fn l_Std_Format_align_elim___redArg(
    mut v_t_1734_: *mut LeanObject,
    mut v_align_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = l_Std_Format_ctorElim___redArg(v_t_1734_, v_align_1735_);
    return v___x_1736_;
}
pub unsafe fn l_Std_Format_align_elim(
    mut v_motive_1737_: *mut LeanObject,
    mut v_t_1738_: *mut LeanObject,
    mut v_h_1739_: *mut LeanObject,
    mut v_align_1740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Std_Format_ctorElim___redArg(v_t_1738_, v_align_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Format_text_elim___redArg(
    mut v_t_1742_: *mut LeanObject,
    mut v_text_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Std_Format_ctorElim___redArg(v_t_1742_, v_text_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_Format_text_elim(
    mut v_motive_1745_: *mut LeanObject,
    mut v_t_1746_: *mut LeanObject,
    mut v_h_1747_: *mut LeanObject,
    mut v_text_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    v___x_1749_ = l_Std_Format_ctorElim___redArg(v_t_1746_, v_text_1748_);
    return v___x_1749_;
}
pub unsafe fn l_Std_Format_nest_elim___redArg(
    mut v_t_1750_: *mut LeanObject,
    mut v_nest_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    v___x_1752_ = l_Std_Format_ctorElim___redArg(v_t_1750_, v_nest_1751_);
    return v___x_1752_;
}
pub unsafe fn l_Std_Format_nest_elim(
    mut v_motive_1753_: *mut LeanObject,
    mut v_t_1754_: *mut LeanObject,
    mut v_h_1755_: *mut LeanObject,
    mut v_nest_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Std_Format_ctorElim___redArg(v_t_1754_, v_nest_1756_);
    return v___x_1757_;
}
pub unsafe fn l_Std_Format_append_elim___redArg(
    mut v_t_1758_: *mut LeanObject,
    mut v_append_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1760_ = l_Std_Format_ctorElim___redArg(v_t_1758_, v_append_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Std_Format_append_elim(
    mut v_motive_1761_: *mut LeanObject,
    mut v_t_1762_: *mut LeanObject,
    mut v_h_1763_: *mut LeanObject,
    mut v_append_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Std_Format_ctorElim___redArg(v_t_1762_, v_append_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_Format_group_elim___redArg(
    mut v_t_1766_: *mut LeanObject,
    mut v_group_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_Format_ctorElim___redArg(v_t_1766_, v_group_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Std_Format_group_elim(
    mut v_motive_1769_: *mut LeanObject,
    mut v_t_1770_: *mut LeanObject,
    mut v_h_1771_: *mut LeanObject,
    mut v_group_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Std_Format_ctorElim___redArg(v_t_1770_, v_group_1772_);
    return v___x_1773_;
}
pub unsafe fn l_Std_Format_tag_elim___redArg(
    mut v_t_1774_: *mut LeanObject,
    mut v_tag_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_1776_ = l_Std_Format_ctorElim___redArg(v_t_1774_, v_tag_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Std_Format_tag_elim(
    mut v_motive_1777_: *mut LeanObject,
    mut v_t_1778_: *mut LeanObject,
    mut v_h_1779_: *mut LeanObject,
    mut v_tag_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Std_Format_ctorElim___redArg(v_t_1778_, v_tag_1780_);
    return v___x_1781_;
}
pub unsafe fn _init_l_Std_instInhabitedFormat_default() -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    v___x_1782_ = lean_box(0);
    return v___x_1782_;
}
pub unsafe fn _init_l_Std_instInhabitedFormat() -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = lean_box(0);
    return v___x_1783_;
}
pub unsafe fn l_Std_Format_isEmpty(mut v_x_1785_: *mut LeanObject) -> u8 {
    let mut v___x_1786_: u8 = 0;
    let mut v_a_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v_f_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v_a_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1785_) {
                1 => {
                    v___x_1786_ = 0;
                    return v___x_1786_;
                }
                3 => {
                    v_a_1787_ = lean_ctor_get(v_x_1785_, 0);
                    v___x_1788_ = l_Std_Format_isEmpty___closed__0;
                    v___x_1789_ = lean_string_dec_eq(v_a_1787_, v___x_1788_);
                    return v___x_1789_;
                }
                4 => {
                    v_f_1790_ = lean_ctor_get(v_x_1785_, 1);
                    v_x_1785_ = v_f_1790_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_1792_ = lean_ctor_get(v_x_1785_, 0);
                    v_a_1793_ = lean_ctor_get(v_x_1785_, 1);
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
                    v_a_1796_ = lean_ctor_get(v_x_1785_, 0);
                    v_x_1785_ = v_a_1796_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_a_1798_ = lean_ctor_get(v_x_1785_, 1);
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
pub unsafe fn l_Std_Format_isEmpty___boxed(mut v_x_1801_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1802_: u8 = 0;
    let mut v_r_1803_: *mut LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Std_Format_isEmpty(v_x_1801_);
    lean_dec(v_x_1801_);
    v_r_1803_ = lean_box((v_res_1802_) as usize);
    return v_r_1803_;
}
pub unsafe fn l_Std_Format_fill(mut v_f_1804_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    v___x_1805_ = 1;
    v___x_1806_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1806_, 0, v_f_1804_);
    lean_ctor_set_uint8(
        v___x_1806_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1805_,
    );
    return v___x_1806_;
}
pub unsafe fn l_Std_Format_instAppend___lam__0(
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    v___x_1809_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1809_, 0, v_a_1807_);
    lean_ctor_set(v___x_1809_, 1, v_a_1808_);
    return v___x_1809_;
}
pub unsafe fn l_Std_Format_instCoeString___lam__0(
    mut v_a_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    v___x_1813_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1813_, 0, v_a_1812_);
    return v___x_1813_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_join_spec__0(
    mut v_x_1816_: *mut LeanObject,
    mut v_x_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1817_) == 0 {
                    return v_x_1816_;
                } else {
                    v_head_1818_ = lean_ctor_get(v_x_1817_, 0);
                    v_tail_1819_ = lean_ctor_get(v_x_1817_, 1);
                    v_isSharedCheck_1827_ = (!lean_is_exclusive(v_x_1817_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1821_ = v_x_1817_;
                        v_isShared_1822_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1819_);
                        lean_inc(v_head_1818_);
                        lean_dec(v_x_1817_);
                        v___x_1821_ = lean_box(0);
                        v_isShared_1822_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1822_ == 0 {
                    lean_ctor_set_tag(v___x_1821_, 5);
                    lean_ctor_set(v___x_1821_, 1, v_head_1818_);
                    lean_ctor_set(v___x_1821_, 0, v_x_1816_);
                    v___x_1824_ = v___x_1821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_x_1816_);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_head_1818_);
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
pub unsafe fn l_Std_Format_join(mut v_xs_1830_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = l_Std_Format_join___closed__0;
    v___x_1832_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_1831_, v_xs_1830_);
    return v___x_1832_;
}
pub unsafe fn l_Std_Format_isNil(mut v_x_1833_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1833_) == 0 {
        let mut v___x_1834_: u8 = 0;
        v___x_1834_ = 1;
        return v___x_1834_;
    } else {
        let mut v___x_1835_: u8 = 0;
        v___x_1835_ = 0;
        return v___x_1835_;
    }
}
pub unsafe fn l_Std_Format_isNil___boxed(mut v_x_1836_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1837_: u8 = 0;
    let mut v_r_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Std_Format_isNil(v_x_1836_);
    lean_dec(v_x_1836_);
    v_r_1838_ = lean_box((v_res_1837_) as usize);
    return v_r_1838_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_merge(
    mut v_w_1844_: *mut LeanObject,
    mut v_r_u2081_1845_: *mut LeanObject,
    mut v_r_u2082_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_foundLine_1847_: u8 = 0;
    let mut v_space_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1853_: u8 = 0;
    let mut v_foundFlattenedHardLine_1854_: u8 = 0;
    let mut v_space_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_foundLine_1847_ = lean_ctor_get_uint8(
                    v_r_u2081_1845_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_space_1848_ = lean_ctor_get(v_r_u2081_1845_, 0);
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
                    v_r_u2082_1852_ = lean_apply_1(v_r_u2082_1846_, v___x_1851_);
                    v_foundLine_1853_ = lean_ctor_get_uint8(
                        v_r_u2082_1852_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_1854_ = lean_ctor_get_uint8(
                        v_r_u2082_1852_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_1855_ = lean_ctor_get(v_r_u2082_1852_, 0);
                    v_isSharedCheck_1863_ = (!lean_is_exclusive(v_r_u2082_1852_)) as u8;
                    if v_isSharedCheck_1863_ == 0 {
                        v___x_1857_ = v_r_u2082_1852_;
                        v_isShared_1858_ = v_isSharedCheck_1863_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_space_1855_);
                        lean_dec(v_r_u2082_1852_);
                        v___x_1857_ = lean_box(0);
                        v_isShared_1858_ = v_isSharedCheck_1863_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_r_u2082_1846_);
                    lean_inc_ref(v_r_u2081_1845_);
                    return v_r_u2081_1845_;
                }
            }
            2 => {
                v___x_1859_ = lean_nat_add(v_space_1848_, v_space_1855_);
                lean_dec(v_space_1855_);
                if v_isShared_1858_ == 0 {
                    lean_ctor_set(v___x_1857_, 0, v___x_1859_);
                    v___x_1861_ = v___x_1857_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_foundLine_1853_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1862_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
    mut v_w_1865_: *mut LeanObject,
    mut v_r_u2081_1866_: *mut LeanObject,
    mut v_r_u2082_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1868_: *mut LeanObject = core::ptr::null_mut();
    v_res_1868_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(
        v_w_1865_,
        v_r_u2081_1866_,
        v_r_u2082_1867_,
    );
    lean_dec_ref(v_r_u2081_1866_);
    lean_dec(v_w_1865_);
    return v_res_1868_;
}
pub unsafe fn l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(
    mut v_a_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_nat_to_int(v_a_1869_);
    return v___x_1870_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
    mut v_x_1874_: *mut LeanObject,
    mut v_x_1875_: u8,
    mut v_x_1876_: *mut LeanObject,
    mut v_x_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: u8 = 0;
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_force_1893_: u8 = 0;
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: u32 = 0;
    let mut v_p_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_off_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: u8 = 0;
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: u8 = 0;
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: u8 = 0;
    let mut v_indent_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1916_: u8 = 0;
    let mut v_space_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1919_: u8 = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_1922_: u8 = 0;
    let mut v_foundFlattenedHardLine_1923_: u8 = 0;
    let mut v_space_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v___x_1933_: u8 = 0;
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1874_) {
                0 => {
                    lean_dec(v_x_1877_);
                    lean_dec(v_x_1876_);
                    v___x_1888_ = l_Std_Format_instInhabitedSpaceResult_default___closed__0;
                    return v___x_1888_;
                }
                1 => {
                    lean_dec(v_x_1877_);
                    lean_dec(v_x_1876_);
                    if v_x_1875_ == 0 {
                        v___x_1889_ = 1;
                        v___x_1890_ = lean_unsigned_to_nat(0);
                        v___x_1891_ = lean_alloc_ctor(0, 1, (2) as u32);
                        lean_ctor_set(v___x_1891_, 0, v___x_1890_);
                        lean_ctor_set_uint8(
                            v___x_1891_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1889_,
                        );
                        lean_ctor_set_uint8(
                            v___x_1891_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
                        lean_dec_ref_known(v_x_1874_, 0);
                        v___y_1879_ = v_x_1875_;
                        state = 1;
                        continue;
                    } else {
                        v_force_1893_ = lean_ctor_get_uint8(v_x_1874_, 0 as u32);
                        lean_dec_ref_known(v_x_1874_, 0);
                        if v_force_1893_ == 0 {
                            lean_dec(v_x_1877_);
                            lean_dec(v_x_1876_);
                            v___x_1894_ = lean_unsigned_to_nat(0);
                            v___x_1895_ = lean_alloc_ctor(0, 1, (2) as u32);
                            lean_ctor_set(v___x_1895_, 0, v___x_1894_);
                            lean_ctor_set_uint8(
                                v___x_1895_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v_force_1893_,
                            );
                            lean_ctor_set_uint8(
                                v___x_1895_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
                    lean_dec(v_x_1877_);
                    lean_dec(v_x_1876_);
                    v_a_1897_ = lean_ctor_get(v_x_1874_, 0);
                    lean_inc_ref_n(v_a_1897_, 3);
                    lean_dec_ref_known(v_x_1874_, 1);
                    v___x_1898_ = 10;
                    v_p_1899_ = lean_string_posof(v_a_1897_, v___x_1898_);
                    lean_inc(v_p_1899_);
                    v_off_1900_ = lean_string_offsetofpos(v_a_1897_, v_p_1899_);
                    v___x_1905_ = lean_string_utf8_byte_size(v_a_1897_);
                    lean_dec_ref(v_a_1897_);
                    v___x_1906_ = lean_nat_dec_eq(v_p_1899_, v___x_1905_);
                    lean_dec(v_p_1899_);
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
                    v_indent_1909_ = lean_ctor_get(v_x_1874_, 0);
                    lean_inc(v_indent_1909_);
                    v_f_1910_ = lean_ctor_get(v_x_1874_, 1);
                    lean_inc(v_f_1910_);
                    lean_dec_ref_known(v_x_1874_, 2);
                    v___x_1911_ = lean_int_sub(v_x_1876_, v_indent_1909_);
                    lean_dec(v_indent_1909_);
                    lean_dec(v_x_1876_);
                    v_x_1874_ = v_f_1910_;
                    v_x_1876_ = v___x_1911_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_1913_ = lean_ctor_get(v_x_1874_, 0);
                    lean_inc(v_a_1913_);
                    v_a_1914_ = lean_ctor_get(v_x_1874_, 1);
                    lean_inc(v_a_1914_);
                    lean_dec_ref_known(v_x_1874_, 2);
                    lean_inc(v_x_1877_);
                    lean_inc(v_x_1876_);
                    v___x_1915_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                        v_a_1913_, v_x_1875_, v_x_1876_, v_x_1877_,
                    );
                    v_foundLine_1916_ = lean_ctor_get_uint8(
                        v___x_1915_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_space_1917_ = lean_ctor_get(v___x_1915_, 0);
                    lean_inc(v_space_1917_);
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
                    v_a_1934_ = lean_ctor_get(v_x_1874_, 0);
                    lean_inc(v_a_1934_);
                    lean_dec_ref_known(v_x_1874_, 1);
                    v___x_1935_ = 1;
                    v_x_1874_ = v_a_1934_;
                    v_x_1875_ = v___x_1935_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1937_ = lean_ctor_get(v_x_1874_, 1);
                    lean_inc(v_a_1937_);
                    lean_dec_ref_known(v_x_1874_, 2);
                    v_x_1874_ = v_a_1937_;
                    state = 0;
                    continue;
                }
            },
            1 => {
                v___x_1880_ = lean_nat_to_int(v_x_1877_);
                v___x_1881_ = lean_int_dec_lt(v___x_1880_, v_x_1876_);
                if v___x_1881_ == 0 {
                    lean_dec(v___x_1880_);
                    lean_dec(v_x_1876_);
                    v___x_1882_ = 1;
                    v___x_1883_ = lean_unsigned_to_nat(0);
                    v___x_1884_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                    lean_ctor_set_uint8(
                        v___x_1884_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1882_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1884_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___y_1879_,
                    );
                    return v___x_1884_;
                } else {
                    v___x_1885_ = lean_int_sub(v_x_1876_, v___x_1880_);
                    lean_dec(v___x_1880_);
                    lean_dec(v_x_1876_);
                    v___x_1886_ = l_Int_toNat(v___x_1885_);
                    lean_dec(v___x_1885_);
                    v___x_1887_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_1887_, 0, v___x_1886_);
                    lean_ctor_set_uint8(
                        v___x_1887_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___y_1879_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1887_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___y_1879_,
                    );
                    return v___x_1887_;
                }
            }
            2 => {
                if v_x_1875_ == 0 {
                    v___x_1903_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_1903_, 0, v_off_1900_);
                    lean_ctor_set_uint8(
                        v___x_1903_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___y_1902_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1903_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_x_1875_,
                    );
                    return v___x_1903_;
                } else {
                    v___x_1904_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_1904_, 0, v_off_1900_);
                    lean_ctor_set_uint8(
                        v___x_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___y_1902_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___y_1902_,
                    );
                    return v___x_1904_;
                }
            }
            3 => {
                if v___y_1919_ == 0 {
                    lean_dec_ref(v___x_1915_);
                    v___x_1920_ = lean_nat_sub(v_x_1877_, v_space_1917_);
                    lean_dec(v_x_1877_);
                    v_r_u2082_1921_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                            v_a_1914_,
                            v_x_1875_,
                            v_x_1876_,
                            v___x_1920_,
                        );
                    v_foundLine_1922_ = lean_ctor_get_uint8(
                        v_r_u2082_1921_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_1923_ = lean_ctor_get_uint8(
                        v_r_u2082_1921_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_1924_ = lean_ctor_get(v_r_u2082_1921_, 0);
                    v_isSharedCheck_1932_ = (!lean_is_exclusive(v_r_u2082_1921_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v___x_1926_ = v_r_u2082_1921_;
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_space_1924_);
                        lean_dec(v_r_u2082_1921_);
                        v___x_1926_ = lean_box(0);
                        v_isShared_1927_ = v_isSharedCheck_1932_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_space_1917_);
                    lean_dec(v_a_1914_);
                    lean_dec(v_x_1877_);
                    lean_dec(v_x_1876_);
                    return v___x_1915_;
                }
            }
            4 => {
                v___x_1928_ = lean_nat_add(v_space_1917_, v_space_1924_);
                lean_dec(v_space_1924_);
                lean_dec(v_space_1917_);
                if v_isShared_1927_ == 0 {
                    lean_ctor_set(v___x_1926_, 0, v___x_1928_);
                    v___x_1930_ = v___x_1926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1931_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_foundLine_1922_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1931_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
    mut v_x_1939_: *mut LeanObject,
    mut v_x_1940_: *mut LeanObject,
    mut v_x_1941_: *mut LeanObject,
    mut v_x_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_415__boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_x_415__boxed_1943_ = (lean_unbox(v_x_1940_) as u8);
    v_res_1944_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
        v_x_1939_,
        v_x_415__boxed_1943_,
        v_x_1941_,
        v_x_1942_,
    );
    return v_res_1944_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorIdx(
    mut v_x_1945_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1945_) == 0 {
        let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
        v___x_1946_ = lean_unsigned_to_nat(0);
        return v___x_1946_;
    } else {
        let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
        v___x_1947_ = lean_unsigned_to_nat(1);
        return v___x_1947_;
    }
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorIdx___boxed(
    mut v_x_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_1948_);
    lean_dec(v_x_1948_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___redArg(
    mut v_t_1950_: *mut LeanObject,
    mut v_k_1951_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1950_) == 0 {
        let mut v_fits_1952_: u8 = 0;
        let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        v_fits_1952_ = lean_ctor_get_uint8(v_t_1950_, 0 as u32);
        v___x_1953_ = lean_box((v_fits_1952_) as usize);
        v___x_1954_ = lean_apply_1(v_k_1951_, v___x_1953_);
        return v___x_1954_;
    } else {
        return v_k_1951_;
    }
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(
    mut v_t_1955_: *mut LeanObject,
    mut v_k_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1957_: *mut LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1955_, v_k_1956_);
    lean_dec(v_t_1955_);
    return v_res_1957_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim(
    mut v_motive_1958_: *mut LeanObject,
    mut v_ctorIdx_1959_: *mut LeanObject,
    mut v_t_1960_: *mut LeanObject,
    mut v_h_1961_: *mut LeanObject,
    mut v_k_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v___x_1963_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1960_, v_k_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_ctorElim___boxed(
    mut v_motive_1964_: *mut LeanObject,
    mut v_ctorIdx_1965_: *mut LeanObject,
    mut v_t_1966_: *mut LeanObject,
    mut v_h_1967_: *mut LeanObject,
    mut v_k_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1969_: *mut LeanObject = core::ptr::null_mut();
    v_res_1969_ = l_Std_Format_FlattenAllowability_ctorElim(
        v_motive_1964_,
        v_ctorIdx_1965_,
        v_t_1966_,
        v_h_1967_,
        v_k_1968_,
    );
    lean_dec(v_t_1966_);
    lean_dec(v_ctorIdx_1965_);
    return v_res_1969_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___redArg(
    mut v_t_1970_: *mut LeanObject,
    mut v_allow_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1970_, v_allow_1971_);
    return v___x_1972_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(
    mut v_t_1973_: *mut LeanObject,
    mut v_allow_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_1973_, v_allow_1974_);
    lean_dec(v_t_1973_);
    return v_res_1975_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim(
    mut v_motive_1976_: *mut LeanObject,
    mut v_t_1977_: *mut LeanObject,
    mut v_h_1978_: *mut LeanObject,
    mut v_allow_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1977_, v_allow_1979_);
    return v___x_1980_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_allow_elim___boxed(
    mut v_motive_1981_: *mut LeanObject,
    mut v_t_1982_: *mut LeanObject,
    mut v_h_1983_: *mut LeanObject,
    mut v_allow_1984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1985_: *mut LeanObject = core::ptr::null_mut();
    v_res_1985_ = l_Std_Format_FlattenAllowability_allow_elim(
        v_motive_1981_,
        v_t_1982_,
        v_h_1983_,
        v_allow_1984_,
    );
    lean_dec(v_t_1982_);
    return v_res_1985_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___redArg(
    mut v_t_1986_: *mut LeanObject,
    mut v_disallow_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1986_, v_disallow_1987_);
    return v___x_1988_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(
    mut v_t_1989_: *mut LeanObject,
    mut v_disallow_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_res_1991_ =
        l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_1989_, v_disallow_1990_);
    lean_dec(v_t_1989_);
    return v_res_1991_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim(
    mut v_motive_1992_: *mut LeanObject,
    mut v_t_1993_: *mut LeanObject,
    mut v_h_1994_: *mut LeanObject,
    mut v_disallow_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_1993_, v_disallow_1995_);
    return v___x_1996_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_disallow_elim___boxed(
    mut v_motive_1997_: *mut LeanObject,
    mut v_t_1998_: *mut LeanObject,
    mut v_h_1999_: *mut LeanObject,
    mut v_disallow_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2001_: *mut LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Std_Format_FlattenAllowability_disallow_elim(
        v_motive_1997_,
        v_t_1998_,
        v_h_1999_,
        v_disallow_2000_,
    );
    lean_dec(v_t_1998_);
    return v_res_2001_;
}
pub unsafe fn l_Std_Format_instBEqFlattenAllowability_beq(
    mut v_x_2002_: *mut LeanObject,
    mut v_x_2003_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2002_) == 0 {
        if lean_obj_tag(v_x_2003_) == 0 {
            let mut v_fits_2004_: u8 = 0;
            v_fits_2004_ = lean_ctor_get_uint8(v_x_2002_, 0 as u32);
            if v_fits_2004_ == 0 {
                let mut v_fits_2005_: u8 = 0;
                v_fits_2005_ = lean_ctor_get_uint8(v_x_2003_, 0 as u32);
                if v_fits_2005_ == 0 {
                    let mut v___x_2006_: u8 = 0;
                    v___x_2006_ = 1;
                    return v___x_2006_;
                } else {
                    return v_fits_2004_;
                }
            } else {
                let mut v_fits_2007_: u8 = 0;
                v_fits_2007_ = lean_ctor_get_uint8(v_x_2003_, 0 as u32);
                return v_fits_2007_;
            }
        } else {
            let mut v___x_2008_: u8 = 0;
            v___x_2008_ = 0;
            return v___x_2008_;
        }
    } else {
        if lean_obj_tag(v_x_2003_) == 1 {
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
    mut v_x_2011_: *mut LeanObject,
    mut v_x_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut LeanObject = core::ptr::null_mut();
    v_res_2013_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_2011_, v_x_2012_);
    lean_dec(v_x_2012_);
    lean_dec(v_x_2011_);
    v_r_2014_ = lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn l_Std_Format_FlattenAllowability_shouldFlatten(mut v_x_2017_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_2017_) == 0 {
        let mut v_fits_2018_: u8 = 0;
        v_fits_2018_ = lean_ctor_get_uint8(v_x_2017_, 0 as u32);
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
    mut v_x_2021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2022_: u8 = 0;
    let mut v_r_2023_: *mut LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_2021_);
    lean_dec(v_x_2021_);
    v_r_2023_ = lean_box((v_res_2022_) as usize);
    return v_r_2023_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
    mut v_x_2024_: *mut LeanObject,
    mut v_x_2025_: *mut LeanObject,
    mut v_x_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fla_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_flb_2035_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v_tail_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v_f_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indent_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2051_: u8 = 0;
    let mut v_space_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: u8 = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2061_: u8 = 0;
    let mut v_foundFlattenedHardLine_2062_: u8 = 0;
    let mut v_space_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v_unused_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2024_) == 0 {
                    lean_dec(v_x_2026_);
                    lean_dec(v_x_2025_);
                    v___x_2027_ = l_Std_Format_instInhabitedSpaceResult_default___closed__0;
                    return v___x_2027_;
                } else {
                    v_head_2028_ = lean_ctor_get(v_x_2024_, 0);
                    lean_inc(v_head_2028_);
                    v_items_2029_ = lean_ctor_get(v_head_2028_, 1);
                    lean_inc(v_items_2029_);
                    if lean_obj_tag(v_items_2029_) == 0 {
                        lean_dec(v_head_2028_);
                        v_tail_2030_ = lean_ctor_get(v_x_2024_, 1);
                        lean_inc(v_tail_2030_);
                        lean_dec_ref_known(v_x_2024_, 2);
                        v_x_2024_ = v_tail_2030_;
                        state = 0;
                        continue;
                    } else {
                        v_head_2032_ = lean_ctor_get(v_items_2029_, 0);
                        lean_inc(v_head_2032_);
                        v_tail_2033_ = lean_ctor_get(v_x_2024_, 1);
                        lean_inc(v_tail_2033_);
                        lean_dec_ref_known(v_x_2024_, 2);
                        v_fla_2034_ = lean_ctor_get(v_head_2028_, 0);
                        v_flb_2035_ = lean_ctor_get_uint8(
                            v_head_2028_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_2077_ = (!lean_is_exclusive(v_head_2028_)) as u8;
                        if v_isSharedCheck_2077_ == 0 {
                            v_unused_2078_ = lean_ctor_get(v_head_2028_, 1);
                            lean_dec(v_unused_2078_);
                            v___x_2037_ = v_head_2028_;
                            v_isShared_2038_ = v_isSharedCheck_2077_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_fla_2034_);
                            lean_dec(v_head_2028_);
                            v___x_2037_ = lean_box(0);
                            v_isShared_2038_ = v_isSharedCheck_2077_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_tail_2039_ = lean_ctor_get(v_items_2029_, 1);
                v_isSharedCheck_2075_ = (!lean_is_exclusive(v_items_2029_)) as u8;
                if v_isSharedCheck_2075_ == 0 {
                    v_unused_2076_ = lean_ctor_get(v_items_2029_, 0);
                    lean_dec(v_unused_2076_);
                    v___x_2041_ = v_items_2029_;
                    v_isShared_2042_ = v_isSharedCheck_2075_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_tail_2039_);
                    lean_dec(v_items_2029_);
                    v___x_2041_ = lean_box(0);
                    v_isShared_2042_ = v_isSharedCheck_2075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2043_ = lean_ctor_get(v_head_2032_, 0);
                lean_inc(v_f_2043_);
                v_indent_2044_ = lean_ctor_get(v_head_2032_, 1);
                lean_inc(v_indent_2044_);
                lean_dec(v_head_2032_);
                v___x_2045_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2034_);
                lean_inc_n(v_x_2026_, 2);
                v___x_2046_ = lean_nat_to_int(v_x_2026_);
                lean_inc(v_x_2025_);
                v___x_2047_ = lean_nat_to_int(v_x_2025_);
                v___x_2048_ = lean_int_add(v___x_2046_, v___x_2047_);
                lean_dec(v___x_2047_);
                lean_dec(v___x_2046_);
                v___x_2049_ = lean_int_sub(v___x_2048_, v_indent_2044_);
                lean_dec(v_indent_2044_);
                lean_dec(v___x_2048_);
                v___x_2050_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(
                    v_f_2043_,
                    v___x_2045_,
                    v___x_2049_,
                    v_x_2026_,
                );
                v_foundLine_2051_ = lean_ctor_get_uint8(
                    v___x_2050_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_space_2052_ = lean_ctor_get(v___x_2050_, 0);
                lean_inc(v_space_2052_);
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 1, v_tail_2039_);
                    v___x_2054_ = v___x_2037_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fla_2034_);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_tail_2039_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2074_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_flb_2035_,
                    );
                    v___x_2054_ = v_reuseFailAlloc_2074_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2042_ == 0 {
                    lean_ctor_set(v___x_2041_, 1, v_tail_2033_);
                    lean_ctor_set(v___x_2041_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2041_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2054_);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_tail_2033_);
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
                    lean_dec_ref(v___x_2050_);
                    v___x_2059_ = lean_nat_sub(v_x_2026_, v_space_2052_);
                    lean_dec(v_x_2026_);
                    v_r_u2082_2060_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v___x_2056_,
                            v_x_2025_,
                            v___x_2059_,
                        );
                    v_foundLine_2061_ = lean_ctor_get_uint8(
                        v_r_u2082_2060_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2062_ = lean_ctor_get_uint8(
                        v_r_u2082_2060_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2063_ = lean_ctor_get(v_r_u2082_2060_, 0);
                    v_isSharedCheck_2071_ = (!lean_is_exclusive(v_r_u2082_2060_)) as u8;
                    if v_isSharedCheck_2071_ == 0 {
                        v___x_2065_ = v_r_u2082_2060_;
                        v_isShared_2066_ = v_isSharedCheck_2071_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_space_2063_);
                        lean_dec(v_r_u2082_2060_);
                        v___x_2065_ = lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2071_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2056_);
                    lean_dec(v_space_2052_);
                    lean_dec(v_x_2026_);
                    lean_dec(v_x_2025_);
                    return v___x_2050_;
                }
            }
            6 => {
                v___x_2067_ = lean_nat_add(v_space_2052_, v_space_2063_);
                lean_dec(v_space_2063_);
                lean_dec(v_space_2052_);
                if v_isShared_2066_ == 0 {
                    lean_ctor_set(v___x_2065_, 0, v___x_2067_);
                    v___x_2069_ = v___x_2065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2070_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_foundLine_2061_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2070_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
    mut v_items_2080_: *mut LeanObject,
    mut v_w_2081_: *mut LeanObject,
    mut v_gs_2082_: *mut LeanObject,
    mut v_toPure_2083_: *mut LeanObject,
    mut v_k_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2086_: u8 = 0;
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2101_: u8 = 0;
    let mut v_space_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2104_: u8 = 0;
    let mut v_foundLine_2105_: u8 = 0;
    let mut v_space_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2111_: u8 = 0;
    let mut v_foundFlattenedHardLine_2112_: u8 = 0;
    let mut v_space_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2091_ = 0;
                v___x_2092_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2079_, v___x_2091_);
                v___x_2093_ = lean_alloc_ctor(0, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2093_, 0 as u32, v___x_2092_);
                lean_inc(v_items_2080_);
                v_g_2094_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v_g_2094_, 0, v___x_2093_);
                lean_ctor_set(v_g_2094_, 1, v_items_2080_);
                lean_ctor_set_uint8(
                    v_g_2094_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_flb_2079_,
                );
                v___x_2095_ = lean_box(0);
                v___x_2096_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2096_, 0, v_g_2094_);
                lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                v___x_2097_ = lean_nat_sub(v_w_2081_, v_k_2084_);
                lean_inc(v___x_2097_);
                lean_inc(v_k_2084_);
                v_r_2098_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2096_,
                    v_k_2084_,
                    v___x_2097_,
                );
                v_foundLine_2105_ = lean_ctor_get_uint8(
                    v_r_2098_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_space_2106_ = lean_ctor_get(v_r_2098_, 0);
                lean_inc(v_space_2106_);
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
                v___x_2087_ = lean_alloc_ctor(0, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2087_, 0 as u32, v___y_2086_);
                v___x_2088_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                lean_ctor_set(v___x_2088_, 1, v_items_2080_);
                lean_ctor_set_uint8(
                    v___x_2088_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_flb_2079_,
                );
                v___x_2089_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2089_, 0, v___x_2088_);
                lean_ctor_set(v___x_2089_, 1, v_gs_2082_);
                v___x_2090_ = lean_apply_2(v_toPure_2083_, lean_box(0), v___x_2089_);
                return v___x_2090_;
            }
            2 => {
                v_foundFlattenedHardLine_2101_ = lean_ctor_get_uint8(
                    v_r_2098_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                lean_dec_ref(v_r_2098_);
                if v_foundFlattenedHardLine_2101_ == 0 {
                    v_space_2102_ = lean_ctor_get(v___y_2100_, 0);
                    lean_inc(v_space_2102_);
                    lean_dec_ref(v___y_2100_);
                    v___x_2103_ = lean_nat_dec_le(v_space_2102_, v___x_2097_);
                    lean_dec(v___x_2097_);
                    lean_dec(v_space_2102_);
                    v___y_2086_ = v___x_2103_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_2100_);
                    lean_dec(v___x_2097_);
                    v___x_2104_ = 0;
                    v___y_2086_ = v___x_2104_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2108_ == 0 {
                    v___x_2109_ = lean_nat_sub(v___x_2097_, v_space_2106_);
                    lean_inc(v_gs_2082_);
                    v_r_u2082_2110_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2082_,
                            v_k_2084_,
                            v___x_2109_,
                        );
                    v_foundLine_2111_ = lean_ctor_get_uint8(
                        v_r_u2082_2110_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2112_ = lean_ctor_get_uint8(
                        v_r_u2082_2110_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2113_ = lean_ctor_get(v_r_u2082_2110_, 0);
                    v_isSharedCheck_2121_ = (!lean_is_exclusive(v_r_u2082_2110_)) as u8;
                    if v_isSharedCheck_2121_ == 0 {
                        v___x_2115_ = v_r_u2082_2110_;
                        v_isShared_2116_ = v_isSharedCheck_2121_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_space_2113_);
                        lean_dec(v_r_u2082_2110_);
                        v___x_2115_ = lean_box(0);
                        v_isShared_2116_ = v_isSharedCheck_2121_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_space_2106_);
                    lean_dec(v_k_2084_);
                    lean_inc_ref(v_r_2098_);
                    v___y_2100_ = v_r_2098_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2117_ = lean_nat_add(v_space_2106_, v_space_2113_);
                lean_dec(v_space_2113_);
                lean_dec(v_space_2106_);
                if v_isShared_2116_ == 0 {
                    lean_ctor_set(v___x_2115_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2115_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2120_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_foundLine_2111_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2120_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
    mut v_flb_2123_: *mut LeanObject,
    mut v_items_2124_: *mut LeanObject,
    mut v_w_2125_: *mut LeanObject,
    mut v_gs_2126_: *mut LeanObject,
    mut v_toPure_2127_: *mut LeanObject,
    mut v_k_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_boxed_2129_: u8 = 0;
    let mut v_res_2130_: *mut LeanObject = core::ptr::null_mut();
    v_flb_boxed_2129_ = (lean_unbox(v_flb_2123_) as u8);
    v_res_2130_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(
        v_flb_boxed_2129_,
        v_items_2124_,
        v_w_2125_,
        v_gs_2126_,
        v_toPure_2127_,
        v_k_2128_,
    );
    lean_dec(v_w_2125_);
    return v_res_2130_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
    mut v_flb_2131_: u8,
    mut v_items_2132_: *mut LeanObject,
    mut v_gs_2133_: *mut LeanObject,
    mut v_w_2134_: *mut LeanObject,
    mut v_inst_2135_: *mut LeanObject,
    mut v_inst_2136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currColumn_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2137_ = lean_ctor_get(v_inst_2135_, 0);
    lean_inc_ref(v_toApplicative_2137_);
    v_toBind_2138_ = lean_ctor_get(v_inst_2135_, 1);
    lean_inc(v_toBind_2138_);
    lean_dec_ref(v_inst_2135_);
    v_currColumn_2139_ = lean_ctor_get(v_inst_2136_, 2);
    lean_inc(v_currColumn_2139_);
    lean_dec_ref(v_inst_2136_);
    v_toPure_2140_ = lean_ctor_get(v_toApplicative_2137_, 1);
    lean_inc(v_toPure_2140_);
    lean_dec_ref(v_toApplicative_2137_);
    v___x_2141_ = lean_box((v_flb_2131_) as usize);
    v___f_2142_ = lean_alloc_closure(
        l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2142_, 0, v___x_2141_);
    lean_closure_set(v___f_2142_, 1, v_items_2132_);
    lean_closure_set(v___f_2142_, 2, v_w_2134_);
    lean_closure_set(v___f_2142_, 3, v_gs_2133_);
    lean_closure_set(v___f_2142_, 4, v_toPure_2140_);
    v___x_2143_ = lean_apply_4(
        v_toBind_2138_,
        lean_box(0),
        lean_box(0),
        v_currColumn_2139_,
        v___f_2142_,
    );
    return v___x_2143_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(
    mut v_flb_2144_: *mut LeanObject,
    mut v_items_2145_: *mut LeanObject,
    mut v_gs_2146_: *mut LeanObject,
    mut v_w_2147_: *mut LeanObject,
    mut v_inst_2148_: *mut LeanObject,
    mut v_inst_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_boxed_2150_: u8 = 0;
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
    v_flb_boxed_2150_ = (lean_unbox(v_flb_2144_) as u8);
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
    mut v_m_2152_: *mut LeanObject,
    mut v_flb_2153_: u8,
    mut v_items_2154_: *mut LeanObject,
    mut v_gs_2155_: *mut LeanObject,
    mut v_w_2156_: *mut LeanObject,
    mut v_inst_2157_: *mut LeanObject,
    mut v_inst_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_2160_: *mut LeanObject,
    mut v_flb_2161_: *mut LeanObject,
    mut v_items_2162_: *mut LeanObject,
    mut v_gs_2163_: *mut LeanObject,
    mut v_w_2164_: *mut LeanObject,
    mut v_inst_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_boxed_2167_: u8 = 0;
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_flb_boxed_2167_ = (lean_unbox(v_flb_2161_) as u8);
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
    mut v_fla_2169_: *mut LeanObject,
    mut v_flb_2170_: u8,
    mut v_tail_2171_: *mut LeanObject,
    mut v_is_x27_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    v___x_2173_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_2173_, 0, v_fla_2169_);
    lean_ctor_set(v___x_2173_, 1, v_is_x27_2172_);
    lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_flb_2170_,
    );
    v___x_2174_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2174_, 0, v___x_2173_);
    lean_ctor_set(v___x_2174_, 1, v_tail_2171_);
    return v___x_2174_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(
    mut v_fla_2175_: *mut LeanObject,
    mut v_flb_2176_: *mut LeanObject,
    mut v_tail_2177_: *mut LeanObject,
    mut v_is_x27_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_1984__boxed_2179_: u8 = 0;
    let mut v_res_2180_: *mut LeanObject = core::ptr::null_mut();
    v_flb_1984__boxed_2179_ = (lean_unbox(v_flb_2176_) as u8);
    v_res_2180_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(
        v_fla_2175_,
        v_flb_1984__boxed_2179_,
        v_tail_2177_,
        v_is_x27_2178_,
    );
    return v_res_2180_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(
    mut v_endTags_2181_: *mut LeanObject,
    mut v_activeTags_2182_: *mut LeanObject,
    mut v_toBind_2183_: *mut LeanObject,
    mut v___f_2184_: *mut LeanObject,
    mut v_____r_2185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2186_ = lean_apply_1(v_endTags_2181_, v_activeTags_2182_);
    v___x_2187_ = lean_apply_4(
        v_toBind_2183_,
        lean_box(0),
        lean_box(0),
        v___x_2186_,
        v___f_2184_,
    );
    return v___x_2187_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(
    mut v_indent_2188_: *mut LeanObject,
    mut v_pushNewline_2189_: *mut LeanObject,
    mut v_toBind_2190_: *mut LeanObject,
    mut v___f_2191_: *mut LeanObject,
    mut v_____r_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ = l_Int_toNat(v_indent_2188_);
    v___x_2194_ = lean_apply_1(v_pushNewline_2189_, v___x_2193_);
    v___x_2195_ = lean_apply_4(
        v_toBind_2190_,
        lean_box(0),
        lean_box(0),
        v___x_2194_,
        v___f_2191_,
    );
    return v___x_2195_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(
    mut v_indent_2196_: *mut LeanObject,
    mut v_pushNewline_2197_: *mut LeanObject,
    mut v_toBind_2198_: *mut LeanObject,
    mut v___f_2199_: *mut LeanObject,
    mut v_____r_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v_res_2201_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(
        v_indent_2196_,
        v_pushNewline_2197_,
        v_toBind_2198_,
        v___f_2199_,
        v_____r_2200_,
    );
    lean_dec(v_indent_2196_);
    return v_res_2201_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(
    mut v_indent_2202_: *mut LeanObject,
    mut v_inst_2203_: *mut LeanObject,
    mut v_toBind_2204_: *mut LeanObject,
    mut v___f_2205_: *mut LeanObject,
    mut v___f_2206_: *mut LeanObject,
    mut v_k_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    v___x_2208_ = lean_nat_to_int(v_k_2207_);
    v___x_2209_ = lean_int_dec_lt(v___x_2208_, v_indent_2202_);
    if v___x_2209_ == 0 {
        let mut v_pushNewline_2210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2208_);
        lean_dec(v___f_2206_);
        v_pushNewline_2210_ = lean_ctor_get(v_inst_2203_, 1);
        lean_inc(v_pushNewline_2210_);
        lean_dec_ref(v_inst_2203_);
        v___x_2211_ = l_Int_toNat(v_indent_2202_);
        v___x_2212_ = lean_apply_1(v_pushNewline_2210_, v___x_2211_);
        v___x_2213_ = lean_apply_4(
            v_toBind_2204_,
            lean_box(0),
            lean_box(0),
            v___x_2212_,
            v___f_2205_,
        );
        return v___x_2213_;
    } else {
        let mut v_pushOutput_2214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2216_: u32 = 0;
        let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2205_);
        v_pushOutput_2214_ = lean_ctor_get(v_inst_2203_, 0);
        lean_inc(v_pushOutput_2214_);
        lean_dec_ref(v_inst_2203_);
        v___x_2215_ = l_Std_Format_isEmpty___closed__0;
        v___x_2216_ = 32;
        v___x_2217_ = lean_int_sub(v_indent_2202_, v___x_2208_);
        lean_dec(v___x_2208_);
        v___x_2218_ = l_Int_toNat(v___x_2217_);
        lean_dec(v___x_2217_);
        v___x_2219_ = lean_string_pushn(v___x_2215_, v___x_2216_, v___x_2218_);
        v___x_2220_ = lean_apply_1(v_pushOutput_2214_, v___x_2219_);
        v___x_2221_ = lean_apply_4(
            v_toBind_2204_,
            lean_box(0),
            lean_box(0),
            v___x_2220_,
            v___f_2206_,
        );
        return v___x_2221_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(
    mut v_indent_2222_: *mut LeanObject,
    mut v_inst_2223_: *mut LeanObject,
    mut v_toBind_2224_: *mut LeanObject,
    mut v___f_2225_: *mut LeanObject,
    mut v___f_2226_: *mut LeanObject,
    mut v_k_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(
        v_indent_2222_,
        v_inst_2223_,
        v_toBind_2224_,
        v___f_2225_,
        v___f_2226_,
        v_k_2227_,
    );
    lean_dec(v_indent_2222_);
    return v_res_2228_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(
    mut v_inst_2229_: *mut LeanObject,
    mut v_activeTags_2230_: *mut LeanObject,
    mut v_toBind_2231_: *mut LeanObject,
    mut v___f_2232_: *mut LeanObject,
    mut v_____r_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_endTags_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    v_endTags_2234_ = lean_ctor_get(v_inst_2229_, 4);
    lean_inc(v_endTags_2234_);
    lean_dec_ref(v_inst_2229_);
    v___x_2235_ = lean_apply_1(v_endTags_2234_, v_activeTags_2230_);
    v___x_2236_ = lean_apply_4(
        v_toBind_2231_,
        lean_box(0),
        lean_box(0),
        v___x_2235_,
        v___f_2232_,
    );
    return v___x_2236_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(
    mut v_gs_x27_2237_: *mut LeanObject,
    mut v_tail_2238_: *mut LeanObject,
    mut v_w_2239_: *mut LeanObject,
    mut v_inst_2240_: *mut LeanObject,
    mut v_inst_2241_: *mut LeanObject,
    mut v_____r_2242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    v___x_2243_ = lean_apply_1(v_gs_x27_2237_, v_tail_2238_);
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
    mut v_tail_2247_: *mut LeanObject,
    mut v_tail_2248_: *mut LeanObject,
    mut v_w_2249_: *mut LeanObject,
    mut v_inst_2250_: *mut LeanObject,
    mut v_inst_2251_: *mut LeanObject,
    mut v_toBind_2252_: *mut LeanObject,
    mut v_____r_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2251_);
    lean_inc_ref(v_inst_2250_);
    lean_inc(v_w_2249_);
    v___x_2254_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
        v_flb_2246_,
        v_tail_2247_,
        v_tail_2248_,
        v_w_2249_,
        v_inst_2250_,
        v_inst_2251_,
    );
    v___x_2255_ = lean_alloc_closure(
        l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_2255_, 0, v_w_2249_);
    lean_closure_set(v___x_2255_, 1, v_inst_2250_);
    lean_closure_set(v___x_2255_, 2, v_inst_2251_);
    v___x_2256_ = lean_apply_4(
        v_toBind_2252_,
        lean_box(0),
        lean_box(0),
        v___x_2254_,
        v___x_2255_,
    );
    return v___x_2256_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(
    mut v_flb_2257_: *mut LeanObject,
    mut v_tail_2258_: *mut LeanObject,
    mut v_tail_2259_: *mut LeanObject,
    mut v_w_2260_: *mut LeanObject,
    mut v_inst_2261_: *mut LeanObject,
    mut v_inst_2262_: *mut LeanObject,
    mut v_toBind_2263_: *mut LeanObject,
    mut v_____r_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_2076__boxed_2265_: u8 = 0;
    let mut v_res_2266_: *mut LeanObject = core::ptr::null_mut();
    v_flb_2076__boxed_2265_ = (lean_unbox(v_flb_2257_) as u8);
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
    mut v_breakHere_2268_: *mut LeanObject,
    mut v_w_2269_: *mut LeanObject,
    mut v_inst_2270_: *mut LeanObject,
    mut v_inst_2271_: *mut LeanObject,
    mut v_endTags_2272_: *mut LeanObject,
    mut v_activeTags_2273_: *mut LeanObject,
    mut v_toBind_2274_: *mut LeanObject,
    mut v_pushOutput_2275_: *mut LeanObject,
    mut v___x_2276_: *mut LeanObject,
    mut v_____x_2277_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2277_) == 1 {
        let mut v_head_2278_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fla_2279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: u8 = 0;
        v_head_2278_ = lean_ctor_get(v_____x_2277_, 0);
        v_fla_2279_ = lean_ctor_get(v_head_2278_, 0);
        v___x_2280_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2279_);
        if v___x_2280_ == 0 {
            lean_dec_ref_known(v_____x_2277_, 2);
            lean_dec_ref(v___x_2276_);
            lean_dec(v_pushOutput_2275_);
            lean_dec(v_toBind_2274_);
            lean_dec(v_activeTags_2273_);
            lean_dec(v_endTags_2272_);
            lean_dec_ref(v_inst_2271_);
            lean_dec_ref(v_inst_2270_);
            lean_dec(v_w_2269_);
            lean_inc(v_breakHere_2268_);
            return v_breakHere_2268_;
        } else {
            let mut v___f_2281_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2282_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
            v___f_2281_ = lean_alloc_closure(
                l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_2281_, 0, v_w_2269_);
            lean_closure_set(v___f_2281_, 1, v_inst_2270_);
            lean_closure_set(v___f_2281_, 2, v_inst_2271_);
            lean_closure_set(v___f_2281_, 3, v_____x_2277_);
            lean_inc(v_toBind_2274_);
            v___f_2282_ = lean_alloc_closure(
                l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_2282_, 0, v_endTags_2272_);
            lean_closure_set(v___f_2282_, 1, v_activeTags_2273_);
            lean_closure_set(v___f_2282_, 2, v_toBind_2274_);
            lean_closure_set(v___f_2282_, 3, v___f_2281_);
            v___x_2283_ = lean_apply_1(v_pushOutput_2275_, v___x_2276_);
            v___x_2284_ = lean_apply_4(
                v_toBind_2274_,
                lean_box(0),
                lean_box(0),
                v___x_2283_,
                v___f_2282_,
            );
            return v___x_2284_;
        }
    } else {
        let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____x_2277_);
        lean_dec_ref(v___x_2276_);
        lean_dec(v_pushOutput_2275_);
        lean_dec(v_toBind_2274_);
        lean_dec(v_activeTags_2273_);
        lean_dec(v_endTags_2272_);
        lean_dec_ref(v_inst_2271_);
        lean_dec(v_w_2269_);
        v___x_2285_ = lean_box(0);
        v___x_2286_ = l_instInhabitedOfMonad___redArg(v_inst_2270_, v___x_2285_);
        v___x_2287_ =
            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0;
        v___x_2288_ = l_panic___redArg(v___x_2286_, v___x_2287_);
        lean_dec(v___x_2286_);
        return v___x_2288_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(
    mut v_breakHere_2289_: *mut LeanObject,
    mut v_w_2290_: *mut LeanObject,
    mut v_inst_2291_: *mut LeanObject,
    mut v_inst_2292_: *mut LeanObject,
    mut v_endTags_2293_: *mut LeanObject,
    mut v_activeTags_2294_: *mut LeanObject,
    mut v_toBind_2295_: *mut LeanObject,
    mut v_pushOutput_2296_: *mut LeanObject,
    mut v___x_2297_: *mut LeanObject,
    mut v_____x_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_breakHere_2289_);
    return v_res_2299_;
}
pub unsafe fn _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
    v___x_2301_ = lean_string_length(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(
    mut v_a_2302_: *mut LeanObject,
    mut v_p_2303_: *mut LeanObject,
    mut v___x_2304_: *mut LeanObject,
    mut v_indent_2305_: *mut LeanObject,
    mut v_activeTags_2306_: *mut LeanObject,
    mut v_tail_2307_: *mut LeanObject,
    mut v_fla_2308_: *mut LeanObject,
    mut v_flb_2309_: u8,
    mut v_tail_2310_: *mut LeanObject,
    mut v_w_2311_: *mut LeanObject,
    mut v_inst_2312_: *mut LeanObject,
    mut v_inst_2313_: *mut LeanObject,
    mut v_toBind_2314_: *mut LeanObject,
    mut v_gs_x27_2315_: *mut LeanObject,
    mut v_____r_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_is_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    v___x_2317_ = lean_string_utf8_next(v_a_2302_, v_p_2303_);
    v___x_2318_ = lean_string_utf8_extract(v_a_2302_, v___x_2317_, v___x_2304_);
    lean_dec(v___x_2317_);
    v___x_2319_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2319_, 0, v___x_2318_);
    v___x_2320_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2320_, 0, v___x_2319_);
    lean_ctor_set(v___x_2320_, 1, v_indent_2305_);
    lean_ctor_set(v___x_2320_, 2, v_activeTags_2306_);
    v_is_2321_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v_is_2321_, 0, v___x_2320_);
    lean_ctor_set(v_is_2321_, 1, v_tail_2307_);
    v___x_2322_ = lean_box(1);
    v___x_2323_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2308_, v___x_2322_);
    if v___x_2323_ == 0 {
        let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_gs_x27_2315_);
        lean_inc_ref(v_inst_2313_);
        lean_inc_ref(v_inst_2312_);
        lean_inc(v_w_2311_);
        v___x_2324_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
            v_flb_2309_,
            v_is_2321_,
            v_tail_2310_,
            v_w_2311_,
            v_inst_2312_,
            v_inst_2313_,
        );
        v___x_2325_ = lean_alloc_closure(
            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___x_2325_, 0, v_w_2311_);
        lean_closure_set(v___x_2325_, 1, v_inst_2312_);
        lean_closure_set(v___x_2325_, 2, v_inst_2313_);
        v___x_2326_ = lean_apply_4(
            v_toBind_2314_,
            lean_box(0),
            lean_box(0),
            v___x_2324_,
            v___x_2325_,
        );
        return v___x_2326_;
    } else {
        let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_2314_);
        lean_dec(v_tail_2310_);
        v___x_2327_ = lean_apply_1(v_gs_x27_2315_, v_is_2321_);
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
    mut v_a_2329_: *mut LeanObject,
    mut v_p_2330_: *mut LeanObject,
    mut v___x_2331_: *mut LeanObject,
    mut v_indent_2332_: *mut LeanObject,
    mut v_activeTags_2333_: *mut LeanObject,
    mut v_tail_2334_: *mut LeanObject,
    mut v_fla_2335_: *mut LeanObject,
    mut v_flb_2336_: *mut LeanObject,
    mut v_tail_2337_: *mut LeanObject,
    mut v_w_2338_: *mut LeanObject,
    mut v_inst_2339_: *mut LeanObject,
    mut v_inst_2340_: *mut LeanObject,
    mut v_toBind_2341_: *mut LeanObject,
    mut v_gs_x27_2342_: *mut LeanObject,
    mut v_____r_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_2100__boxed_2344_: u8 = 0;
    let mut v_res_2345_: *mut LeanObject = core::ptr::null_mut();
    v_flb_2100__boxed_2344_ = (lean_unbox(v_flb_2336_) as u8);
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
    lean_dec(v_fla_2335_);
    lean_dec(v___x_2331_);
    lean_dec(v_p_2330_);
    lean_dec_ref(v_a_2329_);
    return v_res_2345_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(
    mut v_activeTags_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_indent_2348_: *mut LeanObject,
    mut v_tail_2349_: *mut LeanObject,
    mut v_gs_x27_2350_: *mut LeanObject,
    mut v_w_2351_: *mut LeanObject,
    mut v_inst_2352_: *mut LeanObject,
    mut v_inst_2353_: *mut LeanObject,
    mut v_____r_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_2355_ = lean_unsigned_to_nat(1);
    v___x_2356_ = lean_nat_add(v_activeTags_2346_, v___x_2355_);
    v___x_2357_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2357_, 0, v_a_2347_);
    lean_ctor_set(v___x_2357_, 1, v_indent_2348_);
    lean_ctor_set(v___x_2357_, 2, v___x_2356_);
    v___x_2358_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2358_, 0, v___x_2357_);
    lean_ctor_set(v___x_2358_, 1, v_tail_2349_);
    v___x_2359_ = lean_apply_1(v_gs_x27_2350_, v___x_2358_);
    v___x_2360_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2351_,
        v_inst_2352_,
        v_inst_2353_,
        v___x_2359_,
    );
    return v___x_2360_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(
    mut v_activeTags_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
    mut v_indent_2363_: *mut LeanObject,
    mut v_tail_2364_: *mut LeanObject,
    mut v_gs_x27_2365_: *mut LeanObject,
    mut v_w_2366_: *mut LeanObject,
    mut v_inst_2367_: *mut LeanObject,
    mut v_inst_2368_: *mut LeanObject,
    mut v_____r_2369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2370_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_activeTags_2361_);
    return v_res_2370_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
    mut v_w_2371_: *mut LeanObject,
    mut v_inst_2372_: *mut LeanObject,
    mut v_inst_2373_: *mut LeanObject,
    mut v_x_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v_fla_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_flb_2390_: u8 = 0;
    let mut v_tail_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v_f_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indent_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gs_x27_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endTags_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: u8 = 0;
    let mut v_pushNewline_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endTags_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endTags_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pushNewline_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endTags_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_breakHere_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_force_2438_: u8 = 0;
    let mut v___f_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currColumn_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: u8 = 0;
    let mut v_endTags_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: u8 = 0;
    let mut v_a_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u32 = 0;
    let mut v_p_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v_pushOutput_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pushNewline_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pushOutput_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endTags_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indent_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_behavior_2498_: u8 = 0;
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startTag_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_unused_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut v_unused_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2374_) == 0 {
                    v_toApplicative_2375_ = lean_ctor_get(v_inst_2372_, 0);
                    lean_inc_ref(v_toApplicative_2375_);
                    lean_dec_ref(v_inst_2373_);
                    lean_dec_ref(v_inst_2372_);
                    lean_dec(v_w_2371_);
                    v_toPure_2376_ = lean_ctor_get(v_toApplicative_2375_, 1);
                    lean_inc(v_toPure_2376_);
                    lean_dec_ref(v_toApplicative_2375_);
                    v___x_2377_ = lean_box(0);
                    v___x_2378_ = lean_apply_2(v_toPure_2376_, lean_box(0), v___x_2377_);
                    return v___x_2378_;
                } else {
                    v_head_2379_ = lean_ctor_get(v_x_2374_, 0);
                    v_items_2380_ = lean_ctor_get(v_head_2379_, 1);
                    lean_inc(v_items_2380_);
                    if lean_obj_tag(v_items_2380_) == 0 {
                        v_tail_2381_ = lean_ctor_get(v_x_2374_, 1);
                        lean_inc(v_tail_2381_);
                        lean_dec_ref_known(v_x_2374_, 2);
                        v_x_2374_ = v_tail_2381_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_2379_);
                        v_head_2383_ = lean_ctor_get(v_items_2380_, 0);
                        lean_inc(v_head_2383_);
                        v_toBind_2384_ = lean_ctor_get(v_inst_2372_, 1);
                        v_tail_2385_ = lean_ctor_get(v_x_2374_, 1);
                        v_isSharedCheck_2528_ = (!lean_is_exclusive(v_x_2374_)) as u8;
                        if v_isSharedCheck_2528_ == 0 {
                            v_unused_2529_ = lean_ctor_get(v_x_2374_, 0);
                            lean_dec(v_unused_2529_);
                            v___x_2387_ = v_x_2374_;
                            v_isShared_2388_ = v_isSharedCheck_2528_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_2385_);
                            lean_dec(v_x_2374_);
                            v___x_2387_ = lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2528_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2389_ = lean_ctor_get(v_head_2379_, 0);
                lean_inc(v_fla_2389_);
                v_flb_2390_ = lean_ctor_get_uint8(
                    v_head_2379_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                lean_dec(v_head_2379_);
                v_tail_2391_ = lean_ctor_get(v_items_2380_, 1);
                v_isSharedCheck_2526_ = (!lean_is_exclusive(v_items_2380_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v_unused_2527_ = lean_ctor_get(v_items_2380_, 0);
                    lean_dec(v_unused_2527_);
                    v___x_2393_ = v_items_2380_;
                    v_isShared_2394_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_tail_2391_);
                    lean_dec(v_items_2380_);
                    v___x_2393_ = lean_box(0);
                    v_isShared_2394_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2395_ = lean_ctor_get(v_head_2383_, 0);
                v_indent_2396_ = lean_ctor_get(v_head_2383_, 1);
                v_activeTags_2397_ = lean_ctor_get(v_head_2383_, 2);
                v_isSharedCheck_2525_ = (!lean_is_exclusive(v_head_2383_)) as u8;
                if v_isSharedCheck_2525_ == 0 {
                    v___x_2399_ = v_head_2383_;
                    v_isShared_2400_ = v_isSharedCheck_2525_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_activeTags_2397_);
                    lean_inc(v_indent_2396_);
                    lean_inc(v_f_2395_);
                    lean_dec(v_head_2383_);
                    v___x_2399_ = lean_box(0);
                    v_isShared_2400_ = v_isSharedCheck_2525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2401_ = lean_box((v_flb_2390_) as usize);
                lean_inc(v_tail_2385_);
                lean_inc(v_fla_2389_);
                v_gs_x27_2402_ = lean_alloc_closure(
                    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v_gs_x27_2402_, 0, v_fla_2389_);
                lean_closure_set(v_gs_x27_2402_, 1, v___x_2401_);
                lean_closure_set(v_gs_x27_2402_, 2, v_tail_2385_);
                match lean_obj_tag(v_f_2395_) {
                    0 => {
                        lean_inc(v_toBind_2384_);
                        lean_del_object(v___x_2399_);
                        lean_dec(v_indent_2396_);
                        lean_del_object(v___x_2393_);
                        lean_dec(v_fla_2389_);
                        lean_del_object(v___x_2387_);
                        lean_dec(v_tail_2385_);
                        v_endTags_2403_ = lean_ctor_get(v_inst_2373_, 4);
                        lean_inc(v_endTags_2403_);
                        v___f_2404_ = lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        lean_closure_set(v___f_2404_, 0, v_gs_x27_2402_);
                        lean_closure_set(v___f_2404_, 1, v_tail_2391_);
                        lean_closure_set(v___f_2404_, 2, v_w_2371_);
                        lean_closure_set(v___f_2404_, 3, v_inst_2372_);
                        lean_closure_set(v___f_2404_, 4, v_inst_2373_);
                        v___x_2405_ = lean_apply_1(v_endTags_2403_, v_activeTags_2397_);
                        v___x_2406_ = lean_apply_4(
                            v_toBind_2384_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2405_,
                            v___f_2404_,
                        );
                        return v___x_2406_;
                    }
                    1 => {
                        lean_inc(v_toBind_2384_);
                        lean_del_object(v___x_2399_);
                        lean_del_object(v___x_2393_);
                        lean_del_object(v___x_2387_);
                        if v_flb_2390_ == 0 {
                            lean_dec(v_tail_2385_);
                            v___x_2407_ =
                                l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                            lean_dec(v_fla_2389_);
                            if v___x_2407_ == 0 {
                                v_pushNewline_2408_ = lean_ctor_get(v_inst_2373_, 1);
                                lean_inc(v_pushNewline_2408_);
                                v_endTags_2409_ = lean_ctor_get(v_inst_2373_, 4);
                                lean_inc(v_endTags_2409_);
                                v___f_2410_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                                lean_closure_set(v___f_2410_, 0, v_gs_x27_2402_);
                                lean_closure_set(v___f_2410_, 1, v_tail_2391_);
                                lean_closure_set(v___f_2410_, 2, v_w_2371_);
                                lean_closure_set(v___f_2410_, 3, v_inst_2372_);
                                lean_closure_set(v___f_2410_, 4, v_inst_2373_);
                                lean_inc(v_toBind_2384_);
                                v___f_2411_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                                lean_closure_set(v___f_2411_, 0, v_endTags_2409_);
                                lean_closure_set(v___f_2411_, 1, v_activeTags_2397_);
                                lean_closure_set(v___f_2411_, 2, v_toBind_2384_);
                                lean_closure_set(v___f_2411_, 3, v___f_2410_);
                                v___x_2412_ = l_Int_toNat(v_indent_2396_);
                                lean_dec(v_indent_2396_);
                                v___x_2413_ = lean_apply_1(v_pushNewline_2408_, v___x_2412_);
                                v___x_2414_ = lean_apply_4(
                                    v_toBind_2384_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2413_,
                                    v___f_2411_,
                                );
                                return v___x_2414_;
                            } else {
                                lean_dec(v_indent_2396_);
                                v_pushOutput_2415_ = lean_ctor_get(v_inst_2373_, 0);
                                lean_inc(v_pushOutput_2415_);
                                v_endTags_2416_ = lean_ctor_get(v_inst_2373_, 4);
                                lean_inc(v_endTags_2416_);
                                v___f_2417_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                                lean_closure_set(v___f_2417_, 0, v_gs_x27_2402_);
                                lean_closure_set(v___f_2417_, 1, v_tail_2391_);
                                lean_closure_set(v___f_2417_, 2, v_w_2371_);
                                lean_closure_set(v___f_2417_, 3, v_inst_2372_);
                                lean_closure_set(v___f_2417_, 4, v_inst_2373_);
                                lean_inc(v_toBind_2384_);
                                v___f_2418_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                                lean_closure_set(v___f_2418_, 0, v_endTags_2416_);
                                lean_closure_set(v___f_2418_, 1, v_activeTags_2397_);
                                lean_closure_set(v___f_2418_, 2, v_toBind_2384_);
                                lean_closure_set(v___f_2418_, 3, v___f_2417_);
                                v___x_2419_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                                v___x_2420_ = lean_apply_1(v_pushOutput_2415_, v___x_2419_);
                                v___x_2421_ = lean_apply_4(
                                    v_toBind_2384_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2420_,
                                    v___f_2418_,
                                );
                                return v___x_2421_;
                            }
                        } else {
                            lean_dec_ref(v_gs_x27_2402_);
                            v_pushOutput_2422_ = lean_ctor_get(v_inst_2373_, 0);
                            v_pushNewline_2423_ = lean_ctor_get(v_inst_2373_, 1);
                            v_endTags_2424_ = lean_ctor_get(v_inst_2373_, 4);
                            v___x_2425_ = lean_box((v_flb_2390_) as usize);
                            lean_inc_n(v_toBind_2384_, 3);
                            lean_inc_ref(v_inst_2373_);
                            lean_inc_ref(v_inst_2372_);
                            lean_inc(v_w_2371_);
                            lean_inc(v_tail_2385_);
                            lean_inc(v_tail_2391_);
                            v___f_2426_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed as *mut core::ffi::c_void, 8, 7);
                            lean_closure_set(v___f_2426_, 0, v___x_2425_);
                            lean_closure_set(v___f_2426_, 1, v_tail_2391_);
                            lean_closure_set(v___f_2426_, 2, v_tail_2385_);
                            lean_closure_set(v___f_2426_, 3, v_w_2371_);
                            lean_closure_set(v___f_2426_, 4, v_inst_2372_);
                            lean_closure_set(v___f_2426_, 5, v_inst_2373_);
                            lean_closure_set(v___f_2426_, 6, v_toBind_2384_);
                            lean_inc(v_activeTags_2397_);
                            lean_inc(v_endTags_2424_);
                            v___f_2427_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                            lean_closure_set(v___f_2427_, 0, v_endTags_2424_);
                            lean_closure_set(v___f_2427_, 1, v_activeTags_2397_);
                            lean_closure_set(v___f_2427_, 2, v_toBind_2384_);
                            lean_closure_set(v___f_2427_, 3, v___f_2426_);
                            v___x_2428_ = l_Int_toNat(v_indent_2396_);
                            lean_dec(v_indent_2396_);
                            lean_inc(v_pushNewline_2423_);
                            v___x_2429_ = lean_apply_1(v_pushNewline_2423_, v___x_2428_);
                            v_breakHere_2430_ = lean_apply_4(
                                v_toBind_2384_,
                                lean_box(0),
                                lean_box(0),
                                v___x_2429_,
                                v___f_2427_,
                            );
                            v___x_2431_ =
                                l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                            lean_dec(v_fla_2389_);
                            if v___x_2431_ == 0 {
                                lean_dec(v_activeTags_2397_);
                                lean_dec(v_tail_2391_);
                                lean_dec(v_tail_2385_);
                                lean_dec(v_toBind_2384_);
                                lean_dec_ref(v_inst_2373_);
                                lean_dec_ref(v_inst_2372_);
                                lean_dec(v_w_2371_);
                                return v_breakHere_2430_;
                            } else {
                                v___x_2432_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                                lean_inc(v_pushOutput_2422_);
                                lean_inc(v_toBind_2384_);
                                lean_inc(v_endTags_2424_);
                                lean_inc_ref(v_inst_2373_);
                                lean_inc_ref(v_inst_2372_);
                                lean_inc(v_w_2371_);
                                v___f_2433_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed as *mut core::ffi::c_void, 10, 9);
                                lean_closure_set(v___f_2433_, 0, v_breakHere_2430_);
                                lean_closure_set(v___f_2433_, 1, v_w_2371_);
                                lean_closure_set(v___f_2433_, 2, v_inst_2372_);
                                lean_closure_set(v___f_2433_, 3, v_inst_2373_);
                                lean_closure_set(v___f_2433_, 4, v_endTags_2424_);
                                lean_closure_set(v___f_2433_, 5, v_activeTags_2397_);
                                lean_closure_set(v___f_2433_, 6, v_toBind_2384_);
                                lean_closure_set(v___f_2433_, 7, v_pushOutput_2422_);
                                lean_closure_set(v___f_2433_, 8, v___x_2432_);
                                v___x_2434_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                                v___x_2435_ = lean_nat_sub(v_w_2371_, v___x_2434_);
                                lean_dec(v_w_2371_);
                                v___x_2436_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_2390_, v_tail_2391_, v_tail_2385_, v___x_2435_, v_inst_2372_, v_inst_2373_);
                                v___x_2437_ = lean_apply_4(
                                    v_toBind_2384_,
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2436_,
                                    v___f_2433_,
                                );
                                return v___x_2437_;
                            }
                        }
                    }
                    2 => {
                        lean_inc_n(v_toBind_2384_, 3);
                        lean_del_object(v___x_2399_);
                        lean_del_object(v___x_2393_);
                        lean_del_object(v___x_2387_);
                        lean_dec(v_tail_2385_);
                        v_force_2438_ = lean_ctor_get_uint8(v_f_2395_, 0 as u32);
                        lean_dec_ref_known(v_f_2395_, 0);
                        lean_inc_ref_n(v_inst_2373_, 3);
                        v___f_2439_ = lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1
                                as *mut core::ffi::c_void,
                            6,
                            5,
                        );
                        lean_closure_set(v___f_2439_, 0, v_gs_x27_2402_);
                        lean_closure_set(v___f_2439_, 1, v_tail_2391_);
                        lean_closure_set(v___f_2439_, 2, v_w_2371_);
                        lean_closure_set(v___f_2439_, 3, v_inst_2372_);
                        lean_closure_set(v___f_2439_, 4, v_inst_2373_);
                        lean_inc_ref(v___f_2439_);
                        lean_inc(v_activeTags_2397_);
                        v___f_2440_ = lean_alloc_closure(
                            l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        lean_closure_set(v___f_2440_, 0, v_inst_2373_);
                        lean_closure_set(v___f_2440_, 1, v_activeTags_2397_);
                        lean_closure_set(v___f_2440_, 2, v_toBind_2384_);
                        lean_closure_set(v___f_2440_, 3, v___f_2439_);
                        lean_inc_ref(v___f_2440_);
                        v___f_2441_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 5);
                        lean_closure_set(v___f_2441_, 0, v_indent_2396_);
                        lean_closure_set(v___f_2441_, 1, v_inst_2373_);
                        lean_closure_set(v___f_2441_, 2, v_toBind_2384_);
                        lean_closure_set(v___f_2441_, 3, v___f_2440_);
                        lean_closure_set(v___f_2441_, 4, v___f_2440_);
                        v___x_2450_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                        lean_dec(v_fla_2389_);
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
                                lean_dec_ref(v___f_2439_);
                                lean_dec(v_activeTags_2397_);
                                state = 4;
                                continue;
                            }
                        }
                    }
                    3 => {
                        lean_inc(v_toBind_2384_);
                        lean_del_object(v___x_2399_);
                        lean_del_object(v___x_2393_);
                        lean_del_object(v___x_2387_);
                        v_a_2451_ = lean_ctor_get(v_f_2395_, 0);
                        lean_inc_ref_n(v_a_2451_, 2);
                        lean_dec_ref_known(v_f_2395_, 1);
                        v___x_2452_ = 10;
                        v_p_2453_ = lean_string_posof(v_a_2451_, v___x_2452_);
                        v___x_2454_ = lean_string_utf8_byte_size(v_a_2451_);
                        v___x_2455_ = lean_nat_dec_eq(v_p_2453_, v___x_2454_);
                        if v___x_2455_ == 0 {
                            v_pushOutput_2456_ = lean_ctor_get(v_inst_2373_, 0);
                            lean_inc(v_pushOutput_2456_);
                            v_pushNewline_2457_ = lean_ctor_get(v_inst_2373_, 1);
                            lean_inc(v_pushNewline_2457_);
                            v___x_2458_ = lean_box((v_flb_2390_) as usize);
                            lean_inc_n(v_toBind_2384_, 2);
                            lean_inc(v_indent_2396_);
                            lean_inc(v_p_2453_);
                            lean_inc_ref(v_a_2451_);
                            v___f_2459_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed as *mut core::ffi::c_void, 15, 14);
                            lean_closure_set(v___f_2459_, 0, v_a_2451_);
                            lean_closure_set(v___f_2459_, 1, v_p_2453_);
                            lean_closure_set(v___f_2459_, 2, v___x_2454_);
                            lean_closure_set(v___f_2459_, 3, v_indent_2396_);
                            lean_closure_set(v___f_2459_, 4, v_activeTags_2397_);
                            lean_closure_set(v___f_2459_, 5, v_tail_2391_);
                            lean_closure_set(v___f_2459_, 6, v_fla_2389_);
                            lean_closure_set(v___f_2459_, 7, v___x_2458_);
                            lean_closure_set(v___f_2459_, 8, v_tail_2385_);
                            lean_closure_set(v___f_2459_, 9, v_w_2371_);
                            lean_closure_set(v___f_2459_, 10, v_inst_2372_);
                            lean_closure_set(v___f_2459_, 11, v_inst_2373_);
                            lean_closure_set(v___f_2459_, 12, v_toBind_2384_);
                            lean_closure_set(v___f_2459_, 13, v_gs_x27_2402_);
                            v___f_2460_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed as *mut core::ffi::c_void, 5, 4);
                            lean_closure_set(v___f_2460_, 0, v_indent_2396_);
                            lean_closure_set(v___f_2460_, 1, v_pushNewline_2457_);
                            lean_closure_set(v___f_2460_, 2, v_toBind_2384_);
                            lean_closure_set(v___f_2460_, 3, v___f_2459_);
                            v___x_2461_ = lean_unsigned_to_nat(0);
                            v___x_2462_ =
                                lean_string_utf8_extract(v_a_2451_, v___x_2461_, v_p_2453_);
                            lean_dec(v_p_2453_);
                            lean_dec_ref(v_a_2451_);
                            v___x_2463_ = lean_apply_1(v_pushOutput_2456_, v___x_2462_);
                            v___x_2464_ = lean_apply_4(
                                v_toBind_2384_,
                                lean_box(0),
                                lean_box(0),
                                v___x_2463_,
                                v___f_2460_,
                            );
                            return v___x_2464_;
                        } else {
                            lean_dec(v_p_2453_);
                            lean_dec(v_indent_2396_);
                            lean_dec(v_fla_2389_);
                            lean_dec(v_tail_2385_);
                            v_pushOutput_2465_ = lean_ctor_get(v_inst_2373_, 0);
                            lean_inc(v_pushOutput_2465_);
                            v_endTags_2466_ = lean_ctor_get(v_inst_2373_, 4);
                            lean_inc(v_endTags_2466_);
                            v___f_2467_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                            lean_closure_set(v___f_2467_, 0, v_gs_x27_2402_);
                            lean_closure_set(v___f_2467_, 1, v_tail_2391_);
                            lean_closure_set(v___f_2467_, 2, v_w_2371_);
                            lean_closure_set(v___f_2467_, 3, v_inst_2372_);
                            lean_closure_set(v___f_2467_, 4, v_inst_2373_);
                            lean_inc(v_toBind_2384_);
                            v___f_2468_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3 as *mut core::ffi::c_void, 5, 4);
                            lean_closure_set(v___f_2468_, 0, v_endTags_2466_);
                            lean_closure_set(v___f_2468_, 1, v_activeTags_2397_);
                            lean_closure_set(v___f_2468_, 2, v_toBind_2384_);
                            lean_closure_set(v___f_2468_, 3, v___f_2467_);
                            v___x_2469_ = lean_apply_1(v_pushOutput_2465_, v_a_2451_);
                            v___x_2470_ = lean_apply_4(
                                v_toBind_2384_,
                                lean_box(0),
                                lean_box(0),
                                v___x_2469_,
                                v___f_2468_,
                            );
                            return v___x_2470_;
                        }
                    }
                    4 => {
                        lean_dec_ref(v_gs_x27_2402_);
                        lean_del_object(v___x_2387_);
                        v_indent_2471_ = lean_ctor_get(v_f_2395_, 0);
                        lean_inc(v_indent_2471_);
                        v_f_2472_ = lean_ctor_get(v_f_2395_, 1);
                        lean_inc(v_f_2472_);
                        lean_dec_ref_known(v_f_2395_, 2);
                        v___x_2473_ = lean_int_add(v_indent_2396_, v_indent_2471_);
                        lean_dec(v_indent_2471_);
                        lean_dec(v_indent_2396_);
                        if v_isShared_2400_ == 0 {
                            lean_ctor_set(v___x_2399_, 1, v___x_2473_);
                            lean_ctor_set(v___x_2399_, 0, v_f_2472_);
                            v___x_2475_ = v___x_2399_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_f_2472_);
                            lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2473_);
                            lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_activeTags_2397_);
                            v___x_2475_ = v_reuseFailAlloc_2481_;
                            state = 6;
                            continue;
                        }
                    }
                    5 => {
                        lean_dec_ref(v_gs_x27_2402_);
                        v_a_2482_ = lean_ctor_get(v_f_2395_, 0);
                        lean_inc(v_a_2482_);
                        v_a_2483_ = lean_ctor_get(v_f_2395_, 1);
                        lean_inc(v_a_2483_);
                        lean_dec_ref_known(v_f_2395_, 2);
                        v___x_2484_ = lean_unsigned_to_nat(0);
                        lean_inc(v_indent_2396_);
                        if v_isShared_2400_ == 0 {
                            lean_ctor_set(v___x_2399_, 2, v___x_2484_);
                            lean_ctor_set(v___x_2399_, 0, v_a_2482_);
                            v___x_2486_ = v___x_2399_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2482_);
                            lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_indent_2396_);
                            lean_ctor_set(v_reuseFailAlloc_2496_, 2, v___x_2484_);
                            v___x_2486_ = v_reuseFailAlloc_2496_;
                            state = 8;
                            continue;
                        }
                    }
                    6 => {
                        lean_dec_ref(v_gs_x27_2402_);
                        lean_del_object(v___x_2387_);
                        v_a_2497_ = lean_ctor_get(v_f_2395_, 0);
                        lean_inc(v_a_2497_);
                        v_behavior_2498_ = lean_ctor_get_uint8(
                            v_f_2395_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        lean_dec_ref_known(v_f_2395_, 1);
                        v___x_2499_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2389_);
                        if v___x_2499_ == 0 {
                            lean_inc(v_toBind_2384_);
                            if v_isShared_2400_ == 0 {
                                lean_ctor_set(v___x_2399_, 0, v_a_2497_);
                                v___x_2501_ = v___x_2399_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2497_);
                                lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_indent_2396_);
                                lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_activeTags_2397_);
                                v___x_2501_ = v_reuseFailAlloc_2510_;
                                state = 11;
                                continue;
                            }
                        } else {
                            if v_isShared_2400_ == 0 {
                                lean_ctor_set(v___x_2399_, 0, v_a_2497_);
                                v___x_2512_ = v___x_2399_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2497_);
                                lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_indent_2396_);
                                lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_activeTags_2397_);
                                v___x_2512_ = v_reuseFailAlloc_2518_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                    _ => {
                        lean_inc(v_toBind_2384_);
                        lean_del_object(v___x_2399_);
                        lean_del_object(v___x_2393_);
                        lean_dec(v_fla_2389_);
                        lean_del_object(v___x_2387_);
                        lean_dec(v_tail_2385_);
                        v_a_2519_ = lean_ctor_get(v_f_2395_, 0);
                        lean_inc(v_a_2519_);
                        v_a_2520_ = lean_ctor_get(v_f_2395_, 1);
                        lean_inc(v_a_2520_);
                        lean_dec_ref_known(v_f_2395_, 2);
                        v_startTag_2521_ = lean_ctor_get(v_inst_2373_, 3);
                        lean_inc(v_startTag_2521_);
                        v___f_2522_ = lean_alloc_closure(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed as *mut core::ffi::c_void, 9, 8);
                        lean_closure_set(v___f_2522_, 0, v_activeTags_2397_);
                        lean_closure_set(v___f_2522_, 1, v_a_2520_);
                        lean_closure_set(v___f_2522_, 2, v_indent_2396_);
                        lean_closure_set(v___f_2522_, 3, v_tail_2391_);
                        lean_closure_set(v___f_2522_, 4, v_gs_x27_2402_);
                        lean_closure_set(v___f_2522_, 5, v_w_2371_);
                        lean_closure_set(v___f_2522_, 6, v_inst_2372_);
                        lean_closure_set(v___f_2522_, 7, v_inst_2373_);
                        v___x_2523_ = lean_apply_1(v_startTag_2521_, v_a_2519_);
                        v___x_2524_ = lean_apply_4(
                            v_toBind_2384_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2523_,
                            v___f_2522_,
                        );
                        return v___x_2524_;
                    }
                }
            }
            4 => {
                v_currColumn_2443_ = lean_ctor_get(v_inst_2373_, 2);
                lean_inc(v_currColumn_2443_);
                lean_dec_ref(v_inst_2373_);
                v___x_2444_ = lean_apply_4(
                    v_toBind_2384_,
                    lean_box(0),
                    lean_box(0),
                    v_currColumn_2443_,
                    v___f_2441_,
                );
                return v___x_2444_;
            }
            5 => {
                if v___y_2446_ == 0 {
                    lean_dec_ref(v___f_2439_);
                    lean_dec(v_activeTags_2397_);
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref(v___f_2441_);
                    v_endTags_2447_ = lean_ctor_get(v_inst_2373_, 4);
                    lean_inc(v_endTags_2447_);
                    lean_dec_ref(v_inst_2373_);
                    v___x_2448_ = lean_apply_1(v_endTags_2447_, v_activeTags_2397_);
                    v___x_2449_ = lean_apply_4(
                        v_toBind_2384_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2448_,
                        v___f_2439_,
                    );
                    return v___x_2449_;
                }
            }
            6 => {
                if v_isShared_2394_ == 0 {
                    lean_ctor_set(v___x_2393_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2475_);
                    lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_tail_2391_);
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
                v___x_2487_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2487_, 0, v_a_2483_);
                lean_ctor_set(v___x_2487_, 1, v_indent_2396_);
                lean_ctor_set(v___x_2487_, 2, v_activeTags_2397_);
                if v_isShared_2394_ == 0 {
                    lean_ctor_set(v___x_2393_, 0, v___x_2487_);
                    v___x_2489_ = v___x_2393_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2487_);
                    lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_tail_2391_);
                    v___x_2489_ = v_reuseFailAlloc_2495_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2388_ == 0 {
                    lean_ctor_set(v___x_2387_, 1, v___x_2489_);
                    lean_ctor_set(v___x_2387_, 0, v___x_2486_);
                    v___x_2491_ = v___x_2387_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2486_);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 1, v___x_2489_);
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
                v___x_2502_ = lean_box(0);
                if v_isShared_2394_ == 0 {
                    lean_ctor_set(v___x_2393_, 1, v___x_2502_);
                    lean_ctor_set(v___x_2393_, 0, v___x_2501_);
                    v___x_2504_ = v___x_2393_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2501_);
                    lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2502_);
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
                lean_inc_ref(v_inst_2373_);
                lean_inc_ref(v_inst_2372_);
                lean_inc(v_w_2371_);
                v___x_2506_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(
                    v_behavior_2498_,
                    v___x_2504_,
                    v___x_2505_,
                    v_w_2371_,
                    v_inst_2372_,
                    v_inst_2373_,
                );
                v___x_2507_ = lean_alloc_closure(
                    l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___x_2507_, 0, v_w_2371_);
                lean_closure_set(v___x_2507_, 1, v_inst_2372_);
                lean_closure_set(v___x_2507_, 2, v_inst_2373_);
                v___x_2508_ = lean_apply_4(
                    v_toBind_2384_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2506_,
                    v___x_2507_,
                );
                return v___x_2508_;
            }
            13 => {
                if v_isShared_2394_ == 0 {
                    lean_ctor_set(v___x_2393_, 0, v___x_2512_);
                    v___x_2514_ = v___x_2393_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2512_);
                    lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_tail_2391_);
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
    mut v_w_2530_: *mut LeanObject,
    mut v_inst_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_____x_2533_: *mut LeanObject,
    mut v_____r_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___x_2535_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2530_,
        v_inst_2531_,
        v_inst_2532_,
        v_____x_2533_,
    );
    return v___x_2535_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be(
    mut v_m_2536_: *mut LeanObject,
    mut v_w_2537_: *mut LeanObject,
    mut v_inst_2538_: *mut LeanObject,
    mut v_inst_2539_: *mut LeanObject,
    mut v_x_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2537_,
        v_inst_2538_,
        v_inst_2539_,
        v_x_2540_,
    );
    return v___x_2541_;
}
pub unsafe fn l_Std_Format_prettyM___redArg(
    mut v_f_2542_: *mut LeanObject,
    mut v_w_2543_: *mut LeanObject,
    mut v_indent_2544_: *mut LeanObject,
    mut v_inst_2545_: *mut LeanObject,
    mut v_inst_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = lean_box(1);
    v___x_2548_ = 0;
    v___x_2549_ = lean_nat_to_int(v_indent_2544_);
    v___x_2550_ = lean_unsigned_to_nat(0);
    v___x_2551_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2551_, 0, v_f_2542_);
    lean_ctor_set(v___x_2551_, 1, v___x_2549_);
    lean_ctor_set(v___x_2551_, 2, v___x_2550_);
    v___x_2552_ = lean_box(0);
    v___x_2553_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2553_, 0, v___x_2551_);
    lean_ctor_set(v___x_2553_, 1, v___x_2552_);
    v___x_2554_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_2554_, 0, v___x_2547_);
    lean_ctor_set(v___x_2554_, 1, v___x_2553_);
    lean_ctor_set_uint8(
        v___x_2554_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_2548_,
    );
    v___x_2555_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2555_, 0, v___x_2554_);
    lean_ctor_set(v___x_2555_, 1, v___x_2552_);
    v___x_2556_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(
        v_w_2543_,
        v_inst_2545_,
        v_inst_2546_,
        v___x_2555_,
    );
    return v___x_2556_;
}
pub unsafe fn l_Std_Format_prettyM(
    mut v_m_2557_: *mut LeanObject,
    mut v_f_2558_: *mut LeanObject,
    mut v_w_2559_: *mut LeanObject,
    mut v_indent_2560_: *mut LeanObject,
    mut v_inst_2561_: *mut LeanObject,
    mut v_inst_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_l_2564_: *mut LeanObject,
    mut v_f_2565_: *mut LeanObject,
    mut v_r_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    v___x_2567_ = lean_string_length(v_l_2564_);
    v___x_2568_ = lean_nat_to_int(v___x_2567_);
    v___x_2569_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2569_, 0, v_l_2564_);
    v___x_2570_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2570_, 0, v___x_2569_);
    lean_ctor_set(v___x_2570_, 1, v_f_2565_);
    v___x_2571_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2571_, 0, v_r_2566_);
    v___x_2572_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2572_, 0, v___x_2570_);
    lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2573_, 0, v___x_2568_);
    lean_ctor_set(v___x_2573_, 1, v___x_2572_);
    v___x_2574_ = 0;
    v___x_2575_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2575_, 0, v___x_2573_);
    lean_ctor_set_uint8(
        v___x_2575_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2574_,
    );
    return v___x_2575_;
}
pub unsafe fn _init_l_Std_Format_paren___closed__2() -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_Format_paren___closed__0;
    v___x_2579_ = lean_string_length(v___x_2578_);
    return v___x_2579_;
}
pub unsafe fn _init_l_Std_Format_paren___closed__3() -> *mut LeanObject {
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2580_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__2),
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__2_once),
        _init_l_Std_Format_paren___closed__2,
    );
    v___x_2581_ = lean_nat_to_int(v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Std_Format_paren(mut v_f_2586_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__3),
        core::ptr::addr_of_mut!(l_Std_Format_paren___closed__3_once),
        _init_l_Std_Format_paren___closed__3,
    );
    v___x_2588_ = l_Std_Format_paren___closed__4;
    v___x_2589_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2589_, 0, v___x_2588_);
    lean_ctor_set(v___x_2589_, 1, v_f_2586_);
    v___x_2590_ = l_Std_Format_paren___closed__5;
    v___x_2591_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2591_, 0, v___x_2589_);
    lean_ctor_set(v___x_2591_, 1, v___x_2590_);
    v___x_2592_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2592_, 0, v___x_2587_);
    lean_ctor_set(v___x_2592_, 1, v___x_2591_);
    v___x_2593_ = 0;
    v___x_2594_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2594_, 0, v___x_2592_);
    lean_ctor_set_uint8(
        v___x_2594_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2593_,
    );
    return v___x_2594_;
}
pub unsafe fn _init_l_Std_Format_sbracket___closed__2() -> *mut LeanObject {
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Std_Format_sbracket___closed__0;
    v___x_2598_ = lean_string_length(v___x_2597_);
    return v___x_2598_;
}
pub unsafe fn _init_l_Std_Format_sbracket___closed__3() -> *mut LeanObject {
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    v___x_2599_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__2),
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__2_once),
        _init_l_Std_Format_sbracket___closed__2,
    );
    v___x_2600_ = lean_nat_to_int(v___x_2599_);
    return v___x_2600_;
}
pub unsafe fn l_Std_Format_sbracket(mut v_f_2605_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__3),
        core::ptr::addr_of_mut!(l_Std_Format_sbracket___closed__3_once),
        _init_l_Std_Format_sbracket___closed__3,
    );
    v___x_2607_ = l_Std_Format_sbracket___closed__4;
    v___x_2608_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2608_, 0, v___x_2607_);
    lean_ctor_set(v___x_2608_, 1, v_f_2605_);
    v___x_2609_ = l_Std_Format_sbracket___closed__5;
    v___x_2610_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2610_, 0, v___x_2608_);
    lean_ctor_set(v___x_2610_, 1, v___x_2609_);
    v___x_2611_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2611_, 0, v___x_2606_);
    lean_ctor_set(v___x_2611_, 1, v___x_2610_);
    v___x_2612_ = 0;
    v___x_2613_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2613_, 0, v___x_2611_);
    lean_ctor_set_uint8(
        v___x_2613_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2612_,
    );
    return v___x_2613_;
}
pub unsafe fn l_Std_Format_bracketFill(
    mut v_l_2614_: *mut LeanObject,
    mut v_f_2615_: *mut LeanObject,
    mut v_r_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2617_ = lean_string_length(v_l_2614_);
    v___x_2618_ = lean_nat_to_int(v___x_2617_);
    v___x_2619_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2619_, 0, v_l_2614_);
    v___x_2620_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2620_, 0, v___x_2619_);
    lean_ctor_set(v___x_2620_, 1, v_f_2615_);
    v___x_2621_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2621_, 0, v_r_2616_);
    v___x_2622_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2622_, 0, v___x_2620_);
    lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    v___x_2623_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2623_, 0, v___x_2618_);
    lean_ctor_set(v___x_2623_, 1, v___x_2622_);
    v___x_2624_ = l_Std_Format_fill(v___x_2623_);
    return v___x_2624_;
}
pub unsafe fn _init_l_Std_Format_defIndent() -> *mut LeanObject {
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    v___x_2625_ = lean_unsigned_to_nat(2);
    return v___x_2625_;
}
pub unsafe fn _init_l_Std_Format_defUnicode() -> u8 {
    let mut v___x_2626_: u8 = 0;
    v___x_2626_ = 1;
    return v___x_2626_;
}
pub unsafe fn _init_l_Std_Format_defWidth() -> *mut LeanObject {
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2627_ = lean_unsigned_to_nat(120);
    return v___x_2627_;
}
pub unsafe fn _init_l_Std_Format_nestD___closed__0() -> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    v___x_2628_ = lean_unsigned_to_nat(2);
    v___x_2629_ = lean_nat_to_int(v___x_2628_);
    return v___x_2629_;
}
pub unsafe fn l_Std_Format_nestD(mut v_f_2630_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    v___x_2631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Format_nestD___closed__0),
        core::ptr::addr_of_mut!(l_Std_Format_nestD___closed__0_once),
        _init_l_Std_Format_nestD___closed__0,
    );
    v___x_2632_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2632_, 0, v___x_2631_);
    lean_ctor_set(v___x_2632_, 1, v_f_2630_);
    return v___x_2632_;
}
pub unsafe fn l_Std_Format_indentD(mut v_f_2633_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2634_ = lean_box(1);
    v___x_2635_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2635_, 0, v___x_2634_);
    lean_ctor_set(v___x_2635_, 1, v_f_2633_);
    v___x_2636_ = l_Std_Format_nestD(v___x_2635_);
    return v___x_2636_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(
    mut v_s_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_out_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2639_ = lean_ctor_get(v___y_2638_, 0);
                v_column_2640_ = lean_ctor_get(v___y_2638_, 1);
                v_isSharedCheck_2652_ = (!lean_is_exclusive(v___y_2638_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v___x_2642_ = v___y_2638_;
                    v_isShared_2643_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_column_2640_);
                    lean_inc(v_out_2639_);
                    lean_dec(v___y_2638_);
                    v___x_2642_ = lean_box(0);
                    v_isShared_2643_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2644_ = lean_box(0);
                v___x_2645_ = lean_string_append(v_out_2639_, v_s_2637_);
                v___x_2646_ = lean_string_length(v_s_2637_);
                v___x_2647_ = lean_nat_add(v_column_2640_, v___x_2646_);
                lean_dec(v___x_2646_);
                lean_dec(v_column_2640_);
                if v_isShared_2643_ == 0 {
                    lean_ctor_set(v___x_2642_, 1, v___x_2647_);
                    lean_ctor_set(v___x_2642_, 0, v___x_2645_);
                    v___x_2649_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
                    lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2647_);
                    v___x_2649_ = v_reuseFailAlloc_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2650_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2650_, 0, v___x_2644_);
                lean_ctor_set(v___x_2650_, 1, v___x_2649_);
                return v___x_2650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(
    mut v_s_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2655_: *mut LeanObject = core::ptr::null_mut();
    v_res_2655_ =
        l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(
            v_s_2653_,
            v___y_2654_,
        );
    lean_dec_ref(v_s_2653_);
    return v_res_2655_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(
    mut v_indent_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_out_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: u32 = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_unused_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2659_ = lean_ctor_get(v___y_2658_, 0);
                v_isSharedCheck_2672_ = (!lean_is_exclusive(v___y_2658_)) as u8;
                if v_isSharedCheck_2672_ == 0 {
                    v_unused_2673_ = lean_ctor_get(v___y_2658_, 1);
                    lean_dec(v_unused_2673_);
                    v___x_2661_ = v___y_2658_;
                    v_isShared_2662_ = v_isSharedCheck_2672_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_out_2659_);
                    lean_dec(v___y_2658_);
                    v___x_2661_ = lean_box(0);
                    v_isShared_2662_ = v_isSharedCheck_2672_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2663_ = lean_box(0);
                v___x_2664_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2665_ = 32;
                lean_inc(v_indent_2657_);
                v___x_2666_ = lean_string_pushn(v___x_2664_, v___x_2665_, v_indent_2657_);
                v___x_2667_ = lean_string_append(v_out_2659_, v___x_2666_);
                lean_dec_ref(v___x_2666_);
                if v_isShared_2662_ == 0 {
                    lean_ctor_set(v___x_2661_, 1, v_indent_2657_);
                    lean_ctor_set(v___x_2661_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2667_);
                    lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_indent_2657_);
                    v___x_2669_ = v_reuseFailAlloc_2671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2670_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2670_, 0, v___x_2663_);
                lean_ctor_set(v___x_2670_, 1, v___x_2669_);
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(
    mut v_____do__lift_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_column_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_unused_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2676_ = lean_ctor_get(v_____do__lift_2674_, 1);
                v_isSharedCheck_2683_ = (!lean_is_exclusive(v_____do__lift_2674_)) as u8;
                if v_isSharedCheck_2683_ == 0 {
                    v_unused_2684_ = lean_ctor_get(v_____do__lift_2674_, 0);
                    lean_dec(v_unused_2684_);
                    v___x_2678_ = v_____do__lift_2674_;
                    v_isShared_2679_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_column_2676_);
                    lean_dec(v_____do__lift_2674_);
                    v___x_2678_ = lean_box(0);
                    v_isShared_2679_ = v_isSharedCheck_2683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2679_ == 0 {
                    lean_ctor_set(v___x_2678_, 1, v___y_2675_);
                    lean_ctor_set(v___x_2678_, 0, v_column_2676_);
                    v___x_2681_ = v___x_2678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_column_2676_);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___y_2675_);
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
    mut v_x_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    v___x_2687_ = lean_box(0);
    v___x_2688_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2688_, 0, v___x_2687_);
    lean_ctor_set(v___x_2688_, 1, v___y_2686_);
    return v___x_2688_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(
    mut v_x_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2691_ =
        l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(
            v_x_2689_,
            v___y_2690_,
        );
    lean_dec(v_x_2689_);
    return v_res_2691_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(
    mut v_flb_2727_: u8,
    mut v_items_2728_: *mut LeanObject,
    mut v_gs_2729_: *mut LeanObject,
    mut v_w_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2733_: u8 = 0;
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundFlattenedHardLine_2749_: u8 = 0;
    let mut v_space_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: u8 = 0;
    let mut v_foundLine_2753_: u8 = 0;
    let mut v_space_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_u2082_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foundLine_2759_: u8 = 0;
    let mut v_foundFlattenedHardLine_2760_: u8 = 0;
    let mut v_space_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v___x_2770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_column_2738_ = lean_ctor_get(v___y_2731_, 1);
                v___x_2739_ = 0;
                v___x_2740_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_2727_, v___x_2739_);
                v___x_2741_ = lean_alloc_ctor(0, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2741_, 0 as u32, v___x_2740_);
                lean_inc(v_items_2728_);
                v_g_2742_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v_g_2742_, 0, v___x_2741_);
                lean_ctor_set(v_g_2742_, 1, v_items_2728_);
                lean_ctor_set_uint8(
                    v_g_2742_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_flb_2727_,
                );
                v___x_2743_ = lean_box(0);
                v___x_2744_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2744_, 0, v_g_2742_);
                lean_ctor_set(v___x_2744_, 1, v___x_2743_);
                v___x_2745_ = lean_nat_sub(v_w_2730_, v_column_2738_);
                lean_inc(v___x_2745_);
                lean_inc(v_column_2738_);
                v_r_2746_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                    v___x_2744_,
                    v_column_2738_,
                    v___x_2745_,
                );
                v_foundLine_2753_ = lean_ctor_get_uint8(
                    v_r_2746_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_space_2754_ = lean_ctor_get(v_r_2746_, 0);
                lean_inc(v_space_2754_);
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
                v___x_2734_ = lean_alloc_ctor(0, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2734_, 0 as u32, v___y_2733_);
                v___x_2735_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2735_, 0, v___x_2734_);
                lean_ctor_set(v___x_2735_, 1, v_items_2728_);
                lean_ctor_set_uint8(
                    v___x_2735_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_flb_2727_,
                );
                v___x_2736_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2736_, 0, v___x_2735_);
                lean_ctor_set(v___x_2736_, 1, v_gs_2729_);
                v___x_2737_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2737_, 0, v___x_2736_);
                lean_ctor_set(v___x_2737_, 1, v___y_2731_);
                return v___x_2737_;
            }
            2 => {
                v_foundFlattenedHardLine_2749_ = lean_ctor_get_uint8(
                    v_r_2746_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                lean_dec_ref(v_r_2746_);
                if v_foundFlattenedHardLine_2749_ == 0 {
                    v_space_2750_ = lean_ctor_get(v___y_2748_, 0);
                    lean_inc(v_space_2750_);
                    lean_dec_ref(v___y_2748_);
                    v___x_2751_ = lean_nat_dec_le(v_space_2750_, v___x_2745_);
                    lean_dec(v___x_2745_);
                    lean_dec(v_space_2750_);
                    v___y_2733_ = v___x_2751_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_2748_);
                    lean_dec(v___x_2745_);
                    v___x_2752_ = 0;
                    v___y_2733_ = v___x_2752_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2756_ == 0 {
                    v___x_2757_ = lean_nat_sub(v___x_2745_, v_space_2754_);
                    lean_inc(v_column_2738_);
                    lean_inc(v_gs_2729_);
                    v_r_u2082_2758_ =
                        l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(
                            v_gs_2729_,
                            v_column_2738_,
                            v___x_2757_,
                        );
                    v_foundLine_2759_ = lean_ctor_get_uint8(
                        v_r_u2082_2758_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_foundFlattenedHardLine_2760_ = lean_ctor_get_uint8(
                        v_r_u2082_2758_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_space_2761_ = lean_ctor_get(v_r_u2082_2758_, 0);
                    v_isSharedCheck_2769_ = (!lean_is_exclusive(v_r_u2082_2758_)) as u8;
                    if v_isSharedCheck_2769_ == 0 {
                        v___x_2763_ = v_r_u2082_2758_;
                        v_isShared_2764_ = v_isSharedCheck_2769_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_space_2761_);
                        lean_dec(v_r_u2082_2758_);
                        v___x_2763_ = lean_box(0);
                        v_isShared_2764_ = v_isSharedCheck_2769_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_space_2754_);
                    lean_inc_ref(v_r_2746_);
                    v___y_2748_ = v_r_2746_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2765_ = lean_nat_add(v_space_2754_, v_space_2761_);
                lean_dec(v_space_2761_);
                lean_dec(v_space_2754_);
                if v_isShared_2764_ == 0 {
                    lean_ctor_set(v___x_2763_, 0, v___x_2765_);
                    v___x_2767_ = v___x_2763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2768_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_foundLine_2759_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2768_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
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
    mut v_flb_2771_: *mut LeanObject,
    mut v_items_2772_: *mut LeanObject,
    mut v_gs_2773_: *mut LeanObject,
    mut v_w_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flb_boxed_2776_: u8 = 0;
    let mut v_res_2777_: *mut LeanObject = core::ptr::null_mut();
    v_flb_boxed_2776_ = (lean_unbox(v_flb_2771_) as u8);
    v_res_2777_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_2776_, v_items_2772_, v_gs_2773_, v_w_2774_, v___y_2775_);
    lean_dec(v_w_2774_);
    return v_res_2777_;
}
pub unsafe fn l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(
    mut v_msg_2792_: *mut LeanObject,
    mut v___y_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858__overap_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    v___f_2794_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0;
    v___f_2795_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1;
    v___f_2796_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2;
    v___f_2797_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3;
    v___x_2798_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4;
    v___x_2799_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2799_, 0, v___x_2798_);
    lean_ctor_set(v___x_2799_, 1, v___f_2794_);
    v___x_2800_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5;
    v___x_2801_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2801_, 0, v___x_2799_);
    lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    lean_ctor_set(v___x_2801_, 2, v___f_2795_);
    lean_ctor_set(v___x_2801_, 3, v___f_2796_);
    lean_ctor_set(v___x_2801_, 4, v___f_2797_);
    v___x_2802_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6;
    v___x_2803_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2803_, 0, v___x_2801_);
    lean_ctor_set(v___x_2803_, 1, v___x_2802_);
    v___x_2804_ = lean_box(0);
    v___x_2805_ = l_instInhabitedOfMonad___redArg(v___x_2803_, v___x_2804_);
    v___x_4858__overap_2806_ = lean_panic_fn_borrowed(v___x_2805_, v_msg_2792_);
    lean_dec(v___x_2805_);
    v___x_2807_ = lean_apply_1(v___x_4858__overap_2806_, v___y_2793_);
    return v___x_2807_;
}
pub unsafe fn l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(
    mut v_w_2808_: *mut LeanObject,
    mut v_x_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_fla_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_flb_2823_: u8 = 0;
    let mut v_tail_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_f_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indent_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeTags_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v_out_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u32 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u32 = 0;
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v___y_2867_: u8 = 0;
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v_out_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u32 = 0;
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_unused_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v_out_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u32 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fla_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u8 = 0;
    let mut v_out_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u32 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v_unused_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_snd_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_force_2964_: u8 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v_a_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: u32 = 0;
    let mut v_p_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: u8 = 0;
    let mut v_out_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2977_: u8 = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u32 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_is_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v_unused_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut v_indent_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_behavior_3052_: u8 = 0;
    let mut v___x_3053_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_unused_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut v_unused_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2809_) == 0 {
                    v___x_2811_ = lean_box(0);
                    v___x_2812_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2812_, 0, v___x_2811_);
                    lean_ctor_set(v___x_2812_, 1, v___y_2810_);
                    return v___x_2812_;
                } else {
                    v_head_2813_ = lean_ctor_get(v_x_2809_, 0);
                    v_items_2814_ = lean_ctor_get(v_head_2813_, 1);
                    lean_inc(v_items_2814_);
                    if lean_obj_tag(v_items_2814_) == 0 {
                        v_tail_2815_ = lean_ctor_get(v_x_2809_, 1);
                        lean_inc(v_tail_2815_);
                        lean_dec_ref_known(v_x_2809_, 2);
                        v_x_2809_ = v_tail_2815_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_2813_);
                        v_head_2817_ = lean_ctor_get(v_items_2814_, 0);
                        lean_inc(v_head_2817_);
                        v_tail_2818_ = lean_ctor_get(v_x_2809_, 1);
                        v_isSharedCheck_3088_ = (!lean_is_exclusive(v_x_2809_)) as u8;
                        if v_isSharedCheck_3088_ == 0 {
                            v_unused_3089_ = lean_ctor_get(v_x_2809_, 0);
                            lean_dec(v_unused_3089_);
                            v___x_2820_ = v_x_2809_;
                            v_isShared_2821_ = v_isSharedCheck_3088_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_2818_);
                            lean_dec(v_x_2809_);
                            v___x_2820_ = lean_box(0);
                            v_isShared_2821_ = v_isSharedCheck_3088_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fla_2822_ = lean_ctor_get(v_head_2813_, 0);
                lean_inc(v_fla_2822_);
                v_flb_2823_ = lean_ctor_get_uint8(
                    v_head_2813_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                lean_dec(v_head_2813_);
                v_tail_2824_ = lean_ctor_get(v_items_2814_, 1);
                v_isSharedCheck_3086_ = (!lean_is_exclusive(v_items_2814_)) as u8;
                if v_isSharedCheck_3086_ == 0 {
                    v_unused_3087_ = lean_ctor_get(v_items_2814_, 0);
                    lean_dec(v_unused_3087_);
                    v___x_2826_ = v_items_2814_;
                    v_isShared_2827_ = v_isSharedCheck_3086_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_tail_2824_);
                    lean_dec(v_items_2814_);
                    v___x_2826_ = lean_box(0);
                    v_isShared_2827_ = v_isSharedCheck_3086_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_f_2828_ = lean_ctor_get(v_head_2817_, 0);
                v_indent_2829_ = lean_ctor_get(v_head_2817_, 1);
                v_activeTags_2830_ = lean_ctor_get(v_head_2817_, 2);
                v_isSharedCheck_3085_ = (!lean_is_exclusive(v_head_2817_)) as u8;
                if v_isSharedCheck_3085_ == 0 {
                    v___x_2832_ = v_head_2817_;
                    v_isShared_2833_ = v_isSharedCheck_3085_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_activeTags_2830_);
                    lean_inc(v_indent_2829_);
                    lean_inc(v_f_2828_);
                    lean_dec(v_head_2817_);
                    v___x_2832_ = lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_3085_;
                    state = 3;
                    continue;
                }
            }
            3 => match lean_obj_tag(v_f_2828_) {
                0 => {
                    lean_del_object(v___x_2832_);
                    lean_dec(v_activeTags_2830_);
                    lean_dec(v_indent_2829_);
                    lean_del_object(v___x_2826_);
                    lean_del_object(v___x_2820_);
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
                    lean_del_object(v___x_2832_);
                    lean_dec(v_activeTags_2830_);
                    lean_del_object(v___x_2826_);
                    lean_del_object(v___x_2820_);
                    if v_flb_2823_ == 0 {
                        v___x_2872_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                        if v___x_2872_ == 0 {
                            v_out_2873_ = lean_ctor_get(v___y_2810_, 0);
                            v_isSharedCheck_2887_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2887_ == 0 {
                                v_unused_2888_ = lean_ctor_get(v___y_2810_, 1);
                                lean_dec(v_unused_2888_);
                                v___x_2875_ = v___y_2810_;
                                v_isShared_2876_ = v_isSharedCheck_2887_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_out_2873_);
                                lean_dec(v___y_2810_);
                                v___x_2875_ = lean_box(0);
                                v_isShared_2876_ = v_isSharedCheck_2887_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v_indent_2829_);
                            v_out_2889_ = lean_ctor_get(v___y_2810_, 0);
                            v_column_2890_ = lean_ctor_get(v___y_2810_, 1);
                            v_isSharedCheck_2903_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2903_ == 0 {
                                v___x_2892_ = v___y_2810_;
                                v_isShared_2893_ = v_isSharedCheck_2903_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_column_2890_);
                                lean_inc(v_out_2889_);
                                lean_dec(v___y_2810_);
                                v___x_2892_ = lean_box(0);
                                v_isShared_2893_ = v_isSharedCheck_2903_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_2904_ = l_Int_toNat(v_indent_2829_);
                        lean_dec(v_indent_2829_);
                        v___x_2905_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                        lean_dec(v_fla_2822_);
                        if v___x_2905_ == 0 {
                            v_out_2906_ = lean_ctor_get(v___y_2810_, 0);
                            v_isSharedCheck_2921_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                            if v_isSharedCheck_2921_ == 0 {
                                v_unused_2922_ = lean_ctor_get(v___y_2810_, 1);
                                lean_dec(v_unused_2922_);
                                v___x_2908_ = v___y_2810_;
                                v_isShared_2909_ = v_isSharedCheck_2921_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_out_2906_);
                                lean_dec(v___y_2810_);
                                v___x_2908_ = lean_box(0);
                                v_isShared_2909_ = v_isSharedCheck_2921_;
                                state = 13;
                                continue;
                            }
                        } else {
                            v___x_2923_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0;
                            v___x_2924_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                            v___x_2925_ = lean_nat_sub(v_w_2808_, v___x_2924_);
                            lean_inc(v_tail_2818_);
                            lean_inc(v_tail_2824_);
                            v___x_2926_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v___x_2925_, v___y_2810_);
                            lean_dec(v___x_2925_);
                            v_fst_2927_ = lean_ctor_get(v___x_2926_, 0);
                            lean_inc(v_fst_2927_);
                            if lean_obj_tag(v_fst_2927_) == 1 {
                                v_head_2928_ = lean_ctor_get(v_fst_2927_, 0);
                                v_snd_2929_ = lean_ctor_get(v___x_2926_, 1);
                                lean_inc(v_snd_2929_);
                                lean_dec_ref(v___x_2926_);
                                v_fla_2930_ = lean_ctor_get(v_head_2928_, 0);
                                v___x_2931_ =
                                    l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2930_);
                                if v___x_2931_ == 0 {
                                    lean_dec_ref_known(v_fst_2927_, 2);
                                    v_out_2932_ = lean_ctor_get(v_snd_2929_, 0);
                                    v_isSharedCheck_2947_ = (!lean_is_exclusive(v_snd_2929_)) as u8;
                                    if v_isSharedCheck_2947_ == 0 {
                                        v_unused_2948_ = lean_ctor_get(v_snd_2929_, 1);
                                        lean_dec(v_unused_2948_);
                                        v___x_2934_ = v_snd_2929_;
                                        v_isShared_2935_ = v_isSharedCheck_2947_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_out_2932_);
                                        lean_dec(v_snd_2929_);
                                        v___x_2934_ = lean_box(0);
                                        v_isShared_2935_ = v_isSharedCheck_2947_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_2904_);
                                    lean_dec(v_tail_2824_);
                                    lean_dec(v_tail_2818_);
                                    v_out_2949_ = lean_ctor_get(v_snd_2929_, 0);
                                    v_column_2950_ = lean_ctor_get(v_snd_2929_, 1);
                                    v_isSharedCheck_2960_ = (!lean_is_exclusive(v_snd_2929_)) as u8;
                                    if v_isSharedCheck_2960_ == 0 {
                                        v___x_2952_ = v_snd_2929_;
                                        v_isShared_2953_ = v_isSharedCheck_2960_;
                                        state = 17;
                                        continue;
                                    } else {
                                        lean_inc(v_column_2950_);
                                        lean_inc(v_out_2949_);
                                        lean_dec(v_snd_2929_);
                                        v___x_2952_ = lean_box(0);
                                        v_isShared_2953_ = v_isSharedCheck_2960_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_fst_2927_);
                                lean_dec(v___x_2904_);
                                lean_dec(v_tail_2824_);
                                lean_dec(v_tail_2818_);
                                v_snd_2961_ = lean_ctor_get(v___x_2926_, 1);
                                lean_inc(v_snd_2961_);
                                lean_dec_ref(v___x_2926_);
                                v___x_2962_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0;
                                v___x_2963_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_2962_, v_snd_2961_);
                                return v___x_2963_;
                            }
                        }
                    }
                }
                2 => {
                    lean_del_object(v___x_2832_);
                    lean_dec(v_activeTags_2830_);
                    lean_del_object(v___x_2826_);
                    lean_del_object(v___x_2820_);
                    v_force_2964_ = lean_ctor_get_uint8(v_f_2828_, 0 as u32);
                    lean_dec_ref_known(v_f_2828_, 0);
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
                    lean_del_object(v___x_2820_);
                    v_a_2966_ = lean_ctor_get(v_f_2828_, 0);
                    v_isSharedCheck_3024_ = (!lean_is_exclusive(v_f_2828_)) as u8;
                    if v_isSharedCheck_3024_ == 0 {
                        v___x_2968_ = v_f_2828_;
                        v_isShared_2969_ = v_isSharedCheck_3024_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2966_);
                        lean_dec(v_f_2828_);
                        v___x_2968_ = lean_box(0);
                        v_isShared_2969_ = v_isSharedCheck_3024_;
                        state = 19;
                        continue;
                    }
                }
                4 => {
                    lean_del_object(v___x_2820_);
                    v_indent_3025_ = lean_ctor_get(v_f_2828_, 0);
                    lean_inc(v_indent_3025_);
                    v_f_3026_ = lean_ctor_get(v_f_2828_, 1);
                    lean_inc(v_f_3026_);
                    lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3027_ = lean_int_add(v_indent_2829_, v_indent_3025_);
                    lean_dec(v_indent_3025_);
                    lean_dec(v_indent_2829_);
                    if v_isShared_2833_ == 0 {
                        lean_ctor_set(v___x_2832_, 1, v___x_3027_);
                        lean_ctor_set(v___x_2832_, 0, v_f_3026_);
                        v___x_3029_ = v___x_2832_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_f_3026_);
                        lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3027_);
                        lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_activeTags_2830_);
                        v___x_3029_ = v_reuseFailAlloc_3035_;
                        state = 27;
                        continue;
                    }
                }
                5 => {
                    v_a_3036_ = lean_ctor_get(v_f_2828_, 0);
                    lean_inc(v_a_3036_);
                    v_a_3037_ = lean_ctor_get(v_f_2828_, 1);
                    lean_inc(v_a_3037_);
                    lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3038_ = lean_unsigned_to_nat(0);
                    lean_inc(v_indent_2829_);
                    if v_isShared_2833_ == 0 {
                        lean_ctor_set(v___x_2832_, 2, v___x_3038_);
                        lean_ctor_set(v___x_2832_, 0, v_a_3036_);
                        v___x_3040_ = v___x_2832_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3036_);
                        lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_indent_2829_);
                        lean_ctor_set(v_reuseFailAlloc_3050_, 2, v___x_3038_);
                        v___x_3040_ = v_reuseFailAlloc_3050_;
                        state = 29;
                        continue;
                    }
                }
                6 => {
                    lean_del_object(v___x_2820_);
                    v_a_3051_ = lean_ctor_get(v_f_2828_, 0);
                    lean_inc(v_a_3051_);
                    v_behavior_3052_ = lean_ctor_get_uint8(
                        v_f_2828_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_f_2828_, 1);
                    v___x_3053_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_2822_);
                    if v___x_3053_ == 0 {
                        if v_isShared_2833_ == 0 {
                            lean_ctor_set(v___x_2832_, 0, v_a_3051_);
                            v___x_3055_ = v___x_2832_;
                            state = 32;
                            continue;
                        } else {
                            v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3051_);
                            lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_indent_2829_);
                            lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_activeTags_2830_);
                            v___x_3055_ = v_reuseFailAlloc_3065_;
                            state = 32;
                            continue;
                        }
                    } else {
                        if v_isShared_2833_ == 0 {
                            lean_ctor_set(v___x_2832_, 0, v_a_3051_);
                            v___x_3067_ = v___x_2832_;
                            state = 34;
                            continue;
                        } else {
                            v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3051_);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_indent_2829_);
                            lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_activeTags_2830_);
                            v___x_3067_ = v_reuseFailAlloc_3073_;
                            state = 34;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_del_object(v___x_2820_);
                    v_a_3074_ = lean_ctor_get(v_f_2828_, 1);
                    lean_inc(v_a_3074_);
                    lean_dec_ref_known(v_f_2828_, 2);
                    v___x_3075_ = lean_unsigned_to_nat(1);
                    v___x_3076_ = lean_nat_add(v_activeTags_2830_, v___x_3075_);
                    lean_dec(v_activeTags_2830_);
                    if v_isShared_2833_ == 0 {
                        lean_ctor_set(v___x_2832_, 2, v___x_3076_);
                        lean_ctor_set(v___x_2832_, 0, v_a_3074_);
                        v___x_3078_ = v___x_2832_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3074_);
                        lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_indent_2829_);
                        lean_ctor_set(v_reuseFailAlloc_3084_, 2, v___x_3076_);
                        v___x_3078_ = v_reuseFailAlloc_3084_;
                        state = 36;
                        continue;
                    }
                }
            },
            4 => {
                v_out_2835_ = lean_ctor_get(v___y_2810_, 0);
                v_column_2836_ = lean_ctor_get(v___y_2810_, 1);
                v_isSharedCheck_2865_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                if v_isSharedCheck_2865_ == 0 {
                    v___x_2838_ = v___y_2810_;
                    v_isShared_2839_ = v_isSharedCheck_2865_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_column_2836_);
                    lean_inc(v_out_2835_);
                    lean_dec(v___y_2810_);
                    v___x_2838_ = lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2865_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc(v_column_2836_);
                v___x_2840_ = lean_nat_to_int(v_column_2836_);
                v___x_2841_ = lean_int_dec_lt(v___x_2840_, v_indent_2829_);
                if v___x_2841_ == 0 {
                    lean_dec(v___x_2840_);
                    lean_dec(v_column_2836_);
                    v___x_2842_ = l_Int_toNat(v_indent_2829_);
                    lean_dec(v_indent_2829_);
                    v___x_2843_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                    v___x_2844_ = 32;
                    lean_inc(v___x_2842_);
                    v___x_2845_ = lean_string_pushn(v___x_2843_, v___x_2844_, v___x_2842_);
                    v___x_2846_ = lean_string_append(v_out_2835_, v___x_2845_);
                    lean_dec_ref(v___x_2845_);
                    if v_isShared_2839_ == 0 {
                        lean_ctor_set(v___x_2838_, 1, v___x_2842_);
                        lean_ctor_set(v___x_2838_, 0, v___x_2846_);
                        v___x_2848_ = v___x_2838_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2846_);
                        lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2842_);
                        v___x_2848_ = v_reuseFailAlloc_2851_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2852_ = l_Std_Format_isEmpty___closed__0;
                    v___x_2853_ = 32;
                    v___x_2854_ = lean_int_sub(v_indent_2829_, v___x_2840_);
                    lean_dec(v___x_2840_);
                    lean_dec(v_indent_2829_);
                    v___x_2855_ = l_Int_toNat(v___x_2854_);
                    lean_dec(v___x_2854_);
                    v___x_2856_ = lean_string_pushn(v___x_2852_, v___x_2853_, v___x_2855_);
                    v___x_2857_ = lean_string_append(v_out_2835_, v___x_2856_);
                    v___x_2858_ = lean_string_length(v___x_2856_);
                    lean_dec_ref(v___x_2856_);
                    v___x_2859_ = lean_nat_add(v_column_2836_, v___x_2858_);
                    lean_dec(v___x_2858_);
                    lean_dec(v_column_2836_);
                    if v_isShared_2839_ == 0 {
                        lean_ctor_set(v___x_2838_, 1, v___x_2859_);
                        lean_ctor_set(v___x_2838_, 0, v___x_2857_);
                        v___x_2861_ = v___x_2838_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2857_);
                        lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2859_);
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
                    lean_dec(v_indent_2829_);
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
                lean_dec(v_indent_2829_);
                v___x_2878_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2879_ = 32;
                lean_inc(v___x_2877_);
                v___x_2880_ = lean_string_pushn(v___x_2878_, v___x_2879_, v___x_2877_);
                v___x_2881_ = lean_string_append(v_out_2873_, v___x_2880_);
                lean_dec_ref(v___x_2880_);
                if v_isShared_2876_ == 0 {
                    lean_ctor_set(v___x_2875_, 1, v___x_2877_);
                    lean_ctor_set(v___x_2875_, 0, v___x_2881_);
                    v___x_2883_ = v___x_2875_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2881_);
                    lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2877_);
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
                v___x_2896_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once), _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
                v___x_2897_ = lean_nat_add(v_column_2890_, v___x_2896_);
                lean_dec(v_column_2890_);
                if v_isShared_2893_ == 0 {
                    lean_ctor_set(v___x_2892_, 1, v___x_2897_);
                    lean_ctor_set(v___x_2892_, 0, v___x_2895_);
                    v___x_2899_ = v___x_2892_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2895_);
                    lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2897_);
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
                lean_inc(v___x_2904_);
                v___x_2912_ = lean_string_pushn(v___x_2910_, v___x_2911_, v___x_2904_);
                v___x_2913_ = lean_string_append(v_out_2906_, v___x_2912_);
                lean_dec_ref(v___x_2912_);
                if v_isShared_2909_ == 0 {
                    lean_ctor_set(v___x_2908_, 1, v___x_2904_);
                    lean_ctor_set(v___x_2908_, 0, v___x_2913_);
                    v___x_2915_ = v___x_2908_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2904_);
                    v___x_2915_ = v_reuseFailAlloc_2920_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2916_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v_w_2808_, v___x_2915_);
                v_fst_2917_ = lean_ctor_get(v___x_2916_, 0);
                lean_inc(v_fst_2917_);
                v_snd_2918_ = lean_ctor_get(v___x_2916_, 1);
                lean_inc(v_snd_2918_);
                lean_dec_ref(v___x_2916_);
                v_x_2809_ = v_fst_2917_;
                v___y_2810_ = v_snd_2918_;
                state = 0;
                continue;
            }
            15 => {
                v___x_2936_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2937_ = 32;
                lean_inc(v___x_2904_);
                v___x_2938_ = lean_string_pushn(v___x_2936_, v___x_2937_, v___x_2904_);
                v___x_2939_ = lean_string_append(v_out_2932_, v___x_2938_);
                lean_dec_ref(v___x_2938_);
                if v_isShared_2935_ == 0 {
                    lean_ctor_set(v___x_2934_, 1, v___x_2904_);
                    lean_ctor_set(v___x_2934_, 0, v___x_2939_);
                    v___x_2941_ = v___x_2934_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2939_);
                    lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2904_);
                    v___x_2941_ = v_reuseFailAlloc_2946_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2942_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_tail_2824_, v_tail_2818_, v_w_2808_, v___x_2941_);
                v_fst_2943_ = lean_ctor_get(v___x_2942_, 0);
                lean_inc(v_fst_2943_);
                v_snd_2944_ = lean_ctor_get(v___x_2942_, 1);
                lean_inc(v_snd_2944_);
                lean_dec_ref(v___x_2942_);
                v_x_2809_ = v_fst_2943_;
                v___y_2810_ = v_snd_2944_;
                state = 0;
                continue;
            }
            17 => {
                v___x_2954_ = lean_string_append(v_out_2949_, v___x_2923_);
                v___x_2955_ = lean_nat_add(v_column_2950_, v___x_2924_);
                lean_dec(v_column_2950_);
                if v_isShared_2953_ == 0 {
                    lean_ctor_set(v___x_2952_, 1, v___x_2955_);
                    lean_ctor_set(v___x_2952_, 0, v___x_2954_);
                    v___x_2957_ = v___x_2952_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2954_);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2955_);
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
                lean_inc_ref(v_a_2966_);
                v_p_2971_ = lean_string_posof(v_a_2966_, v___x_2970_);
                v___x_2972_ = lean_string_utf8_byte_size(v_a_2966_);
                v___x_2973_ = lean_nat_dec_eq(v_p_2971_, v___x_2972_);
                if v___x_2973_ == 0 {
                    v_out_2974_ = lean_ctor_get(v___y_2810_, 0);
                    v_isSharedCheck_3008_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v_unused_3009_ = lean_ctor_get(v___y_2810_, 1);
                        lean_dec(v_unused_3009_);
                        v___x_2976_ = v___y_2810_;
                        v_isShared_2977_ = v_isSharedCheck_3008_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_out_2974_);
                        lean_dec(v___y_2810_);
                        v___x_2976_ = lean_box(0);
                        v_isShared_2977_ = v_isSharedCheck_3008_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec(v_p_2971_);
                    lean_del_object(v___x_2968_);
                    lean_del_object(v___x_2832_);
                    lean_dec(v_activeTags_2830_);
                    lean_dec(v_indent_2829_);
                    lean_del_object(v___x_2826_);
                    v_out_3010_ = lean_ctor_get(v___y_2810_, 0);
                    v_column_3011_ = lean_ctor_get(v___y_2810_, 1);
                    v_isSharedCheck_3023_ = (!lean_is_exclusive(v___y_2810_)) as u8;
                    if v_isSharedCheck_3023_ == 0 {
                        v___x_3013_ = v___y_2810_;
                        v_isShared_3014_ = v_isSharedCheck_3023_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_column_3011_);
                        lean_inc(v_out_3010_);
                        lean_dec(v___y_2810_);
                        v___x_3013_ = lean_box(0);
                        v_isShared_3014_ = v_isSharedCheck_3023_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                v___x_2978_ = lean_unsigned_to_nat(0);
                v___x_2979_ = lean_string_utf8_extract(v_a_2966_, v___x_2978_, v_p_2971_);
                v___x_2980_ = lean_string_append(v_out_2974_, v___x_2979_);
                lean_dec_ref(v___x_2979_);
                v___x_2981_ = l_Int_toNat(v_indent_2829_);
                v___x_2982_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0;
                v___x_2983_ = 32;
                lean_inc(v___x_2981_);
                v___x_2984_ = lean_string_pushn(v___x_2982_, v___x_2983_, v___x_2981_);
                v___x_2985_ = lean_string_append(v___x_2980_, v___x_2984_);
                lean_dec_ref(v___x_2984_);
                if v_isShared_2977_ == 0 {
                    lean_ctor_set(v___x_2976_, 1, v___x_2981_);
                    lean_ctor_set(v___x_2976_, 0, v___x_2985_);
                    v___x_2987_ = v___x_2976_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2985_);
                    lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2981_);
                    v___x_2987_ = v_reuseFailAlloc_3007_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2988_ = lean_string_utf8_next(v_a_2966_, v_p_2971_);
                lean_dec(v_p_2971_);
                v___x_2989_ = lean_string_utf8_extract(v_a_2966_, v___x_2988_, v___x_2972_);
                lean_dec(v___x_2988_);
                lean_dec_ref(v_a_2966_);
                if v_isShared_2969_ == 0 {
                    lean_ctor_set(v___x_2968_, 0, v___x_2989_);
                    v___x_2991_ = v___x_2968_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2989_);
                    v___x_2991_ = v_reuseFailAlloc_3006_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2833_ == 0 {
                    lean_ctor_set(v___x_2832_, 0, v___x_2991_);
                    v___x_2993_ = v___x_2832_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2991_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_indent_2829_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_activeTags_2830_);
                    v___x_2993_ = v_reuseFailAlloc_3005_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 0, v___x_2993_);
                    v_is_2995_ = v___x_2826_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2993_);
                    lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_tail_2824_);
                    v_is_2995_ = v_reuseFailAlloc_3004_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_2996_ = lean_box(1);
                v___x_2997_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_2822_, v___x_2996_);
                if v___x_2997_ == 0 {
                    lean_dec(v_fla_2822_);
                    v___x_2998_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_2823_, v_is_2995_, v_tail_2818_, v_w_2808_, v___x_2987_);
                    v_fst_2999_ = lean_ctor_get(v___x_2998_, 0);
                    lean_inc(v_fst_2999_);
                    v_snd_3000_ = lean_ctor_get(v___x_2998_, 1);
                    lean_inc(v_snd_3000_);
                    lean_dec_ref(v___x_2998_);
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
                lean_dec_ref(v_a_2966_);
                v___x_3017_ = lean_nat_add(v_column_3011_, v___x_3016_);
                lean_dec(v___x_3016_);
                lean_dec(v_column_3011_);
                if v_isShared_3014_ == 0 {
                    lean_ctor_set(v___x_3013_, 1, v___x_3017_);
                    lean_ctor_set(v___x_3013_, 0, v___x_3015_);
                    v___x_3019_ = v___x_3013_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3017_);
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
                    lean_ctor_set(v___x_2826_, 0, v___x_3029_);
                    v___x_3031_ = v___x_2826_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3029_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_tail_2824_);
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
                v___x_3041_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3041_, 0, v_a_3037_);
                lean_ctor_set(v___x_3041_, 1, v_indent_2829_);
                lean_ctor_set(v___x_3041_, 2, v_activeTags_2830_);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 0, v___x_3041_);
                    v___x_3043_ = v___x_2826_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3041_);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_tail_2824_);
                    v___x_3043_ = v_reuseFailAlloc_3049_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_2821_ == 0 {
                    lean_ctor_set(v___x_2820_, 1, v___x_3043_);
                    lean_ctor_set(v___x_2820_, 0, v___x_3040_);
                    v___x_3045_ = v___x_2820_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3040_);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3043_);
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
                v___x_3056_ = lean_box(0);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 1, v___x_3056_);
                    lean_ctor_set(v___x_2826_, 0, v___x_3055_);
                    v___x_3058_ = v___x_2826_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3055_);
                    lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3056_);
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
                v_fst_3061_ = lean_ctor_get(v___x_3060_, 0);
                lean_inc(v_fst_3061_);
                v_snd_3062_ = lean_ctor_get(v___x_3060_, 1);
                lean_inc(v_snd_3062_);
                lean_dec_ref(v___x_3060_);
                v_x_2809_ = v_fst_3061_;
                v___y_2810_ = v_snd_3062_;
                state = 0;
                continue;
            }
            34 => {
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 0, v___x_3067_);
                    v___x_3069_ = v___x_2826_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3067_);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_tail_2824_);
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
                    lean_ctor_set(v___x_2826_, 0, v___x_3078_);
                    v___x_3080_ = v___x_2826_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3078_);
                    lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_tail_2824_);
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
    mut v_w_3090_: *mut LeanObject,
    mut v_x_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3093_: *mut LeanObject = core::ptr::null_mut();
    v_res_3093_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_3090_, v_x_3091_, v___y_3092_);
    lean_dec(v_w_3090_);
    return v_res_3093_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
    mut v_f_3094_: *mut LeanObject,
    mut v_w_3095_: *mut LeanObject,
    mut v_indent_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    v___x_3098_ = lean_box(1);
    v___x_3099_ = 0;
    v___x_3100_ = lean_nat_to_int(v_indent_3096_);
    v___x_3101_ = lean_unsigned_to_nat(0);
    v___x_3102_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3102_, 0, v_f_3094_);
    lean_ctor_set(v___x_3102_, 1, v___x_3100_);
    lean_ctor_set(v___x_3102_, 2, v___x_3101_);
    v___x_3103_ = lean_box(0);
    v___x_3104_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3104_, 0, v___x_3102_);
    lean_ctor_set(v___x_3104_, 1, v___x_3103_);
    v___x_3105_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_3105_, 0, v___x_3098_);
    lean_ctor_set(v___x_3105_, 1, v___x_3104_);
    lean_ctor_set_uint8(
        v___x_3105_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_3099_,
    );
    v___x_3106_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3106_, 0, v___x_3105_);
    lean_ctor_set(v___x_3106_, 1, v___x_3103_);
    v___x_3107_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_3095_, v___x_3106_, v___y_3097_);
    return v___x_3107_;
}
pub unsafe fn l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(
    mut v_f_3108_: *mut LeanObject,
    mut v_w_3109_: *mut LeanObject,
    mut v_indent_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3112_: *mut LeanObject = core::ptr::null_mut();
    v_res_3112_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
        v_f_3108_,
        v_w_3109_,
        v_indent_3110_,
        v___y_3111_,
    );
    lean_dec(v_w_3109_);
    return v_res_3112_;
}
pub unsafe fn l_Std_Format_pretty(
    mut v_f_3113_: *mut LeanObject,
    mut v_width_3114_: *mut LeanObject,
    mut v_indent_3115_: *mut LeanObject,
    mut v_column_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3117_ = l_Std_Format_isEmpty___closed__0;
    v___x_3118_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3118_, 0, v___x_3117_);
    lean_ctor_set(v___x_3118_, 1, v_column_3116_);
    v___x_3119_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(
        v_f_3113_,
        v_width_3114_,
        v_indent_3115_,
        v___x_3118_,
    );
    v_snd_3120_ = lean_ctor_get(v___x_3119_, 1);
    lean_inc(v_snd_3120_);
    lean_dec_ref(v___x_3119_);
    v_out_3121_ = lean_ctor_get(v_snd_3120_, 0);
    lean_inc_ref(v_out_3121_);
    lean_dec(v_snd_3120_);
    return v_out_3121_;
}
pub unsafe fn l_Std_Format_pretty___boxed(
    mut v_f_3122_: *mut LeanObject,
    mut v_width_3123_: *mut LeanObject,
    mut v_indent_3124_: *mut LeanObject,
    mut v_column_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3126_: *mut LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Std_Format_pretty(v_f_3122_, v_width_3123_, v_indent_3124_, v_column_3125_);
    lean_dec(v_width_3123_);
    return v_res_3126_;
}
pub unsafe fn l_Std_instToFormatFormat___lam__0(mut v_f_3127_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_f_3127_);
    return v_f_3127_;
}
pub unsafe fn l_Std_instToFormatFormat___lam__0___boxed(
    mut v_f_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3129_: *mut LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_Std_instToFormatFormat___lam__0(v_f_3128_);
    lean_dec(v_f_3128_);
    return v_res_3129_;
}
pub unsafe fn l_Std_instToFormatString___lam__0(mut v_s_3132_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3133_, 0, v_s_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Std_Format_joinSep___redArg___lam__0(
    mut v_x_3136_: *mut LeanObject,
    mut v_inst_3137_: *mut LeanObject,
    mut v_x1_3138_: *mut LeanObject,
    mut v_x2_3139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    v___x_3140_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3140_, 0, v_x1_3138_);
    lean_ctor_set(v___x_3140_, 1, v_x_3136_);
    v___x_3141_ = lean_apply_1(v_inst_3137_, v_x2_3139_);
    v___x_3142_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3142_, 0, v___x_3140_);
    lean_ctor_set(v___x_3142_, 1, v___x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Std_Format_joinSep___redArg(
    mut v_inst_3143_: *mut LeanObject,
    mut v_x_3144_: *mut LeanObject,
    mut v_x_3145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3144_) == 0 {
        let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3145_);
        lean_dec_ref(v_inst_3143_);
        v___x_3146_ = lean_box(0);
        return v___x_3146_;
    } else {
        let mut v_tail_3147_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3147_ = lean_ctor_get(v_x_3144_, 1);
        if lean_obj_tag(v_tail_3147_) == 0 {
            let mut v_head_3148_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3145_);
            v_head_3148_ = lean_ctor_get(v_x_3144_, 0);
            lean_inc(v_head_3148_);
            lean_dec_ref_known(v_x_3144_, 2);
            v___x_3149_ = lean_apply_1(v_inst_3143_, v_head_3148_);
            return v___x_3149_;
        } else {
            let mut v_head_3150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3151_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3147_);
            v_head_3150_ = lean_ctor_get(v_x_3144_, 0);
            lean_inc(v_head_3150_);
            lean_dec_ref_known(v_x_3144_, 2);
            lean_inc_ref(v_inst_3143_);
            v___f_3151_ = lean_alloc_closure(
                l_Std_Format_joinSep___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                2,
            );
            lean_closure_set(v___f_3151_, 0, v_x_3145_);
            lean_closure_set(v___f_3151_, 1, v_inst_3143_);
            v___x_3152_ = lean_apply_1(v_inst_3143_, v_head_3150_);
            v___x_3153_ = l_List_foldl___redArg(v___f_3151_, v___x_3152_, v_tail_3147_);
            return v___x_3153_;
        }
    }
}
pub unsafe fn l_Std_Format_joinSep(
    mut v_00_u03b1_3154_: *mut LeanObject,
    mut v_inst_3155_: *mut LeanObject,
    mut v_x_3156_: *mut LeanObject,
    mut v_x_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Std_Format_joinSep___redArg(v_inst_3155_, v_x_3156_, v_x_3157_);
    return v___x_3158_;
}
pub unsafe fn l_Std_Format_prefixJoin___redArg___lam__0(
    mut v_pre_3159_: *mut LeanObject,
    mut v_inst_3160_: *mut LeanObject,
    mut v_x1_3161_: *mut LeanObject,
    mut v_x2_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    v___x_3163_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3163_, 0, v_x1_3161_);
    lean_ctor_set(v___x_3163_, 1, v_pre_3159_);
    v___x_3164_ = lean_apply_1(v_inst_3160_, v_x2_3162_);
    v___x_3165_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3165_, 0, v___x_3163_);
    lean_ctor_set(v___x_3165_, 1, v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_Format_prefixJoin___redArg(
    mut v_inst_3166_: *mut LeanObject,
    mut v_pre_3167_: *mut LeanObject,
    mut v_x_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___f_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3168_) == 0 {
                    lean_dec(v_pre_3167_);
                    lean_dec_ref(v_inst_3166_);
                    v___x_3169_ = lean_box(0);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = lean_ctor_get(v_x_3168_, 0);
                    v_tail_3171_ = lean_ctor_get(v_x_3168_, 1);
                    v_isSharedCheck_3181_ = (!lean_is_exclusive(v_x_3168_)) as u8;
                    if v_isSharedCheck_3181_ == 0 {
                        v___x_3173_ = v_x_3168_;
                        v_isShared_3174_ = v_isSharedCheck_3181_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3171_);
                        lean_inc(v_head_3170_);
                        lean_dec(v_x_3168_);
                        v___x_3173_ = lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3181_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_3166_);
                lean_inc(v_pre_3167_);
                v___f_3175_ = lean_alloc_closure(
                    l_Std_Format_prefixJoin___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3175_, 0, v_pre_3167_);
                lean_closure_set(v___f_3175_, 1, v_inst_3166_);
                v___x_3176_ = lean_apply_1(v_inst_3166_, v_head_3170_);
                if v_isShared_3174_ == 0 {
                    lean_ctor_set_tag(v___x_3173_, 5);
                    lean_ctor_set(v___x_3173_, 1, v___x_3176_);
                    lean_ctor_set(v___x_3173_, 0, v_pre_3167_);
                    v___x_3178_ = v___x_3173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_pre_3167_);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3176_);
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
    mut v_00_u03b1_3182_: *mut LeanObject,
    mut v_inst_3183_: *mut LeanObject,
    mut v_pre_3184_: *mut LeanObject,
    mut v_x_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_Std_Format_prefixJoin___redArg(v_inst_3183_, v_pre_3184_, v_x_3185_);
    return v___x_3186_;
}
pub unsafe fn l_Std_Format_joinSuffix___redArg___lam__0(
    mut v_inst_3187_: *mut LeanObject,
    mut v_x_3188_: *mut LeanObject,
    mut v_x1_3189_: *mut LeanObject,
    mut v_x2_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = lean_apply_1(v_inst_3187_, v_x2_3190_);
    v___x_3192_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3192_, 0, v_x1_3189_);
    lean_ctor_set(v___x_3192_, 1, v___x_3191_);
    v___x_3193_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    lean_ctor_set(v___x_3193_, 1, v_x_3188_);
    return v___x_3193_;
}
pub unsafe fn l_Std_Format_joinSuffix___redArg(
    mut v_inst_3194_: *mut LeanObject,
    mut v_x_3195_: *mut LeanObject,
    mut v_x_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___f_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3195_) == 0 {
                    lean_dec(v_x_3196_);
                    lean_dec_ref(v_inst_3194_);
                    v___x_3197_ = lean_box(0);
                    return v___x_3197_;
                } else {
                    v_head_3198_ = lean_ctor_get(v_x_3195_, 0);
                    v_tail_3199_ = lean_ctor_get(v_x_3195_, 1);
                    v_isSharedCheck_3209_ = (!lean_is_exclusive(v_x_3195_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3201_ = v_x_3195_;
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3199_);
                        lean_inc(v_head_3198_);
                        lean_dec(v_x_3195_);
                        v___x_3201_ = lean_box(0);
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3196_);
                lean_inc_ref(v_inst_3194_);
                v___f_3203_ = lean_alloc_closure(
                    l_Std_Format_joinSuffix___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3203_, 0, v_inst_3194_);
                lean_closure_set(v___f_3203_, 1, v_x_3196_);
                v___x_3204_ = lean_apply_1(v_inst_3194_, v_head_3198_);
                if v_isShared_3202_ == 0 {
                    lean_ctor_set_tag(v___x_3201_, 5);
                    lean_ctor_set(v___x_3201_, 1, v_x_3196_);
                    lean_ctor_set(v___x_3201_, 0, v___x_3204_);
                    v___x_3206_ = v___x_3201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3204_);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_x_3196_);
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
    mut v_00_u03b1_3210_: *mut LeanObject,
    mut v_inst_3211_: *mut LeanObject,
    mut v_x_3212_: *mut LeanObject,
    mut v_x_3213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    v___x_3214_ = l_Std_Format_joinSuffix___redArg(v_inst_3211_, v_x_3212_, v_x_3213_);
    return v___x_3214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Format_instInhabitedFlattenBehavior_default =
        _init_l_Std_Format_instInhabitedFlattenBehavior_default();
    l_Std_Format_instInhabitedFlattenBehavior = _init_l_Std_Format_instInhabitedFlattenBehavior();
    l_Std_instInhabitedFormat_default = _init_l_Std_instInhabitedFormat_default();
    lean_mark_persistent(l_Std_instInhabitedFormat_default);
    l_Std_instInhabitedFormat = _init_l_Std_instInhabitedFormat();
    lean_mark_persistent(l_Std_instInhabitedFormat);
    l_Std_Format_defIndent = _init_l_Std_Format_defIndent();
    lean_mark_persistent(l_Std_Format_defIndent);
    l_Std_Format_defUnicode = _init_l_Std_Format_defUnicode();
    l_Std_Format_defWidth = _init_l_Std_Format_defWidth();
    lean_mark_persistent(l_Std_Format_defWidth);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Format_Basic(builtin);
}
