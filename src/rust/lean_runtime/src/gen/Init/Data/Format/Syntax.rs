// Lean compiler output
// Module: Init.Data.Format.Syntax
// Imports: Init.Data.ToString.Name Init.Data.ToString.Basic Init.Data.Format.Instances Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Instances::{
    initialize_Init_Data_Format_Instances, runtime_initialize_Init_Data_Format_Instances,
};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_replacePrefix;
use crate::r#gen::Init::Prelude::{l_Function_comp, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value:
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
    m_data: [58, 0],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value:
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
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value
) as *mut LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value:
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
    m_data: [33, 58, 0],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
) as *mut LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value:
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
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value) as *mut LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Syntax_formatStxAux___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Syntax_formatStxAux___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__4_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__1_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__5_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__6_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [60, 109, 105, 115, 115, 105, 110, 103, 62, 0],
};
static mut l_Lean_Syntax_formatStxAux___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__7_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__8_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [46, 46, 0],
};
static mut l_Lean_Syntax_formatStxAux___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__10_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Syntax_formatStxAux___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Syntax_formatStxAux___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__11_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__13_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Syntax_formatStxAux___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__12_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value) as *mut LeanObject;
static l_Lean_Syntax_formatStxAux___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l_Lean_Syntax_formatStxAux___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static mut l_Lean_Syntax_formatStxAux___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__15_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value) as *mut LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Syntax_formatStxAux___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Syntax_formatStxAux___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__19_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__16_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__20_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__20_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__21_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Syntax_formatStxAux___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__21_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__22_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Syntax_formatStxAux___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value) as *mut LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__23_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value) as *mut LeanObject],
};
static mut l_Lean_Syntax_formatStxAux___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__23_value) as *mut LeanObject;
pub static l_Lean_Syntax_instToFormat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_instToFormat___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_instToFormat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Syntax_instToFormat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Syntax_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Syntax_instToString___closed__1_value: LeanClosureObject<5> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Syntax_instToString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Syntax_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value) as *mut LeanObject;
pub static l_Lean_Syntax_instToFormatTSyntax___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToFormatTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToFormatTSyntax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormatTSyntax___closed__0_value) as *mut LeanObject;
pub static l_Lean_Syntax_instToStringTSyntax___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToStringTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToStringTSyntax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToStringTSyntax___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
    mut v_showInfo_296_: u8,
    mut v_info_297_: *mut LeanObject,
    mut v_f_298_: *mut LeanObject,
) -> *mut LeanObject {
    if v_showInfo_296_ == 1 {
        match lean_obj_tag(v_info_297_) {
            0 => {
                let mut v_leading_299_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pos_300_: *mut LeanObject = core::ptr::null_mut();
                let mut v_trailing_301_: *mut LeanObject = core::ptr::null_mut();
                let mut v_endPos_302_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_303_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_304_: *mut LeanObject = core::ptr::null_mut();
                let mut v_stopPos_305_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_311_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_312_: *mut LeanObject = core::ptr::null_mut();
                let mut v_stopPos_313_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
                v_leading_299_ = lean_ctor_get(v_info_297_, 0);
                lean_inc_ref(v_leading_299_);
                v_pos_300_ = lean_ctor_get(v_info_297_, 1);
                lean_inc(v_pos_300_);
                v_trailing_301_ = lean_ctor_get(v_info_297_, 2);
                lean_inc_ref(v_trailing_301_);
                v_endPos_302_ = lean_ctor_get(v_info_297_, 3);
                lean_inc(v_endPos_302_);
                lean_dec_ref_known(v_info_297_, 4);
                v_str_303_ = lean_ctor_get(v_leading_299_, 0);
                lean_inc_ref(v_str_303_);
                v_startPos_304_ = lean_ctor_get(v_leading_299_, 1);
                lean_inc(v_startPos_304_);
                v_stopPos_305_ = lean_ctor_get(v_leading_299_, 2);
                lean_inc(v_stopPos_305_);
                lean_dec_ref(v_leading_299_);
                v___x_306_ = lean_string_utf8_extract(v_str_303_, v_startPos_304_, v_stopPos_305_);
                lean_dec(v_stopPos_305_);
                lean_dec(v_startPos_304_);
                lean_dec_ref(v_str_303_);
                v___x_307_ = l_String_quote(v___x_306_);
                v___x_308_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_308_, 0, v___x_307_);
                v___x_309_ =
                    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                v___x_310_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_310_, 0, v___x_308_);
                lean_ctor_set(v___x_310_, 1, v___x_309_);
                v_str_311_ = lean_ctor_get(v_trailing_301_, 0);
                lean_inc_ref(v_str_311_);
                v_startPos_312_ = lean_ctor_get(v_trailing_301_, 1);
                lean_inc(v_startPos_312_);
                v_stopPos_313_ = lean_ctor_get(v_trailing_301_, 2);
                lean_inc(v_stopPos_313_);
                lean_dec_ref(v_trailing_301_);
                v___x_314_ = l_Nat_reprFast(v_pos_300_);
                v___x_315_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_315_, 0, v___x_314_);
                v___x_316_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_316_, 0, v___x_310_);
                lean_ctor_set(v___x_316_, 1, v___x_315_);
                v___x_317_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_317_, 0, v___x_316_);
                lean_ctor_set(v___x_317_, 1, v___x_309_);
                v___x_318_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_318_, 0, v___x_317_);
                lean_ctor_set(v___x_318_, 1, v_f_298_);
                v___x_319_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_319_, 0, v___x_318_);
                lean_ctor_set(v___x_319_, 1, v___x_309_);
                v___x_320_ = l_Nat_reprFast(v_endPos_302_);
                v___x_321_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_321_, 0, v___x_320_);
                v___x_322_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_322_, 0, v___x_319_);
                lean_ctor_set(v___x_322_, 1, v___x_321_);
                v___x_323_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_323_, 0, v___x_322_);
                lean_ctor_set(v___x_323_, 1, v___x_309_);
                v___x_324_ = lean_string_utf8_extract(v_str_311_, v_startPos_312_, v_stopPos_313_);
                lean_dec(v_stopPos_313_);
                lean_dec(v_startPos_312_);
                lean_dec_ref(v_str_311_);
                v___x_325_ = l_String_quote(v___x_324_);
                v___x_326_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_326_, 0, v___x_325_);
                v___x_327_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_327_, 0, v___x_323_);
                lean_ctor_set(v___x_327_, 1, v___x_326_);
                return v___x_327_;
            }
            1 => {
                let mut v_canonical_328_: u8 = 0;
                v_canonical_328_ = lean_ctor_get_uint8(
                    v_info_297_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_canonical_328_ == 0 {
                    let mut v_pos_329_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_endPos_330_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
                    v_pos_329_ = lean_ctor_get(v_info_297_, 0);
                    lean_inc(v_pos_329_);
                    v_endPos_330_ = lean_ctor_get(v_info_297_, 1);
                    lean_inc(v_endPos_330_);
                    lean_dec_ref_known(v_info_297_, 2);
                    v___x_331_ = l_Nat_reprFast(v_pos_329_);
                    v___x_332_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_332_, 0, v___x_331_);
                    v___x_333_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_334_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_334_, 0, v___x_332_);
                    lean_ctor_set(v___x_334_, 1, v___x_333_);
                    v___x_335_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_335_, 0, v___x_334_);
                    lean_ctor_set(v___x_335_, 1, v_f_298_);
                    v___x_336_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_336_, 0, v___x_335_);
                    lean_ctor_set(v___x_336_, 1, v___x_333_);
                    v___x_337_ = l_Nat_reprFast(v_endPos_330_);
                    v___x_338_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_338_, 0, v___x_337_);
                    v___x_339_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_339_, 0, v___x_336_);
                    lean_ctor_set(v___x_339_, 1, v___x_338_);
                    return v___x_339_;
                } else {
                    let mut v_pos_340_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_endPos_341_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
                    v_pos_340_ = lean_ctor_get(v_info_297_, 0);
                    lean_inc(v_pos_340_);
                    v_endPos_341_ = lean_ctor_get(v_info_297_, 1);
                    lean_inc(v_endPos_341_);
                    lean_dec_ref_known(v_info_297_, 2);
                    v___x_342_ = l_Nat_reprFast(v_pos_340_);
                    v___x_343_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_343_, 0, v___x_342_);
                    v___x_344_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3;
                    v___x_345_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_345_, 0, v___x_343_);
                    lean_ctor_set(v___x_345_, 1, v___x_344_);
                    v___x_346_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_346_, 0, v___x_345_);
                    lean_ctor_set(v___x_346_, 1, v_f_298_);
                    v___x_347_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_348_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_348_, 0, v___x_346_);
                    lean_ctor_set(v___x_348_, 1, v___x_347_);
                    v___x_349_ = l_Nat_reprFast(v_endPos_341_);
                    v___x_350_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_350_, 0, v___x_349_);
                    v___x_351_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_351_, 0, v___x_348_);
                    lean_ctor_set(v___x_351_, 1, v___x_350_);
                    return v___x_351_;
                }
            }
            _ => {
                lean_dec(v_info_297_);
                return v_f_298_;
            }
        }
    } else {
        lean_dec(v_info_297_);
        return v_f_298_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(
    mut v_showInfo_352_: *mut LeanObject,
    mut v_info_353_: *mut LeanObject,
    mut v_f_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_showInfo_boxed_355_: u8 = 0;
    let mut v_res_356_: *mut LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_355_ = (lean_unbox(v_showInfo_352_) as u8);
    v_res_356_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
        v_showInfo_boxed_355_,
        v_info_353_,
        v_f_354_,
    );
    return v_res_356_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Syntax_formatStxAux_spec__0(
    mut v_a_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_nat_to_int(v_a_357_);
    return v___x_358_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(
    mut v_x_359_: *mut LeanObject,
    mut v_x_360_: *mut LeanObject,
    mut v_x_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_361_) == 0 {
                    lean_dec(v_x_359_);
                    return v_x_360_;
                } else {
                    v_head_362_ = lean_ctor_get(v_x_361_, 0);
                    v_tail_363_ = lean_ctor_get(v_x_361_, 1);
                    v_isSharedCheck_372_ = (!lean_is_exclusive(v_x_361_)) as u8;
                    if v_isSharedCheck_372_ == 0 {
                        v___x_365_ = v_x_361_;
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_363_);
                        lean_inc(v_head_362_);
                        lean_dec(v_x_361_);
                        v___x_365_ = lean_box(0);
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_359_);
                if v_isShared_366_ == 0 {
                    lean_ctor_set_tag(v___x_365_, 5);
                    lean_ctor_set(v___x_365_, 1, v_x_359_);
                    lean_ctor_set(v___x_365_, 0, v_x_360_);
                    v___x_368_ = v___x_365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_371_, 0, v_x_360_);
                    lean_ctor_set(v_reuseFailAlloc_371_, 1, v_x_359_);
                    v___x_368_ = v_reuseFailAlloc_371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_369_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_369_, 0, v___x_368_);
                lean_ctor_set(v___x_369_, 1, v_head_362_);
                v_x_360_ = v___x_369_;
                v_x_361_ = v_tail_363_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
    mut v_x_373_: *mut LeanObject,
    mut v_x_374_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_374_);
        v___x_375_ = lean_box(0);
        return v___x_375_;
    } else {
        let mut v_tail_376_: *mut LeanObject = core::ptr::null_mut();
        v_tail_376_ = lean_ctor_get(v_x_373_, 1);
        if lean_obj_tag(v_tail_376_) == 0 {
            let mut v_head_377_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_374_);
            v_head_377_ = lean_ctor_get(v_x_373_, 0);
            lean_inc(v_head_377_);
            lean_dec_ref_known(v_x_373_, 2);
            return v_head_377_;
        } else {
            let mut v_head_378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_376_);
            v_head_378_ = lean_ctor_get(v_x_373_, 0);
            lean_inc(v_head_378_);
            lean_dec_ref_known(v_x_373_, 2);
            v___x_379_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(v_x_374_, v_head_378_, v_tail_376_);
            return v___x_379_;
        }
    }
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__2() -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v___x_381_ = l_Lean_Syntax_formatStxAux___closed__0;
    v___x_382_ = lean_string_length(v___x_381_);
    return v___x_382_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__3() -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2_once),
        _init_l_Lean_Syntax_formatStxAux___closed__2,
    );
    v___x_384_ = lean_nat_to_int(v___x_383_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__17() -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Syntax_formatStxAux___closed__15;
    v___x_406_ = lean_string_length(v___x_405_);
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__18() -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17_once),
        _init_l_Lean_Syntax_formatStxAux___closed__17,
    );
    v___x_408_ = lean_nat_to_int(v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux(
    mut v_maxDepth_420_: *mut LeanObject,
    mut v_showInfo_421_: u8,
    mut v_depth_422_: *mut LeanObject,
    mut v_x_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_441_: u8 = 0;
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shorterName_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_header_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_474_: u8 = 0;
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v_val_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v_val_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_423_) {
                0 => {
                    lean_dec(v_maxDepth_420_);
                    v___x_434_ = l_Lean_Syntax_formatStxAux___closed__7;
                    return v___x_434_;
                }
                1 => {
                    v_info_435_ = lean_ctor_get(v_x_423_, 0);
                    lean_inc(v_info_435_);
                    v_kind_436_ = lean_ctor_get(v_x_423_, 1);
                    lean_inc(v_kind_436_);
                    v_args_437_ = lean_ctor_get(v_x_423_, 2);
                    lean_inc_ref(v_args_437_);
                    lean_dec_ref_known(v_x_423_, 3);
                    v___x_438_ = lean_unsigned_to_nat(1);
                    v_depth_439_ = lean_nat_add(v_depth_422_, v___x_438_);
                    v___x_451_ = l_Lean_Syntax_formatStxAux___closed__11;
                    v___x_452_ = lean_name_eq(v_kind_436_, v___x_451_);
                    if v___x_452_ == 0 {
                        v___x_453_ = l_Lean_Syntax_formatStxAux___closed__14;
                        v___x_454_ = lean_box(0);
                        v_shorterName_455_ =
                            l_Lean_Name_replacePrefix(v_kind_436_, v___x_453_, v___x_454_);
                        v___x_456_ = 1;
                        v___x_457_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_shorterName_455_,
                                v___x_456_,
                            );
                        v___x_458_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v___x_458_, 0, v___x_457_);
                        v_header_459_ =
                            l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                                v_showInfo_421_,
                                v_info_435_,
                                v___x_458_,
                            );
                        v___x_482_ = lean_unsigned_to_nat(0);
                        v___x_483_ = lean_array_get_size(v_args_437_);
                        v___x_484_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
                        if v___x_484_ == 0 {
                            v___y_474_ = v___x_484_;
                            state = 5;
                            continue;
                        } else {
                            if lean_obj_tag(v_maxDepth_420_) == 0 {
                                lean_inc(v_depth_439_);
                                v___y_480_ = v_depth_439_;
                                state = 6;
                                continue;
                            } else {
                                v_val_485_ = lean_ctor_get(v_maxDepth_420_, 0);
                                lean_inc(v_val_485_);
                                v___y_480_ = v_val_485_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_kind_436_);
                        lean_dec(v_info_435_);
                        v___x_486_ = lean_unsigned_to_nat(0);
                        v___x_487_ = lean_array_get_size(v_args_437_);
                        v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
                        if v___x_488_ == 0 {
                            v___y_441_ = v___x_488_;
                            state = 2;
                            continue;
                        } else {
                            if lean_obj_tag(v_maxDepth_420_) == 0 {
                                lean_inc(v_depth_439_);
                                v___y_449_ = v_depth_439_;
                                state = 3;
                                continue;
                            } else {
                                v_val_489_ = lean_ctor_get(v_maxDepth_420_, 0);
                                lean_inc(v_val_489_);
                                v___y_449_ = v_val_489_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
                2 => {
                    lean_dec(v_maxDepth_420_);
                    v_info_490_ = lean_ctor_get(v_x_423_, 0);
                    lean_inc(v_info_490_);
                    v_val_491_ = lean_ctor_get(v_x_423_, 1);
                    lean_inc_ref(v_val_491_);
                    lean_dec_ref_known(v_x_423_, 2);
                    v___x_492_ = l_String_quote(v_val_491_);
                    v___x_493_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_493_, 0, v___x_492_);
                    v___x_494_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_490_,
                        v___x_493_,
                    );
                    return v___x_494_;
                }
                _ => {
                    lean_dec(v_maxDepth_420_);
                    v_info_495_ = lean_ctor_get(v_x_423_, 0);
                    lean_inc(v_info_495_);
                    v_val_496_ = lean_ctor_get(v_x_423_, 2);
                    lean_inc(v_val_496_);
                    lean_dec_ref_known(v_x_423_, 4);
                    v___x_497_ = l_Lean_Syntax_formatStxAux___closed__23;
                    v___x_498_ = 1;
                    v___x_499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_val_496_, v___x_498_,
                    );
                    v___x_500_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_500_, 0, v___x_499_);
                    v___x_501_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_501_, 0, v___x_497_);
                    lean_ctor_set(v___x_501_, 1, v___x_500_);
                    v___x_502_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_495_,
                        v___x_501_,
                    );
                    return v___x_502_;
                }
            },
            1 => {
                v___x_426_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__3,
                );
                v___x_427_ = l_Lean_Syntax_formatStxAux___closed__4;
                v___x_428_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_428_, 0, v___x_427_);
                lean_ctor_set(v___x_428_, 1, v___y_425_);
                v___x_429_ = l_Lean_Syntax_formatStxAux___closed__5;
                v___x_430_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_430_, 0, v___x_428_);
                lean_ctor_set(v___x_430_, 1, v___x_429_);
                v___x_431_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_431_, 0, v___x_426_);
                lean_ctor_set(v___x_431_, 1, v___x_430_);
                v___x_432_ = 0;
                v___x_433_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_433_, 0, v___x_431_);
                lean_ctor_set_uint8(
                    v___x_433_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_432_,
                );
                return v___x_433_;
            }
            2 => {
                if v___y_441_ == 0 {
                    v___x_442_ = lean_array_to_list(v_args_437_);
                    v___x_443_ = lean_box(0);
                    v___x_444_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_442_,
                        v___x_443_,
                    );
                    lean_dec(v_depth_439_);
                    v___x_445_ = lean_box(1);
                    v___x_446_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                        v___x_444_, v___x_445_,
                    );
                    v___y_425_ = v___x_446_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_depth_439_);
                    lean_dec_ref(v_args_437_);
                    lean_dec(v_maxDepth_420_);
                    v___x_447_ = l_Lean_Syntax_formatStxAux___closed__9;
                    v___y_425_ = v___x_447_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_450_ = lean_nat_dec_lt(v___y_449_, v_depth_439_);
                lean_dec(v___y_449_);
                v___y_441_ = v___x_450_;
                state = 2;
                continue;
            }
            4 => {
                v___x_462_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_462_, 0, v_header_459_);
                lean_ctor_set(v___x_462_, 1, v___y_461_);
                v___x_463_ = lean_box(1);
                v___x_464_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                    v___x_462_, v___x_463_,
                );
                v___x_465_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__18,
                );
                v___x_466_ = l_Lean_Syntax_formatStxAux___closed__19;
                v___x_467_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_467_, 0, v___x_466_);
                lean_ctor_set(v___x_467_, 1, v___x_464_);
                v___x_468_ = l_Lean_Syntax_formatStxAux___closed__20;
                v___x_469_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_469_, 0, v___x_467_);
                lean_ctor_set(v___x_469_, 1, v___x_468_);
                v___x_470_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_470_, 0, v___x_465_);
                lean_ctor_set(v___x_470_, 1, v___x_469_);
                v___x_471_ = 0;
                v___x_472_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_472_, 0, v___x_470_);
                lean_ctor_set_uint8(
                    v___x_472_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_471_,
                );
                return v___x_472_;
            }
            5 => {
                if v___y_474_ == 0 {
                    v___x_475_ = lean_array_to_list(v_args_437_);
                    v___x_476_ = lean_box(0);
                    v___x_477_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_475_,
                        v___x_476_,
                    );
                    lean_dec(v_depth_439_);
                    v___y_461_ = v___x_477_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_depth_439_);
                    lean_dec_ref(v_args_437_);
                    lean_dec(v_maxDepth_420_);
                    v___x_478_ = l_Lean_Syntax_formatStxAux___closed__21;
                    v___y_461_ = v___x_478_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_481_ = lean_nat_dec_lt(v___y_480_, v_depth_439_);
                lean_dec(v___y_480_);
                v___y_474_ = v___x_481_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
    mut v_maxDepth_503_: *mut LeanObject,
    mut v_showInfo_504_: u8,
    mut v_depth_505_: *mut LeanObject,
    mut v_a_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_506_) == 0 {
                    lean_dec(v_maxDepth_503_);
                    v___x_508_ = l_List_reverse___redArg(v_a_507_);
                    return v___x_508_;
                } else {
                    v_head_509_ = lean_ctor_get(v_a_506_, 0);
                    v_tail_510_ = lean_ctor_get(v_a_506_, 1);
                    v_isSharedCheck_519_ = (!lean_is_exclusive(v_a_506_)) as u8;
                    if v_isSharedCheck_519_ == 0 {
                        v___x_512_ = v_a_506_;
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_510_);
                        lean_inc(v_head_509_);
                        lean_dec(v_a_506_);
                        v___x_512_ = lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_maxDepth_503_);
                v___x_514_ = l_Lean_Syntax_formatStxAux(
                    v_maxDepth_503_,
                    v_showInfo_504_,
                    v_depth_505_,
                    v_head_509_,
                );
                if v_isShared_513_ == 0 {
                    lean_ctor_set(v___x_512_, 1, v_a_507_);
                    lean_ctor_set(v___x_512_, 0, v___x_514_);
                    v___x_516_ = v___x_512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
                    lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_507_);
                    v___x_516_ = v_reuseFailAlloc_518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_506_ = v_tail_510_;
                v_a_507_ = v___x_516_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1___boxed(
    mut v_maxDepth_520_: *mut LeanObject,
    mut v_showInfo_521_: *mut LeanObject,
    mut v_depth_522_: *mut LeanObject,
    mut v_a_523_: *mut LeanObject,
    mut v_a_524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_showInfo_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_525_ = (lean_unbox(v_showInfo_521_) as u8);
    v_res_526_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
        v_maxDepth_520_,
        v_showInfo_boxed_525_,
        v_depth_522_,
        v_a_523_,
        v_a_524_,
    );
    lean_dec(v_depth_522_);
    return v_res_526_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux___boxed(
    mut v_maxDepth_527_: *mut LeanObject,
    mut v_showInfo_528_: *mut LeanObject,
    mut v_depth_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_showInfo_boxed_531_: u8 = 0;
    let mut v_res_532_: *mut LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_531_ = (lean_unbox(v_showInfo_528_) as u8);
    v_res_532_ = l_Lean_Syntax_formatStxAux(
        v_maxDepth_527_,
        v_showInfo_boxed_531_,
        v_depth_529_,
        v_x_530_,
    );
    lean_dec(v_depth_529_);
    return v_res_532_;
}
pub unsafe fn l_Lean_Syntax_formatStx(
    mut v_stx_533_: *mut LeanObject,
    mut v_maxDepth_534_: *mut LeanObject,
    mut v_showInfo_535_: u8,
) -> *mut LeanObject {
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    v___x_536_ = lean_unsigned_to_nat(0);
    v___x_537_ =
        l_Lean_Syntax_formatStxAux(v_maxDepth_534_, v_showInfo_535_, v___x_536_, v_stx_533_);
    return v___x_537_;
}
pub unsafe fn l_Lean_Syntax_formatStx___boxed(
    mut v_stx_538_: *mut LeanObject,
    mut v_maxDepth_539_: *mut LeanObject,
    mut v_showInfo_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_showInfo_boxed_541_: u8 = 0;
    let mut v_res_542_: *mut LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_541_ = (lean_unbox(v_showInfo_540_) as u8);
    v_res_542_ = l_Lean_Syntax_formatStx(v_stx_538_, v_maxDepth_539_, v_showInfo_boxed_541_);
    return v_res_542_;
}
pub unsafe fn l_Lean_Syntax_instToFormat___lam__0(
    mut v_stx_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = lean_box(0);
    v___x_545_ = 0;
    v___x_546_ = l_Lean_Syntax_formatStx(v_stx_543_, v___x_544_, v___x_545_);
    return v___x_546_;
}
pub unsafe fn l_Lean_Syntax_instToString___lam__0(
    mut v_f_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Std_Format_defWidth;
    v___x_551_ = lean_unsigned_to_nat(0);
    v___x_552_ = l_Std_Format_pretty(v_f_549_, v___x_550_, v___x_551_, v___x_551_);
    return v___x_552_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___lam__0(
    mut v_x_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    v___x_559_ = lean_box(0);
    v___x_560_ = 0;
    v___x_561_ = l_Lean_Syntax_formatStx(v_x_558_, v___x_559_, v___x_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax(mut v_k_563_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_564_: *mut LeanObject = core::ptr::null_mut();
    v___f_564_ = l_Lean_Syntax_instToFormatTSyntax___closed__0;
    return v___f_564_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___boxed(
    mut v_k_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Syntax_instToFormatTSyntax(v_k_565_);
    lean_dec(v_k_565_);
    return v_res_566_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___lam__0(
    mut v_x_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_568_ = lean_box(0);
    v___x_569_ = 0;
    v___x_570_ = l_Lean_Syntax_formatStx(v_x_567_, v___x_568_, v___x_569_);
    v___x_571_ = l_Std_Format_defWidth;
    v___x_572_ = lean_unsigned_to_nat(0);
    v___x_573_ = l_Std_Format_pretty(v___x_570_, v___x_571_, v___x_572_, v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax(mut v_k_575_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_576_: *mut LeanObject = core::ptr::null_mut();
    v___f_576_ = l_Lean_Syntax_instToStringTSyntax___closed__0;
    return v___f_576_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___boxed(
    mut v_k_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Syntax_instToStringTSyntax(v_k_577_);
    lean_dec(v_k_577_);
    return v_res_578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Format_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Format_Syntax(builtin);
}
