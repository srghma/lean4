// Lean compiler output
// Module: Lean.Compiler.ExternAttr
// Imports: Lean.ProjFns Lean.Attributes Init.Data.String.Lemmas.Order Init.Data.String.OrderInstances Init.Data.Order.Lemmas
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_mul, lean_nat_sub, lean_st_ref_get, lean_string_append,
    lean_string_dec_eq, lean_string_hash, lean_string_push, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint32_to_nat, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_intersperseTR___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_getD___redArg;
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_Syntax_isStrLit_x3f};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_ParametricAttribute_getParam_x3f___redArg,
    l_Lean_registerParametricAttribute___redArg, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::CoreM::l_Lean_compileDecls;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_isConstructor,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::ProjFns::{
    initialize_Lean_ProjFns, l_Lean_Environment_isProjectionFn, runtime_initialize_Lean_ProjFns,
};
pub static l_Lean_instBEqExternEntry___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqExternEntry_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqExternEntry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExternEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqExternEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExternEntry___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instHashableExternEntry_hash___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableExternEntry_hash___closed__0: u64 = 0;
static mut l_Lean_instHashableExternEntry_hash___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableExternEntry_hash___closed__1: u64 = 0;
pub static l_Lean_instHashableExternEntry___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableExternEntry_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableExternEntry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExternEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instHashableExternEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExternEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedExternAttrData_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedExternAttrData: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqExternAttrData___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqExternAttrData_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqExternAttrData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExternAttrData___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqExternAttrData: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqExternAttrData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instHashableExternAttrData___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableExternAttrData_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableExternAttrData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExternAttrData___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instHashableExternAttrData: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableExternAttrData___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2_value) as *mut leanh::LeanObject,807312601722567303 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 116, 101, 114, 110, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16634252444307200090 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,969182223056470162 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [98, 117, 105, 108, 116, 105, 110, 32, 97, 110, 100, 32, 102, 111, 114, 101, 105, 103, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_externAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_expandExternPatternAux___closed__0_value: leanh::LeanStringObject<1> =
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
static mut l_Lean_expandExternPatternAux___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_expandExternPatternAux___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkSimpleFnCall___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_Lean_mkSimpleFnCall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkSimpleFnCall___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_mkSimpleFnCall___closed__1_value: leanh::LeanStringObject<3> =
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
static mut l_Lean_mkSimpleFnCall___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkSimpleFnCall___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_mkSimpleFnCall___closed__2_value: leanh::LeanStringObject<2> =
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
static mut l_Lean_mkSimpleFnCall___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkSimpleFnCall___closed__2_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_ExternEntry_ctorIdx(
    mut v_x_692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_692_) {
        0 => {
            let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_693_ = leanh::lean_unsigned_to_nat(0);
            return v___x_693_;
        }
        1 => {
            let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_694_ = leanh::lean_unsigned_to_nat(1);
            return v___x_694_;
        }
        2 => {
            let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_695_ = leanh::lean_unsigned_to_nat(2);
            return v___x_695_;
        }
        _ => {
            let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_696_ = leanh::lean_unsigned_to_nat(3);
            return v___x_696_;
        }
    }
}
pub unsafe fn l_Lean_ExternEntry_ctorIdx___boxed(
    mut v_x_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_698_ = l_Lean_ExternEntry_ctorIdx(v_x_697_);
    leanh::lean_dec(v_x_697_);
    return v_res_698_;
}
pub unsafe fn l_Lean_ExternEntry_ctorElim___redArg(
    mut v_t_699_: *mut leanh::LeanObject,
    mut v_k_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_699_) {
        0 => {
            let mut v_backend_701_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_backend_701_ = leanh::lean_ctor_get(v_t_699_, 0);
            leanh::lean_inc(v_backend_701_);
            leanh::lean_dec_ref_known(v_t_699_, 1);
            v___x_702_ = leanh::lean_apply_1(v_k_700_, v_backend_701_);
            return v___x_702_;
        }
        3 => {
            return v_k_700_;
        }
        _ => {
            let mut v_backend_703_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_pattern_704_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_backend_703_ = leanh::lean_ctor_get(v_t_699_, 0);
            leanh::lean_inc(v_backend_703_);
            v_pattern_704_ = leanh::lean_ctor_get(v_t_699_, 1);
            leanh::lean_inc_ref(v_pattern_704_);
            leanh::lean_dec(v_t_699_);
            v___x_705_ = leanh::lean_apply_2(v_k_700_, v_backend_703_, v_pattern_704_);
            return v___x_705_;
        }
    }
}
pub unsafe fn l_Lean_ExternEntry_ctorElim(
    mut v_motive_706_: *mut leanh::LeanObject,
    mut v_ctorIdx_707_: *mut leanh::LeanObject,
    mut v_t_708_: *mut leanh::LeanObject,
    mut v_h_709_: *mut leanh::LeanObject,
    mut v_k_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_708_, v_k_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_ExternEntry_ctorElim___boxed(
    mut v_motive_712_: *mut leanh::LeanObject,
    mut v_ctorIdx_713_: *mut leanh::LeanObject,
    mut v_t_714_: *mut leanh::LeanObject,
    mut v_h_715_: *mut leanh::LeanObject,
    mut v_k_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ =
        l_Lean_ExternEntry_ctorElim(v_motive_712_, v_ctorIdx_713_, v_t_714_, v_h_715_, v_k_716_);
    leanh::lean_dec(v_ctorIdx_713_);
    return v_res_717_;
}
pub unsafe fn l_Lean_ExternEntry_adhoc_elim___redArg(
    mut v_t_718_: *mut leanh::LeanObject,
    mut v_adhoc_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_718_, v_adhoc_719_);
    return v___x_720_;
}
pub unsafe fn l_Lean_ExternEntry_adhoc_elim(
    mut v_motive_721_: *mut leanh::LeanObject,
    mut v_t_722_: *mut leanh::LeanObject,
    mut v_h_723_: *mut leanh::LeanObject,
    mut v_adhoc_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_722_, v_adhoc_724_);
    return v___x_725_;
}
pub unsafe fn l_Lean_ExternEntry_inline_elim___redArg(
    mut v_t_726_: *mut leanh::LeanObject,
    mut v_inline_727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_726_, v_inline_727_);
    return v___x_728_;
}
pub unsafe fn l_Lean_ExternEntry_inline_elim(
    mut v_motive_729_: *mut leanh::LeanObject,
    mut v_t_730_: *mut leanh::LeanObject,
    mut v_h_731_: *mut leanh::LeanObject,
    mut v_inline_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_730_, v_inline_732_);
    return v___x_733_;
}
pub unsafe fn l_Lean_ExternEntry_standard_elim___redArg(
    mut v_t_734_: *mut leanh::LeanObject,
    mut v_standard_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_734_, v_standard_735_);
    return v___x_736_;
}
pub unsafe fn l_Lean_ExternEntry_standard_elim(
    mut v_motive_737_: *mut leanh::LeanObject,
    mut v_t_738_: *mut leanh::LeanObject,
    mut v_h_739_: *mut leanh::LeanObject,
    mut v_standard_740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_738_, v_standard_740_);
    return v___x_741_;
}
pub unsafe fn l_Lean_ExternEntry_opaque_elim___redArg(
    mut v_t_742_: *mut leanh::LeanObject,
    mut v_opaque_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_742_, v_opaque_743_);
    return v___x_744_;
}
pub unsafe fn l_Lean_ExternEntry_opaque_elim(
    mut v_motive_745_: *mut leanh::LeanObject,
    mut v_t_746_: *mut leanh::LeanObject,
    mut v_h_747_: *mut leanh::LeanObject,
    mut v_opaque_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Lean_ExternEntry_ctorElim___redArg(v_t_746_, v_opaque_748_);
    return v___x_749_;
}
pub unsafe fn l_Lean_instBEqExternEntry_beq(
    mut v_x_750_: *mut leanh::LeanObject,
    mut v_x_751_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_a_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: u8 = 0;
    let mut v_backend_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: u8 = 0;
    let mut v_backend_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: u8 = 0;
    let mut v_backend_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_750_) {
                0 => {
                    if leanh::lean_obj_tag(v_x_751_) == 0 {
                        v_backend_759_ = leanh::lean_ctor_get(v_x_750_, 0);
                        v_backend_760_ = leanh::lean_ctor_get(v_x_751_, 0);
                        v___x_761_ = lean_name_eq(v_backend_759_, v_backend_760_);
                        return v___x_761_;
                    } else {
                        v___x_762_ = 0;
                        return v___x_762_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_751_) == 1 {
                        v_backend_763_ = leanh::lean_ctor_get(v_x_750_, 0);
                        v_pattern_764_ = leanh::lean_ctor_get(v_x_750_, 1);
                        v_backend_765_ = leanh::lean_ctor_get(v_x_751_, 0);
                        v_pattern_766_ = leanh::lean_ctor_get(v_x_751_, 1);
                        v_a_753_ = v_backend_763_;
                        v_a_754_ = v_pattern_764_;
                        v_b_755_ = v_backend_765_;
                        v_b_756_ = v_pattern_766_;
                        state = 1;
                        continue;
                    } else {
                        v___x_767_ = 0;
                        return v___x_767_;
                    }
                }
                2 => {
                    if leanh::lean_obj_tag(v_x_751_) == 2 {
                        v_backend_768_ = leanh::lean_ctor_get(v_x_750_, 0);
                        v_fn_769_ = leanh::lean_ctor_get(v_x_750_, 1);
                        v_backend_770_ = leanh::lean_ctor_get(v_x_751_, 0);
                        v_fn_771_ = leanh::lean_ctor_get(v_x_751_, 1);
                        v_a_753_ = v_backend_768_;
                        v_a_754_ = v_fn_769_;
                        v_b_755_ = v_backend_770_;
                        v_b_756_ = v_fn_771_;
                        state = 1;
                        continue;
                    } else {
                        v___x_772_ = 0;
                        return v___x_772_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_x_751_) == 3 {
                        v___x_773_ = 1;
                        return v___x_773_;
                    } else {
                        v___x_774_ = 0;
                        return v___x_774_;
                    }
                }
            },
            1 => {
                v___x_757_ = lean_name_eq(v_a_753_, v_b_755_);
                if v___x_757_ == 0 {
                    return v___x_757_;
                } else {
                    v___x_758_ = lean_string_dec_eq(v_a_754_, v_b_756_);
                    return v___x_758_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqExternEntry_beq___boxed(
    mut v_x_775_: *mut leanh::LeanObject,
    mut v_x_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_777_: u8 = 0;
    let mut v_r_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_instBEqExternEntry_beq(v_x_775_, v_x_776_);
    leanh::lean_dec(v_x_776_);
    leanh::lean_dec(v_x_775_);
    v_r_778_ = leanh::lean_box((v_res_777_) as usize);
    return v_r_778_;
}
pub unsafe fn _init_l_Lean_instHashableExternEntry_hash___closed__0() -> u64 {
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u64 = 0;
    v___x_781_ = leanh::lean_unsigned_to_nat(1723);
    v___x_782_ = lean_uint64_of_nat(v___x_781_);
    return v___x_782_;
}
pub unsafe fn _init_l_Lean_instHashableExternEntry_hash___closed__1() -> u64 {
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: u64 = 0;
    let mut v___x_785_: u64 = 0;
    v___x_783_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableExternEntry_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableExternEntry_hash___closed__0_once),
        _init_l_Lean_instHashableExternEntry_hash___closed__0,
    );
    v___x_784_ = 0u64;
    v___x_785_ = lean_uint64_mix_hash(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn l_Lean_instHashableExternEntry_hash(
    mut v_x_786_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_backend_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u64 = 0;
    let mut v___x_789_: u64 = 0;
    let mut v_hash_790_: u64 = 0;
    let mut v___x_791_: u64 = 0;
    let mut v_backend_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u64 = 0;
    let mut v___y_796_: u64 = 0;
    let mut v___x_797_: u64 = 0;
    let mut v___x_798_: u64 = 0;
    let mut v___x_799_: u64 = 0;
    let mut v___x_800_: u64 = 0;
    let mut v_hash_801_: u64 = 0;
    let mut v_backend_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u64 = 0;
    let mut v___y_806_: u64 = 0;
    let mut v___x_807_: u64 = 0;
    let mut v___x_808_: u64 = 0;
    let mut v___x_809_: u64 = 0;
    let mut v___x_810_: u64 = 0;
    let mut v_hash_811_: u64 = 0;
    let mut v___x_812_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_786_) {
                0 => {
                    v_backend_787_ = leanh::lean_ctor_get(v_x_786_, 0);
                    v___x_788_ = 0u64;
                    if leanh::lean_obj_tag(v_backend_787_) == 0 {
                        v___x_789_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__1_once
                            ),
                            _init_l_Lean_instHashableExternEntry_hash___closed__1,
                        );
                        return v___x_789_;
                    } else {
                        v_hash_790_ = leanh::lean_ctor_get_uint64(
                            v_backend_787_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_791_ = lean_uint64_mix_hash(v___x_788_, v_hash_790_);
                        return v___x_791_;
                    }
                }
                1 => {
                    v_backend_792_ = leanh::lean_ctor_get(v_x_786_, 0);
                    v_pattern_793_ = leanh::lean_ctor_get(v_x_786_, 1);
                    v___x_794_ = 1u64;
                    if leanh::lean_obj_tag(v_backend_792_) == 0 {
                        v___x_800_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__0_once
                            ),
                            _init_l_Lean_instHashableExternEntry_hash___closed__0,
                        );
                        v___y_796_ = v___x_800_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_801_ = leanh::lean_ctor_get_uint64(
                            v_backend_792_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_796_ = v_hash_801_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_backend_802_ = leanh::lean_ctor_get(v_x_786_, 0);
                    v_fn_803_ = leanh::lean_ctor_get(v_x_786_, 1);
                    v___x_804_ = 2u64;
                    if leanh::lean_obj_tag(v_backend_802_) == 0 {
                        v___x_810_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instHashableExternEntry_hash___closed__0_once
                            ),
                            _init_l_Lean_instHashableExternEntry_hash___closed__0,
                        );
                        v___y_806_ = v___x_810_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_811_ = leanh::lean_ctor_get_uint64(
                            v_backend_802_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_806_ = v_hash_811_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_812_ = 3u64;
                    return v___x_812_;
                }
            },
            1 => {
                v___x_797_ = lean_uint64_mix_hash(v___x_794_, v___y_796_);
                v___x_798_ = lean_string_hash(v_pattern_793_);
                v___x_799_ = lean_uint64_mix_hash(v___x_797_, v___x_798_);
                return v___x_799_;
            }
            2 => {
                v___x_807_ = lean_uint64_mix_hash(v___x_804_, v___y_806_);
                v___x_808_ = lean_string_hash(v_fn_803_);
                v___x_809_ = lean_uint64_mix_hash(v___x_807_, v___x_808_);
                return v___x_809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instHashableExternEntry_hash___boxed(
    mut v_x_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_814_: u64 = 0;
    let mut v_r_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_instHashableExternEntry_hash(v_x_813_);
    leanh::lean_dec(v_x_813_);
    v_r_815_ = leanh::lean_box_uint64(v_res_814_);
    return v_r_815_;
}
pub unsafe fn _init_l_Lean_instInhabitedExternAttrData_default() -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = leanh::lean_box(0);
    return v___x_818_;
}
pub unsafe fn _init_l_Lean_instInhabitedExternAttrData() -> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = leanh::lean_box(0);
    return v___x_819_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(
    mut v_x_820_: *mut leanh::LeanObject,
    mut v_x_821_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: u8 = 0;
    let mut v_head_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_820_) == 0 {
                    if leanh::lean_obj_tag(v_x_821_) == 0 {
                        v___x_822_ = 1;
                        return v___x_822_;
                    } else {
                        v___x_823_ = 0;
                        return v___x_823_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_821_) == 0 {
                        v___x_824_ = 0;
                        return v___x_824_;
                    } else {
                        v_head_825_ = leanh::lean_ctor_get(v_x_820_, 0);
                        v_tail_826_ = leanh::lean_ctor_get(v_x_820_, 1);
                        v_head_827_ = leanh::lean_ctor_get(v_x_821_, 0);
                        v_tail_828_ = leanh::lean_ctor_get(v_x_821_, 1);
                        v___x_829_ = l_Lean_instBEqExternEntry_beq(v_head_825_, v_head_827_);
                        if v___x_829_ == 0 {
                            return v___x_829_;
                        } else {
                            v_x_820_ = v_tail_826_;
                            v_x_821_ = v_tail_828_;
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
pub unsafe fn l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0___boxed(
    mut v_x_831_: *mut leanh::LeanObject,
    mut v_x_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_833_: u8 = 0;
    let mut v_r_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_833_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_831_, v_x_832_);
    leanh::lean_dec(v_x_832_);
    leanh::lean_dec(v_x_831_);
    v_r_834_ = leanh::lean_box((v_res_833_) as usize);
    return v_r_834_;
}
pub unsafe fn l_Lean_instBEqExternAttrData_beq(
    mut v_x_835_: *mut leanh::LeanObject,
    mut v_x_836_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_837_: u8 = 0;
    v___x_837_ = l_List_beq___at___00Lean_instBEqExternAttrData_beq_spec__0(v_x_835_, v_x_836_);
    return v___x_837_;
}
pub unsafe fn l_Lean_instBEqExternAttrData_beq___boxed(
    mut v_x_838_: *mut leanh::LeanObject,
    mut v_x_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_840_: u8 = 0;
    let mut v_r_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_instBEqExternAttrData_beq(v_x_838_, v_x_839_);
    leanh::lean_dec(v_x_839_);
    leanh::lean_dec(v_x_838_);
    v_r_841_ = leanh::lean_box((v_res_840_) as usize);
    return v_r_841_;
}
pub unsafe fn l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(
    mut v_x_844_: u64,
    mut v_x_845_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_head_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: u64 = 0;
    let mut v___x_849_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_845_) == 0 {
                    return v_x_844_;
                } else {
                    v_head_846_ = leanh::lean_ctor_get(v_x_845_, 0);
                    v_tail_847_ = leanh::lean_ctor_get(v_x_845_, 1);
                    v___x_848_ = l_Lean_instHashableExternEntry_hash(v_head_846_);
                    v___x_849_ = lean_uint64_mix_hash(v_x_844_, v___x_848_);
                    v_x_844_ = v___x_849_;
                    v_x_845_ = v_tail_847_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0___boxed(
    mut v_x_851_: *mut leanh::LeanObject,
    mut v_x_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_57__boxed_853_: u64 = 0;
    let mut v_res_854_: u64 = 0;
    let mut v_r_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_57__boxed_853_ = leanh::lean_unbox_uint64(v_x_851_);
    leanh::lean_dec_ref(v_x_851_);
    v_res_854_ = l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(
        v_x_57__boxed_853_,
        v_x_852_,
    );
    leanh::lean_dec(v_x_852_);
    v_r_855_ = leanh::lean_box_uint64(v_res_854_);
    return v_r_855_;
}
pub unsafe fn l_Lean_instHashableExternAttrData_hash(
    mut v_x_856_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_857_: u64 = 0;
    let mut v___x_858_: u64 = 0;
    let mut v___x_859_: u64 = 0;
    let mut v___x_860_: u64 = 0;
    v___x_857_ = 0u64;
    v___x_858_ = 7u64;
    v___x_859_ =
        l_List_foldl___at___00Lean_instHashableExternAttrData_hash_spec__0(v___x_858_, v_x_856_);
    v___x_860_ = lean_uint64_mix_hash(v___x_857_, v___x_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_instHashableExternAttrData_hash___boxed(
    mut v_x_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_862_: u64 = 0;
    let mut v_r_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l_Lean_instHashableExternAttrData_hash(v_x_861_);
    leanh::lean_dec(v_x_861_);
    v_r_863_ = leanh::lean_box_uint64(v_res_862_);
    return v_r_863_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__0);
    v___x_868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_868_, 0, v___x_867_);
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
    v___x_870_ = leanh::lean_unsigned_to_nat(0);
    v___x_871_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_871_, 0, v___x_870_);
    leanh::lean_ctor_set(v___x_871_, 1, v___x_870_);
    leanh::lean_ctor_set(v___x_871_, 2, v___x_870_);
    leanh::lean_ctor_set(v___x_871_, 3, v___x_870_);
    leanh::lean_ctor_set(v___x_871_, 4, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 5, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 6, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 7, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 8, v___x_869_);
    leanh::lean_ctor_set(v___x_871_, 9, v___x_869_);
    return v___x_871_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = leanh::lean_unsigned_to_nat(32);
    v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
    v___x_874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
    return v___x_874_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_875_: usize = 0;
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = 5usize;
    v___x_876_ = leanh::lean_unsigned_to_nat(0);
    v___x_877_ = leanh::lean_unsigned_to_nat(32);
    v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
    v___x_879_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__3);
    v___x_880_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_880_, 0, v___x_879_);
    leanh::lean_ctor_set(v___x_880_, 1, v___x_878_);
    leanh::lean_ctor_set(v___x_880_, 2, v___x_876_);
    leanh::lean_ctor_set(v___x_880_, 3, v___x_876_);
    leanh::lean_ctor_set_usize(v___x_880_, 4, v___x_875_);
    return v___x_880_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = leanh::lean_box(1);
    v___x_882_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__4);
    v___x_883_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__1);
    v___x_884_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_884_, 0, v___x_883_);
    leanh::lean_ctor_set(v___x_884_, 1, v___x_882_);
    leanh::lean_ctor_set(v___x_884_, 2, v___x_881_);
    return v___x_884_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(
    mut v_msgData_885_: *mut leanh::LeanObject,
    mut v___y_886_: *mut leanh::LeanObject,
    mut v___y_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = lean_st_ref_get(v___y_887_);
    v_env_890_ = leanh::lean_ctor_get(v___x_889_, 0);
    leanh::lean_inc_ref(v_env_890_);
    leanh::lean_dec(v___x_889_);
    v_options_891_ = leanh::lean_ctor_get(v___y_886_, 2);
    v___x_892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__2);
    v___x_893_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___closed__5);
    leanh::lean_inc_ref(v_options_891_);
    v___x_894_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_894_, 0, v_env_890_);
    leanh::lean_ctor_set(v___x_894_, 1, v___x_892_);
    leanh::lean_ctor_set(v___x_894_, 2, v___x_893_);
    leanh::lean_ctor_set(v___x_894_, 3, v_options_891_);
    v___x_895_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_895_, 0, v___x_894_);
    leanh::lean_ctor_set(v___x_895_, 1, v_msgData_885_);
    v___x_896_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_896_, 0, v___x_895_);
    return v___x_896_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_897_: *mut leanh::LeanObject,
    mut v___y_898_: *mut leanh::LeanObject,
    mut v___y_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_901_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msgData_897_, v___y_898_, v___y_899_);
    leanh::lean_dec(v___y_899_);
    leanh::lean_dec_ref(v___y_898_);
    return v_res_901_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(
    mut v_msg_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_911_: u8 = 0;
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_906_ = leanh::lean_ctor_get(v___y_903_, 5);
                v___x_907_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0_spec__1(v_msg_902_, v___y_903_, v___y_904_);
                v_a_908_ = leanh::lean_ctor_get(v___x_907_, 0);
                v_isSharedCheck_916_ = (!leanh::lean_is_exclusive(v___x_907_)) as u8;
                if v_isSharedCheck_916_ == 0 {
                    v___x_910_ = v___x_907_;
                    v_isShared_911_ = v_isSharedCheck_916_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_908_);
                    leanh::lean_dec(v___x_907_);
                    v___x_910_ = leanh::lean_box(0);
                    v_isShared_911_ = v_isSharedCheck_916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_906_);
                v___x_912_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_912_, 0, v_ref_906_);
                leanh::lean_ctor_set(v___x_912_, 1, v_a_908_);
                if v_isShared_911_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_910_, 1);
                    leanh::lean_ctor_set(v___x_910_, 0, v___x_912_);
                    v___x_914_ = v___x_910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
                    v___x_914_ = v_reuseFailAlloc_915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg___boxed(
    mut v_msg_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_917_, v___y_918_, v___y_919_);
    leanh::lean_dec(v___y_919_);
    leanh::lean_dec_ref(v___y_918_);
    return v_res_921_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(
    mut v_ref_922_: *mut leanh::LeanObject,
    mut v_msg_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_939_: u8 = 0;
    let mut v_cancelTk_x3f_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_941_: u8 = 0;
    let mut v_inheritedTraceOptions_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_927_ = leanh::lean_ctor_get(v___y_924_, 0);
    v_fileMap_928_ = leanh::lean_ctor_get(v___y_924_, 1);
    v_options_929_ = leanh::lean_ctor_get(v___y_924_, 2);
    v_currRecDepth_930_ = leanh::lean_ctor_get(v___y_924_, 3);
    v_maxRecDepth_931_ = leanh::lean_ctor_get(v___y_924_, 4);
    v_ref_932_ = leanh::lean_ctor_get(v___y_924_, 5);
    v_currNamespace_933_ = leanh::lean_ctor_get(v___y_924_, 6);
    v_openDecls_934_ = leanh::lean_ctor_get(v___y_924_, 7);
    v_initHeartbeats_935_ = leanh::lean_ctor_get(v___y_924_, 8);
    v_maxHeartbeats_936_ = leanh::lean_ctor_get(v___y_924_, 9);
    v_quotContext_937_ = leanh::lean_ctor_get(v___y_924_, 10);
    v_currMacroScope_938_ = leanh::lean_ctor_get(v___y_924_, 11);
    v_diag_939_ = leanh::lean_ctor_get_uint8(
        v___y_924_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_940_ = leanh::lean_ctor_get(v___y_924_, 12);
    v_suppressElabErrors_941_ = leanh::lean_ctor_get_uint8(
        v___y_924_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_942_ = leanh::lean_ctor_get(v___y_924_, 13);
    v_ref_943_ = l_Lean_replaceRef(v_ref_922_, v_ref_932_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_942_);
    leanh::lean_inc(v_cancelTk_x3f_940_);
    leanh::lean_inc(v_currMacroScope_938_);
    leanh::lean_inc(v_quotContext_937_);
    leanh::lean_inc(v_maxHeartbeats_936_);
    leanh::lean_inc(v_initHeartbeats_935_);
    leanh::lean_inc(v_openDecls_934_);
    leanh::lean_inc(v_currNamespace_933_);
    leanh::lean_inc(v_maxRecDepth_931_);
    leanh::lean_inc(v_currRecDepth_930_);
    leanh::lean_inc_ref(v_options_929_);
    leanh::lean_inc_ref(v_fileMap_928_);
    leanh::lean_inc_ref(v_fileName_927_);
    v___x_944_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_944_, 0, v_fileName_927_);
    leanh::lean_ctor_set(v___x_944_, 1, v_fileMap_928_);
    leanh::lean_ctor_set(v___x_944_, 2, v_options_929_);
    leanh::lean_ctor_set(v___x_944_, 3, v_currRecDepth_930_);
    leanh::lean_ctor_set(v___x_944_, 4, v_maxRecDepth_931_);
    leanh::lean_ctor_set(v___x_944_, 5, v_ref_943_);
    leanh::lean_ctor_set(v___x_944_, 6, v_currNamespace_933_);
    leanh::lean_ctor_set(v___x_944_, 7, v_openDecls_934_);
    leanh::lean_ctor_set(v___x_944_, 8, v_initHeartbeats_935_);
    leanh::lean_ctor_set(v___x_944_, 9, v_maxHeartbeats_936_);
    leanh::lean_ctor_set(v___x_944_, 10, v_quotContext_937_);
    leanh::lean_ctor_set(v___x_944_, 11, v_currMacroScope_938_);
    leanh::lean_ctor_set(v___x_944_, 12, v_cancelTk_x3f_940_);
    leanh::lean_ctor_set(v___x_944_, 13, v_inheritedTraceOptions_942_);
    leanh::lean_ctor_set_uint8(
        v___x_944_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_939_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_944_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_941_,
    );
    v___x_945_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_923_, v___x_944_, v___y_925_);
    leanh::lean_dec_ref_known(v___x_944_, 14);
    return v___x_945_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg___boxed(
    mut v_ref_946_: *mut leanh::LeanObject,
    mut v_msg_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_946_, v_msg_947_, v___y_948_, v___y_949_);
    leanh::lean_dec(v___y_949_);
    leanh::lean_dec_ref(v___y_948_);
    leanh::lean_dec(v_ref_946_);
    return v_res_951_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__0;
    v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
    return v___x_954_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(
    mut v_as_958_: *mut leanh::LeanObject,
    mut v_sz_959_: usize,
    mut v_i_960_: usize,
    mut v_b_961_: *mut leanh::LeanObject,
    mut v___y_962_: *mut leanh::LeanObject,
    mut v___y_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: usize = 0;
    let mut v___x_968_: usize = 0;
    let mut v___x_970_: u8 = 0;
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut v_val_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_970_ = lean_usize_dec_lt(v_i_960_, v_sz_959_);
                if v___x_970_ == 0 {
                    v___x_971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_971_, 0, v_b_961_);
                    return v___x_971_;
                } else {
                    v___x_972_ = leanh::lean_unsigned_to_nat(1);
                    v___x_973_ = leanh::lean_unsigned_to_nat(0);
                    v_a_974_ = lean_array_uget_borrowed(v_as_958_, v_i_960_);
                    v___x_1001_ = l_Lean_Syntax_getArg(v_a_974_, v___x_973_);
                    v___x_1002_ = l_Lean_Syntax_isNone(v___x_1001_);
                    if v___x_1002_ == 0 {
                        v___x_1003_ = l_Lean_Syntax_getArg(v___x_1001_, v___x_973_);
                        leanh::lean_dec(v___x_1001_);
                        v___x_1004_ = l_Lean_Syntax_getId(v___x_1003_);
                        leanh::lean_dec(v___x_1003_);
                        v___y_985_ = v___x_1004_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1001_);
                        v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3;
                        v___y_985_ = v___x_1005_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_967_ = 1usize;
                v___x_968_ = lean_usize_add(v_i_960_, v___x_967_);
                v_i_960_ = v___x_968_;
                v_b_961_ = v_a_966_;
                state = 0;
                continue;
            }
            2 => {
                v___x_978_ = l_Lean_Syntax_getArg(v_a_974_, v___x_972_);
                v___x_979_ = l_Lean_Syntax_isNone(v___x_978_);
                leanh::lean_dec(v___x_978_);
                if v___x_979_ == 0 {
                    v___x_980_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_980_, 0, v___y_976_);
                    leanh::lean_ctor_set(v___x_980_, 1, v_str_977_);
                    v___x_981_ = lean_array_push(v_b_961_, v___x_980_);
                    v_a_966_ = v___x_981_;
                    state = 1;
                    continue;
                } else {
                    v___x_982_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_982_, 0, v___y_976_);
                    leanh::lean_ctor_set(v___x_982_, 1, v_str_977_);
                    v___x_983_ = lean_array_push(v_b_961_, v___x_982_);
                    v_a_966_ = v___x_983_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_986_ = leanh::lean_unsigned_to_nat(2);
                v___x_987_ = l_Lean_Syntax_getArg(v_a_974_, v___x_986_);
                v___x_988_ = l_Lean_Syntax_isStrLit_x3f(v___x_987_);
                if leanh::lean_obj_tag(v___x_988_) == 0 {
                    v___x_989_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__1);
                    v___x_990_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v___x_987_, v___x_989_, v___y_962_, v___y_963_);
                    leanh::lean_dec(v___x_987_);
                    if leanh::lean_obj_tag(v___x_990_) == 0 {
                        v_a_991_ = leanh::lean_ctor_get(v___x_990_, 0);
                        leanh::lean_inc(v_a_991_);
                        leanh::lean_dec_ref_known(v___x_990_, 1);
                        v___y_976_ = v___y_985_;
                        v_str_977_ = v_a_991_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_985_);
                        leanh::lean_dec_ref(v_b_961_);
                        v_a_992_ = leanh::lean_ctor_get(v___x_990_, 0);
                        v_isSharedCheck_999_ = (!leanh::lean_is_exclusive(v___x_990_)) as u8;
                        if v_isSharedCheck_999_ == 0 {
                            v___x_994_ = v___x_990_;
                            v_isShared_995_ = v_isSharedCheck_999_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_992_);
                            leanh::lean_dec(v___x_990_);
                            v___x_994_ = leanh::lean_box(0);
                            v_isShared_995_ = v_isSharedCheck_999_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_987_);
                    v_val_1000_ = leanh::lean_ctor_get(v___x_988_, 0);
                    leanh::lean_inc(v_val_1000_);
                    leanh::lean_dec_ref_known(v___x_988_, 1);
                    v___y_976_ = v___y_985_;
                    v_str_977_ = v_val_1000_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_995_ == 0 {
                    v___x_997_ = v___x_994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___boxed(
    mut v_as_1006_: *mut leanh::LeanObject,
    mut v_sz_1007_: *mut leanh::LeanObject,
    mut v_i_1008_: *mut leanh::LeanObject,
    mut v_b_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
    mut v___y_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1013_: usize = 0;
    let mut v_i_boxed_1014_: usize = 0;
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1013_ = leanh::lean_unbox_usize(v_sz_1007_);
    leanh::lean_dec(v_sz_1007_);
    v_i_boxed_1014_ = leanh::lean_unbox_usize(v_i_1008_);
    leanh::lean_dec(v_i_1008_);
    v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_as_1006_, v_sz_boxed_1013_, v_i_boxed_1014_, v_b_1009_, v___y_1010_, v___y_1011_);
    leanh::lean_dec(v___y_1011_);
    leanh::lean_dec_ref(v___y_1010_);
    leanh::lean_dec_ref(v_as_1006_);
    return v_res_1015_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(
    mut v_stx_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entriesStx_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v_entries_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1034_: usize = 0;
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_a_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1027_ = leanh::lean_unsigned_to_nat(1);
                v___x_1028_ = l_Lean_Syntax_getArg(v_stx_1023_, v___x_1027_);
                v_entriesStx_1029_ = l_Lean_Syntax_getArgs(v___x_1028_);
                leanh::lean_dec(v___x_1028_);
                v___x_1030_ = lean_array_get_size(v_entriesStx_1029_);
                v___x_1031_ = leanh::lean_unsigned_to_nat(0);
                v___x_1032_ = lean_nat_dec_eq(v___x_1030_, v___x_1031_);
                if v___x_1032_ == 0 {
                    v_entries_1033_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__0;
                    v_sz_1034_ = lean_array_size(v_entriesStx_1029_);
                    v___x_1035_ = 0usize;
                    v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1(v_entriesStx_1029_, v_sz_1034_, v___x_1035_, v_entries_1033_, v_a_1024_, v_a_1025_);
                    leanh::lean_dec_ref(v_entriesStx_1029_);
                    if leanh::lean_obj_tag(v___x_1036_) == 0 {
                        v_a_1037_ = leanh::lean_ctor_get(v___x_1036_, 0);
                        v_isSharedCheck_1045_ =
                            (!leanh::lean_is_exclusive(v___x_1036_)) as u8;
                        if v_isSharedCheck_1045_ == 0 {
                            v___x_1039_ = v___x_1036_;
                            v_isShared_1040_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1037_);
                            leanh::lean_dec(v___x_1036_);
                            v___x_1039_ = leanh::lean_box(0);
                            v_isShared_1040_ = v_isSharedCheck_1045_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1046_ = leanh::lean_ctor_get(v___x_1036_, 0);
                        v_isSharedCheck_1053_ =
                            (!leanh::lean_is_exclusive(v___x_1036_)) as u8;
                        if v_isSharedCheck_1053_ == 0 {
                            v___x_1048_ = v___x_1036_;
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1046_);
                            leanh::lean_dec(v___x_1036_);
                            v___x_1048_ = leanh::lean_box(0);
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_entriesStx_1029_);
                    v___x_1054_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__2;
                    v___x_1055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1055_, 0, v___x_1054_);
                    return v___x_1055_;
                }
            }
            1 => {
                v___x_1041_ = lean_array_to_list(v_a_1037_);
                if v_isShared_1040_ == 0 {
                    leanh::lean_ctor_set(v___x_1039_, 0, v___x_1041_);
                    v___x_1043_ = v___x_1039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
                    v___x_1043_ = v_reuseFailAlloc_1044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1043_;
            }
            3 => {
                if v_isShared_1049_ == 0 {
                    v___x_1051_ = v___x_1048_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
                    v___x_1051_ = v_reuseFailAlloc_1052_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___boxed(
    mut v_stx_1056_: *mut leanh::LeanObject,
    mut v_a_1057_: *mut leanh::LeanObject,
    mut v_a_1058_: *mut leanh::LeanObject,
    mut v_a_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(
        v_stx_1056_,
        v_a_1057_,
        v_a_1058_,
    );
    leanh::lean_dec(v_a_1058_);
    leanh::lean_dec_ref(v_a_1057_);
    leanh::lean_dec(v_stx_1056_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(
    mut v_00_u03b1_1061_: *mut leanh::LeanObject,
    mut v_ref_1062_: *mut leanh::LeanObject,
    mut v_msg_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
    mut v___y_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___redArg(v_ref_1062_, v_msg_1063_, v___y_1064_, v___y_1065_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0___boxed(
    mut v_00_u03b1_1068_: *mut leanh::LeanObject,
    mut v_ref_1069_: *mut leanh::LeanObject,
    mut v_msg_1070_: *mut leanh::LeanObject,
    mut v___y_1071_: *mut leanh::LeanObject,
    mut v___y_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0(v_00_u03b1_1068_, v_ref_1069_, v_msg_1070_, v___y_1071_, v___y_1072_);
    leanh::lean_dec(v___y_1072_);
    leanh::lean_dec_ref(v___y_1071_);
    leanh::lean_dec(v_ref_1069_);
    return v_res_1074_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(
    mut v_00_u03b1_1075_: *mut leanh::LeanObject,
    mut v_msg_1076_: *mut leanh::LeanObject,
    mut v___y_1077_: *mut leanh::LeanObject,
    mut v___y_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___redArg(v_msg_1076_, v___y_1077_, v___y_1078_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0___boxed(
    mut v_00_u03b1_1081_: *mut leanh::LeanObject,
    mut v_msg_1082_: *mut leanh::LeanObject,
    mut v___y_1083_: *mut leanh::LeanObject,
    mut v___y_1084_: *mut leanh::LeanObject,
    mut v___y_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__0_spec__0(v_00_u03b1_1081_, v_msg_1082_, v___y_1083_, v___y_1084_);
    leanh::lean_dec(v___y_1084_);
    leanh::lean_dec_ref(v___y_1083_);
    return v_res_1086_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(
    mut v_x_1087_: *mut leanh::LeanObject,
    mut v_stx_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData(
        v_stx_1088_,
        v___y_1089_,
        v___y_1090_,
    );
    return v___x_1092_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(
    mut v_x_1093_: *mut leanh::LeanObject,
    mut v_stx_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
    mut v___y_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_x_1093_, v_stx_1094_, v___y_1095_, v___y_1096_);
    leanh::lean_dec(v___y_1096_);
    leanh::lean_dec_ref(v___y_1095_);
    leanh::lean_dec(v_stx_1094_);
    leanh::lean_dec(v_x_1093_);
    return v_res_1098_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(
    mut v_declName_1099_: *mut leanh::LeanObject,
    mut v_externAttrData_1100_: *mut leanh::LeanObject,
    mut v___y_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1105_: u8 = 0;
    let mut v___y_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: u8 = 0;
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: u8 = 0;
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1128_: u8 = 0;
    let mut v_unused_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1112_ = lean_st_ref_get(v___y_1102_);
                v_env_1113_ = leanh::lean_ctor_get(v___x_1112_, 0);
                leanh::lean_inc_ref_n(v_env_1113_, 2);
                leanh::lean_dec(v___x_1112_);
                leanh::lean_inc(v_declName_1099_);
                v___x_1130_ = l_Lean_Environment_isProjectionFn(v_env_1113_, v_declName_1099_);
                if v___x_1130_ == 0 {
                    leanh::lean_inc(v_declName_1099_);
                    leanh::lean_inc_ref(v_env_1113_);
                    v___x_1131_ = l_Lean_Environment_isConstructor(v_env_1113_, v_declName_1099_);
                    v___y_1115_ = v___x_1131_;
                    state = 2;
                    continue;
                } else {
                    v___y_1115_ = v___x_1130_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1108_ = leanh::lean_unsigned_to_nat(1);
                v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
                v___x_1110_ = lean_array_push(v___x_1109_, v_declName_1099_);
                v___x_1111_ =
                    l_Lean_compileDecls(v___x_1110_, v___y_1105_, v___y_1106_, v___y_1107_);
                return v___x_1111_;
            }
            2 => {
                if v___y_1115_ == 0 {
                    leanh::lean_dec_ref(v_env_1113_);
                    leanh::lean_dec(v_declName_1099_);
                    v___x_1116_ = leanh::lean_box(0);
                    v___x_1117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1117_, 0, v___x_1116_);
                    return v___x_1117_;
                } else {
                    v___x_1118_ = 0;
                    leanh::lean_inc(v_declName_1099_);
                    v___x_1119_ =
                        l_Lean_Environment_find_x3f(v_env_1113_, v_declName_1099_, v___x_1118_);
                    if leanh::lean_obj_tag(v___x_1119_) == 1 {
                        v_val_1120_ = leanh::lean_ctor_get(v___x_1119_, 0);
                        leanh::lean_inc(v_val_1120_);
                        leanh::lean_dec_ref_known(v___x_1119_, 1);
                        if leanh::lean_obj_tag(v_val_1120_) == 2 {
                            leanh::lean_dec(v_declName_1099_);
                            v_isSharedCheck_1128_ =
                                (!leanh::lean_is_exclusive(v_val_1120_)) as u8;
                            if v_isSharedCheck_1128_ == 0 {
                                v_unused_1129_ = leanh::lean_ctor_get(v_val_1120_, 0);
                                leanh::lean_dec(v_unused_1129_);
                                v___x_1122_ = v_val_1120_;
                                v_isShared_1123_ = v_isSharedCheck_1128_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_1120_);
                                v___x_1122_ = leanh::lean_box(0);
                                v_isShared_1123_ = v_isSharedCheck_1128_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_1120_);
                            v___y_1105_ = v___y_1115_;
                            v___y_1106_ = v___y_1101_;
                            v___y_1107_ = v___y_1102_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1119_);
                        v___y_1105_ = v___y_1115_;
                        v___y_1106_ = v___y_1101_;
                        v___y_1107_ = v___y_1102_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1124_ = leanh::lean_box(0);
                if v_isShared_1123_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1122_, 0);
                    leanh::lean_ctor_set(v___x_1122_, 0, v___x_1124_);
                    v___x_1126_ = v___x_1122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1127_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
                    v___x_1126_ = v_reuseFailAlloc_1127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(
    mut v_declName_1132_: *mut leanh::LeanObject,
    mut v_externAttrData_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v_declName_1132_, v_externAttrData_1133_, v___y_1134_, v___y_1135_);
    leanh::lean_dec(v___y_1135_);
    leanh::lean_dec_ref(v___y_1134_);
    leanh::lean_dec(v_externAttrData_1133_);
    return v_res_1137_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(
    mut v___x_1138_: u8,
    mut v_env_1139_: *mut leanh::LeanObject,
    mut v_n_1140_: *mut leanh::LeanObject,
    mut v_x_1141_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1142_: u8 = 0;
    v___x_1142_ = l_Lean_Environment_contains(v_env_1139_, v_n_1140_, v___x_1138_);
    return v___x_1142_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(
    mut v___x_1143_: *mut leanh::LeanObject,
    mut v_env_1144_: *mut leanh::LeanObject,
    mut v_n_1145_: *mut leanh::LeanObject,
    mut v_x_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_632__boxed_1147_: u8 = 0;
    let mut v_res_1148_: u8 = 0;
    let mut v_r_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_632__boxed_1147_ = (leanh::lean_unbox(v___x_1143_) as u8);
    v_res_1148_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___lam__2_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_(v___x_632__boxed_1147_, v_env_1144_, v_n_1145_, v_x_1146_);
    leanh::lean_dec(v_x_1146_);
    v_r_1149_ = leanh::lean_box((v_res_1148_) as usize);
    return v_r_1149_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_;
    v___x_1177_ = l_Lean_registerParametricAttribute___redArg(v___x_1176_);
    return v___x_1177_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2____boxed(
    mut v_a_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
    return v_res_1179_;
}
pub unsafe fn l_Lean_getExternAttrData_x3f(
    mut v_env_1180_: *mut leanh::LeanObject,
    mut v_n_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = leanh::lean_box(0);
    v___x_1183_ = l_Lean_externAttr;
    v___x_1184_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_1182_,
        v___x_1183_,
        v_env_1180_,
        v_n_1181_,
    );
    return v___x_1184_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(
    mut v_pattern_1185_: *mut leanh::LeanObject,
    mut v_it_1186_: *mut leanh::LeanObject,
    mut v_r_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1194_: u32 = 0;
    let mut v___y_1196_: u8 = 0;
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u32 = 0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: u32 = 0;
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1188_ = leanh::lean_ctor_get(v_pattern_1185_, 0);
                v_startInclusive_1189_ = leanh::lean_ctor_get(v_pattern_1185_, 1);
                v_endExclusive_1190_ = leanh::lean_ctor_get(v_pattern_1185_, 2);
                v___x_1191_ = lean_nat_sub(v_endExclusive_1190_, v_startInclusive_1189_);
                v___x_1192_ = lean_nat_dec_eq(v_it_1186_, v___x_1191_);
                leanh::lean_dec(v___x_1191_);
                if v___x_1192_ == 0 {
                    v___x_1193_ = lean_nat_add(v_startInclusive_1189_, v_it_1186_);
                    v_c_1194_ = lean_string_utf8_get_fast(v_str_1188_, v___x_1193_);
                    v___x_1207_ = 48;
                    v___x_1208_ = lean_uint32_dec_le(v___x_1207_, v_c_1194_);
                    if v___x_1208_ == 0 {
                        v___y_1196_ = v___x_1208_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1209_ = 57;
                        v___x_1210_ = lean_uint32_dec_le(v_c_1194_, v___x_1209_);
                        v___y_1196_ = v___x_1210_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1211_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1211_, 0, v_it_1186_);
                    leanh::lean_ctor_set(v___x_1211_, 1, v_r_1187_);
                    return v___x_1211_;
                }
            }
            1 => {
                if v___y_1196_ == 0 {
                    leanh::lean_dec(v___x_1193_);
                    v___x_1197_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1197_, 0, v_it_1186_);
                    leanh::lean_ctor_set(v___x_1197_, 1, v_r_1187_);
                    return v___x_1197_;
                } else {
                    leanh::lean_dec(v_it_1186_);
                    v___x_1198_ = lean_string_utf8_next_fast(v_str_1188_, v___x_1193_);
                    leanh::lean_dec(v___x_1193_);
                    v___x_1199_ = lean_nat_sub(v___x_1198_, v_startInclusive_1189_);
                    v___x_1200_ = leanh::lean_unsigned_to_nat(10);
                    v___x_1201_ = lean_nat_mul(v_r_1187_, v___x_1200_);
                    leanh::lean_dec(v_r_1187_);
                    v___x_1202_ = lean_uint32_to_nat(v_c_1194_);
                    v___x_1203_ = leanh::lean_unsigned_to_nat(48);
                    v___x_1204_ = lean_nat_sub(v___x_1202_, v___x_1203_);
                    leanh::lean_dec(v___x_1202_);
                    v___x_1205_ = lean_nat_add(v___x_1201_, v___x_1204_);
                    leanh::lean_dec(v___x_1204_);
                    leanh::lean_dec(v___x_1201_);
                    v_it_1186_ = v___x_1199_;
                    v_r_1187_ = v___x_1205_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum___boxed(
    mut v_pattern_1212_: *mut leanh::LeanObject,
    mut v_it_1213_: *mut leanh::LeanObject,
    mut v_r_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(
        v_pattern_1212_,
        v_it_1213_,
        v_r_1214_,
    );
    leanh::lean_dec_ref(v_pattern_1212_);
    return v_res_1215_;
}
pub unsafe fn l_Lean_expandExternPatternAux(
    mut v_args_1217_: *mut leanh::LeanObject,
    mut v_pattern_1218_: *mut leanh::LeanObject,
    mut v_it_1219_: *mut leanh::LeanObject,
    mut v_r_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v_c_1223_: u32 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u32 = 0;
    let mut v___x_1229_: u8 = 0;
    let mut v_it_u2081_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1221_ = lean_string_utf8_byte_size(v_pattern_1218_);
                v___x_1222_ = lean_nat_dec_eq(v_it_1219_, v___x_1221_);
                if v___x_1222_ == 0 {
                    v_c_1223_ = lean_string_utf8_get_fast(v_pattern_1218_, v_it_1219_);
                    v___x_1228_ = 35;
                    v___x_1229_ = lean_uint32_dec_eq(v_c_1223_, v___x_1228_);
                    if v___x_1229_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v___x_1222_ == 0 {
                            v_it_u2081_1230_ =
                                lean_string_utf8_next_fast(v_pattern_1218_, v_it_1219_);
                            leanh::lean_dec(v_it_1219_);
                            leanh::lean_inc_ref(v_pattern_1218_);
                            v___x_1231_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_1231_, 0, v_pattern_1218_);
                            leanh::lean_ctor_set(v___x_1231_, 1, v_it_u2081_1230_);
                            leanh::lean_ctor_set(v___x_1231_, 2, v___x_1221_);
                            v___x_1232_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1233_ = l___private_Lean_Compiler_ExternAttr_0__Lean_parseOptNum(
                                v___x_1231_,
                                v___x_1232_,
                                v___x_1232_,
                            );
                            leanh::lean_dec_ref_known(v___x_1231_, 3);
                            v_fst_1234_ = leanh::lean_ctor_get(v___x_1233_, 0);
                            leanh::lean_inc(v_fst_1234_);
                            v_snd_1235_ = leanh::lean_ctor_get(v___x_1233_, 1);
                            leanh::lean_inc(v_snd_1235_);
                            leanh::lean_dec_ref(v___x_1233_);
                            v___x_1236_ = leanh::lean_unsigned_to_nat(1);
                            v_j_1237_ = lean_nat_sub(v_snd_1235_, v___x_1236_);
                            leanh::lean_dec(v_snd_1235_);
                            v___x_1238_ = lean_nat_add(v_it_u2081_1230_, v_fst_1234_);
                            leanh::lean_dec(v_fst_1234_);
                            v___x_1239_ = l_Lean_expandExternPatternAux___closed__0;
                            v___x_1240_ =
                                l_List_getD___redArg(v_args_1217_, v_j_1237_, v___x_1239_);
                            v___x_1241_ = lean_string_append(v_r_1220_, v___x_1240_);
                            leanh::lean_dec(v___x_1240_);
                            v_it_1219_ = v___x_1238_;
                            v_r_1220_ = v___x_1241_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_it_1219_);
                    leanh::lean_dec_ref(v_pattern_1218_);
                    return v_r_1220_;
                }
            }
            1 => {
                v___x_1225_ = lean_string_utf8_next_fast(v_pattern_1218_, v_it_1219_);
                leanh::lean_dec(v_it_1219_);
                v___x_1226_ = lean_string_push(v_r_1220_, v_c_1223_);
                v_it_1219_ = v___x_1225_;
                v_r_1220_ = v___x_1226_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_expandExternPatternAux___boxed(
    mut v_args_1243_: *mut leanh::LeanObject,
    mut v_pattern_1244_: *mut leanh::LeanObject,
    mut v_it_1245_: *mut leanh::LeanObject,
    mut v_r_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1247_ =
        l_Lean_expandExternPatternAux(v_args_1243_, v_pattern_1244_, v_it_1245_, v_r_1246_);
    leanh::lean_dec(v_args_1243_);
    return v_res_1247_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___redArg(
    mut v_x_1248_: *mut leanh::LeanObject,
    mut v_h__1_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1250_ = leanh::lean_ctor_get(v_x_1248_, 0);
    leanh::lean_inc(v_fst_1250_);
    v_snd_1251_ = leanh::lean_ctor_get(v_x_1248_, 1);
    leanh::lean_inc(v_snd_1251_);
    leanh::lean_dec_ref(v_x_1248_);
    v___x_1252_ = leanh::lean_apply_2(v_h__1_1249_, v_fst_1250_, v_snd_1251_);
    return v___x_1252_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(
    mut v_pattern_1253_: *mut leanh::LeanObject,
    mut v_it_u2081_1254_: *mut leanh::LeanObject,
    mut v_motive_1255_: *mut leanh::LeanObject,
    mut v_x_1256_: *mut leanh::LeanObject,
    mut v_h__1_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1258_ = leanh::lean_ctor_get(v_x_1256_, 0);
    leanh::lean_inc(v_fst_1258_);
    v_snd_1259_ = leanh::lean_ctor_get(v_x_1256_, 1);
    leanh::lean_inc(v_snd_1259_);
    leanh::lean_dec_ref(v_x_1256_);
    v___x_1260_ = leanh::lean_apply_2(v_h__1_1257_, v_fst_1258_, v_snd_1259_);
    return v___x_1260_;
}
pub unsafe fn l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter___boxed(
    mut v_pattern_1261_: *mut leanh::LeanObject,
    mut v_it_u2081_1262_: *mut leanh::LeanObject,
    mut v_motive_1263_: *mut leanh::LeanObject,
    mut v_x_1264_: *mut leanh::LeanObject,
    mut v_h__1_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ =
        l___private_Lean_Compiler_ExternAttr_0__Lean_expandExternPatternAux_match__1_splitter(
            v_pattern_1261_,
            v_it_u2081_1262_,
            v_motive_1263_,
            v_x_1264_,
            v_h__1_1265_,
        );
    leanh::lean_dec(v_it_u2081_1262_);
    leanh::lean_dec_ref(v_pattern_1261_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_expandExternPattern(
    mut v_pattern_1267_: *mut leanh::LeanObject,
    mut v_args_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = leanh::lean_unsigned_to_nat(0);
    v___x_1270_ = l_Lean_expandExternPatternAux___closed__0;
    v___x_1271_ =
        l_Lean_expandExternPatternAux(v_args_1268_, v_pattern_1267_, v___x_1269_, v___x_1270_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_expandExternPattern___boxed(
    mut v_pattern_1272_: *mut leanh::LeanObject,
    mut v_args_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lean_expandExternPattern(v_pattern_1272_, v_args_1273_);
    leanh::lean_dec(v_args_1273_);
    return v_res_1274_;
}
pub unsafe fn l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(
    mut v_x_1275_: *mut leanh::LeanObject,
    mut v_x_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1276_) == 0 {
                    return v_x_1275_;
                } else {
                    v_head_1277_ = leanh::lean_ctor_get(v_x_1276_, 0);
                    v_tail_1278_ = leanh::lean_ctor_get(v_x_1276_, 1);
                    v___x_1279_ = lean_string_append(v_x_1275_, v_head_1277_);
                    v_x_1275_ = v___x_1279_;
                    v_x_1276_ = v_tail_1278_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0___boxed(
    mut v_x_1281_: *mut leanh::LeanObject,
    mut v_x_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v_x_1281_, v_x_1282_);
    leanh::lean_dec(v_x_1282_);
    return v_res_1283_;
}
pub unsafe fn l_Lean_mkSimpleFnCall(
    mut v_fn_1287_: *mut leanh::LeanObject,
    mut v_args_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = l_Lean_mkSimpleFnCall___closed__0;
    v___x_1290_ = lean_string_append(v_fn_1287_, v___x_1289_);
    v___x_1291_ = l_Lean_expandExternPatternAux___closed__0;
    v___x_1292_ = l_Lean_mkSimpleFnCall___closed__1;
    v___x_1293_ = l_List_intersperseTR___redArg(v___x_1292_, v_args_1288_);
    v___x_1294_ = l_List_foldl___at___00Lean_mkSimpleFnCall_spec__0(v___x_1291_, v___x_1293_);
    leanh::lean_dec(v___x_1293_);
    v___x_1295_ = lean_string_append(v___x_1290_, v___x_1294_);
    leanh::lean_dec_ref(v___x_1294_);
    v___x_1296_ = l_Lean_mkSimpleFnCall___closed__2;
    v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Lean_ExternEntry_backend(
    mut v_x_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1298_) == 3 {
        let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3;
        return v___x_1299_;
    } else {
        let mut v_backend_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_backend_1300_ = leanh::lean_ctor_get(v_x_1298_, 0);
        leanh::lean_inc(v_backend_1300_);
        return v_backend_1300_;
    }
}
pub unsafe fn l_Lean_ExternEntry_backend___boxed(
    mut v_x_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Lean_ExternEntry_backend(v_x_1301_);
    leanh::lean_dec(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(
    mut v_backend_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: u8 = 0;
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1304_) == 0 {
                    v___x_1305_ = leanh::lean_box(0);
                    return v___x_1305_;
                } else {
                    v_head_1306_ = leanh::lean_ctor_get(v_x_1304_, 0);
                    v_tail_1307_ = leanh::lean_ctor_get(v_x_1304_, 1);
                    v___x_1312_ = l_Lean_ExternEntry_backend(v_head_1306_);
                    v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__3;
                    v___x_1314_ = lean_name_eq(v___x_1312_, v___x_1313_);
                    if v___x_1314_ == 0 {
                        v___x_1315_ = lean_name_eq(v___x_1312_, v_backend_1303_);
                        leanh::lean_dec(v___x_1312_);
                        v___y_1309_ = v___x_1315_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1312_);
                        v___y_1309_ = v___x_1314_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1309_ == 0 {
                    v_x_1304_ = v_tail_1307_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_head_1306_);
                    v___x_1311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1311_, 0, v_head_1306_);
                    return v___x_1311_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0___boxed(
    mut v_backend_1316_: *mut leanh::LeanObject,
    mut v_x_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1318_ =
        l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_1316_, v_x_1317_);
    leanh::lean_dec(v_x_1317_);
    leanh::lean_dec(v_backend_1316_);
    return v_res_1318_;
}
pub unsafe fn l_Lean_getExternEntryForAux(
    mut v_backend_1319_: *mut leanh::LeanObject,
    mut v_entries_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(
        v_backend_1319_,
        v_entries_1320_,
    );
    return v___x_1321_;
}
pub unsafe fn l_Lean_getExternEntryForAux___boxed(
    mut v_backend_1322_: *mut leanh::LeanObject,
    mut v_entries_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1324_ = l_Lean_getExternEntryForAux(v_backend_1322_, v_entries_1323_);
    leanh::lean_dec(v_entries_1323_);
    leanh::lean_dec(v_backend_1322_);
    return v_res_1324_;
}
pub unsafe fn l_Lean_getExternEntryFor(
    mut v_d_1325_: *mut leanh::LeanObject,
    mut v_backend_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ =
        l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(v_backend_1326_, v_d_1325_);
    return v___x_1327_;
}
pub unsafe fn l_Lean_getExternEntryFor___boxed(
    mut v_d_1328_: *mut leanh::LeanObject,
    mut v_backend_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lean_getExternEntryFor(v_d_1328_, v_backend_1329_);
    leanh::lean_dec(v_backend_1329_);
    leanh::lean_dec(v_d_1328_);
    return v_res_1330_;
}
pub unsafe fn l_Lean_isExtern(
    mut v_env_1331_: *mut leanh::LeanObject,
    mut v_fn_1332_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = l_Lean_getExternAttrData_x3f(v_env_1331_, v_fn_1332_);
    if leanh::lean_obj_tag(v___x_1333_) == 0 {
        let mut v___x_1334_: u8 = 0;
        v___x_1334_ = 0;
        return v___x_1334_;
    } else {
        let mut v___x_1335_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_1333_, 1);
        v___x_1335_ = 1;
        return v___x_1335_;
    }
}
pub unsafe fn l_Lean_isExtern___boxed(
    mut v_env_1336_: *mut leanh::LeanObject,
    mut v_fn_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1338_: u8 = 0;
    let mut v_r_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1338_ = l_Lean_isExtern(v_env_1336_, v_fn_1337_);
    v_r_1339_ = leanh::lean_box((v_res_1338_) as usize);
    return v_r_1339_;
}
pub unsafe fn l_Lean_isExternC(
    mut v_env_1340_: *mut leanh::LeanObject,
    mut v_fn_1341_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_getExternAttrData_x3f(v_env_1340_, v_fn_1341_);
    if leanh::lean_obj_tag(v___x_1342_) == 1 {
        let mut v_val_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1343_ = leanh::lean_ctor_get(v___x_1342_, 0);
        leanh::lean_inc(v_val_1343_);
        leanh::lean_dec_ref_known(v___x_1342_, 1);
        if leanh::lean_obj_tag(v_val_1343_) == 1 {
            let mut v_head_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1344_ = leanh::lean_ctor_get(v_val_1343_, 0);
            if leanh::lean_obj_tag(v_head_1344_) == 2 {
                let mut v_backend_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_backend_1345_ = leanh::lean_ctor_get(v_head_1344_, 0);
                leanh::lean_inc(v_backend_1345_);
                if leanh::lean_obj_tag(v_backend_1345_) == 1 {
                    let mut v_pre_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_pre_1346_ = leanh::lean_ctor_get(v_backend_1345_, 0);
                    if leanh::lean_obj_tag(v_pre_1346_) == 0 {
                        let mut v_tail_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1350_: u8 = 0;
                        v_tail_1347_ = leanh::lean_ctor_get(v_val_1343_, 1);
                        leanh::lean_inc(v_tail_1347_);
                        leanh::lean_dec_ref_known(v_val_1343_, 2);
                        v_str_1348_ = leanh::lean_ctor_get(v_backend_1345_, 1);
                        leanh::lean_inc_ref(v_str_1348_);
                        leanh::lean_dec_ref_known(v_backend_1345_, 2);
                        v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData_spec__1___closed__2;
                        v___x_1350_ = lean_string_dec_eq(v_str_1348_, v___x_1349_);
                        leanh::lean_dec_ref(v_str_1348_);
                        if v___x_1350_ == 0 {
                            leanh::lean_dec(v_tail_1347_);
                            return v___x_1350_;
                        } else {
                            if leanh::lean_obj_tag(v_tail_1347_) == 0 {
                                return v___x_1350_;
                            } else {
                                let mut v___x_1351_: u8 = 0;
                                leanh::lean_dec(v_tail_1347_);
                                v___x_1351_ = 0;
                                return v___x_1351_;
                            }
                        }
                    } else {
                        let mut v___x_1352_: u8 = 0;
                        leanh::lean_dec_ref_known(v_backend_1345_, 2);
                        leanh::lean_dec_ref_known(v_val_1343_, 2);
                        v___x_1352_ = 0;
                        return v___x_1352_;
                    }
                } else {
                    let mut v___x_1353_: u8 = 0;
                    leanh::lean_dec(v_backend_1345_);
                    leanh::lean_dec_ref_known(v_val_1343_, 2);
                    v___x_1353_ = 0;
                    return v___x_1353_;
                }
            } else {
                let mut v___x_1354_: u8 = 0;
                leanh::lean_dec_ref_known(v_val_1343_, 2);
                v___x_1354_ = 0;
                return v___x_1354_;
            }
        } else {
            let mut v___x_1355_: u8 = 0;
            leanh::lean_dec(v_val_1343_);
            v___x_1355_ = 0;
            return v___x_1355_;
        }
    } else {
        let mut v___x_1356_: u8 = 0;
        leanh::lean_dec(v___x_1342_);
        v___x_1356_ = 0;
        return v___x_1356_;
    }
}
pub unsafe fn l_Lean_isExternC___boxed(
    mut v_env_1357_: *mut leanh::LeanObject,
    mut v_fn_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: u8 = 0;
    let mut v_r_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Lean_isExternC(v_env_1357_, v_fn_1358_);
    v_r_1360_ = leanh::lean_box((v_res_1359_) as usize);
    return v_r_1360_;
}
pub unsafe fn l_Lean_getExternNameFor(
    mut v_env_1361_: *mut leanh::LeanObject,
    mut v_backend_1362_: *mut leanh::LeanObject,
    mut v_fn_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v_fn_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1364_ = l_Lean_getExternAttrData_x3f(v_env_1361_, v_fn_1363_);
                if leanh::lean_obj_tag(v___x_1364_) == 0 {
                    v___x_1365_ = leanh::lean_box(0);
                    return v___x_1365_;
                } else {
                    v_val_1366_ = leanh::lean_ctor_get(v___x_1364_, 0);
                    leanh::lean_inc(v_val_1366_);
                    leanh::lean_dec_ref_known(v___x_1364_, 1);
                    v___x_1367_ = l_List_find_x3f___at___00Lean_getExternEntryForAux_spec__0(
                        v_backend_1362_,
                        v_val_1366_,
                    );
                    leanh::lean_dec(v_val_1366_);
                    if leanh::lean_obj_tag(v___x_1367_) == 0 {
                        v___x_1368_ = leanh::lean_box(0);
                        return v___x_1368_;
                    } else {
                        v_val_1369_ = leanh::lean_ctor_get(v___x_1367_, 0);
                        v_isSharedCheck_1378_ =
                            (!leanh::lean_is_exclusive(v___x_1367_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1371_ = v___x_1367_;
                            v_isShared_1372_ = v_isSharedCheck_1378_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1369_);
                            leanh::lean_dec(v___x_1367_);
                            v___x_1371_ = leanh::lean_box(0);
                            v_isShared_1372_ = v_isSharedCheck_1378_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_1369_) == 2 {
                    v_fn_1373_ = leanh::lean_ctor_get(v_val_1369_, 1);
                    leanh::lean_inc_ref(v_fn_1373_);
                    leanh::lean_dec_ref_known(v_val_1369_, 2);
                    if v_isShared_1372_ == 0 {
                        leanh::lean_ctor_set(v___x_1371_, 0, v_fn_1373_);
                        v___x_1375_ = v___x_1371_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fn_1373_);
                        v___x_1375_ = v_reuseFailAlloc_1376_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1371_);
                    leanh::lean_dec(v_val_1369_);
                    v___x_1377_ = leanh::lean_box(0);
                    return v___x_1377_;
                }
            }
            2 => {
                return v___x_1375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getExternNameFor___boxed(
    mut v_env_1379_: *mut leanh::LeanObject,
    mut v_backend_1380_: *mut leanh::LeanObject,
    mut v_fn_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Lean_getExternNameFor(v_env_1379_, v_backend_1380_, v_fn_1381_);
    leanh::lean_dec(v_backend_1380_);
    return v_res_1382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_ExternAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ProjFns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedExternAttrData_default = _init_l_Lean_instInhabitedExternAttrData_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedExternAttrData_default);
    l_Lean_instInhabitedExternAttrData = _init_l_Lean_instInhabitedExternAttrData();
    leanh::lean_mark_persistent(l_Lean_instInhabitedExternAttrData);
    res = l___private_Lean_Compiler_ExternAttr_0__Lean_initFn_00___x40_Lean_Compiler_ExternAttr_2498400062____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_externAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_externAttr);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_ExternAttr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_ExternAttr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ProjFns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_ExternAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_ExternAttr(builtin);
}