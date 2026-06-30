// Lean compiler output
// Module: Lean.Compiler.LCNF.ConfigOptions
// Imports: Lean.Data.Options
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
pub static l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default___closed__0_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((16 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((64 as usize) << 1) | 1) as *mut leanh::LeanObject,
        65792 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedConfigOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 109, 97, 108, 108, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,16264496820922384229 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<106> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 103, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 119, 105, 116, 104, 32, 115, 105, 122, 101, 32, 96, 226, 137, 164, 32, 115, 109, 97, 108, 108, 96, 32, 105, 115, 32, 105, 110, 108, 105, 110, 101, 100, 32, 101, 118, 101, 110, 32, 105, 102, 32, 116, 104, 101, 114, 101, 32, 97, 114, 101, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 46, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12891334116250683707 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_small: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 97, 120, 82, 101, 99, 73, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject,17423324612682002659 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value: leanh::LeanStringObject<155> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 155, m_capacity: 155, m_length: 154, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116, 105, 109, 101, 115, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 91, 105, 110, 108, 105, 110, 101, 93, 96, 32, 99, 97, 110, 32, 98, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 108, 121, 32, 105, 110, 108, 105, 110, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject,7732076117198460861 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_maxRecInline: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [109, 97, 120, 82, 101, 99, 73, 110, 108, 105, 110, 101, 73, 102, 82, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11151809928963299184 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value: leanh::LeanStringObject<165> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 165, m_capacity: 165, m_length: 164, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116, 105, 109, 101, 115, 32, 97, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 91, 105, 110, 108, 105, 110, 101, 95, 105, 102, 95, 114, 101, 100, 117, 99, 101, 93, 96, 32, 99, 97, 110, 32, 98, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 108, 121, 32, 105, 110, 108, 105, 110, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 16 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject,17997980487431182150 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_maxRecInlineIfReduce: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 84, 121, 112, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11379743648570689931 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value: leanh::LeanStringObject<210> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 210, m_capacity: 210, m_length: 209, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 112, 101, 114, 102, 111, 114, 109, 32, 116, 121, 112, 101, 32, 99, 111, 109, 112, 97, 116, 105, 98, 105, 108, 105, 116, 121, 32, 99, 104, 101, 99, 107, 105, 110, 103, 32, 97, 102, 116, 101, 114, 32, 101, 97, 99, 104, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 112, 97, 115, 115, 46, 32, 78, 111, 116, 101, 32, 116, 104, 105, 115, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 109, 112, 108, 101, 116, 101, 32, 99, 104, 101, 99, 107, 44, 32, 97, 110, 100, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 100, 32, 111, 110, 108, 121, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 112, 117, 114, 112, 111, 115, 101, 115, 46, 32, 73, 116, 32, 102, 97, 105, 108, 115, 32, 105, 110, 32, 99, 111, 100, 101, 32, 116, 104, 97, 116, 32, 109, 97, 107, 101, 115, 32, 104, 101, 97, 118, 121, 32, 117, 115, 101, 32, 111, 102, 32, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 116, 121, 112, 101, 115, 46, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject,753431753459230485 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_checkTypes: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 116, 114, 97, 99, 116, 95, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11820474812310478749 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 101, 110, 97, 98, 108, 101, 47, 100, 105, 115, 97, 98, 108, 101, 32, 99, 108, 111, 115, 101, 100, 32, 116, 101, 114, 109, 32, 99, 97, 99, 104, 105, 110, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12111255849164724419 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_extract__closed: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [109, 97, 120, 82, 101, 99, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10573091669154641317 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value: leanh::LeanStringObject<154> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 154, m_capacity: 154, m_length: 153, m_data: [40, 99, 111, 109, 112, 105, 108, 101, 114, 41, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 116, 105, 109, 101, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 64, 91, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 93, 96, 32, 99, 97, 110, 32, 98, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 108, 121, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5655657913681397115 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_maxRecSpecialize: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 101, 117, 115, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14541074971161486361 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13407523230617984227 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [104, 101, 117, 114, 105, 115, 116, 105, 99, 97, 108, 108, 121, 32, 105, 110, 115, 101, 114, 116, 32, 114, 101, 115, 101, 116, 47, 114, 101, 117, 115, 101, 32, 105, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 32, 112, 97, 105, 114, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6883333986318228743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11901872366496240573 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_compiler_reuse: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(
    mut v_name_286_: *mut leanh::LeanObject,
    mut v_decl_287_: *mut leanh::LeanObject,
    mut v_ref_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_298_: u8 = 0;
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_303_: u8 = 0;
    let mut v_unused_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_308_: u8 = 0;
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_290_ = leanh::lean_ctor_get(v_decl_287_, 0);
                v_descr_291_ = leanh::lean_ctor_get(v_decl_287_, 1);
                v_deprecation_x3f_292_ = leanh::lean_ctor_get(v_decl_287_, 2);
                leanh::lean_inc(v_defValue_290_);
                v___x_293_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_293_, 0, v_defValue_290_);
                leanh::lean_inc(v_deprecation_x3f_292_);
                leanh::lean_inc_ref(v_descr_291_);
                leanh::lean_inc_n(v_name_286_, 2);
                v___x_294_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_294_, 0, v_name_286_);
                leanh::lean_ctor_set(v___x_294_, 1, v_ref_288_);
                leanh::lean_ctor_set(v___x_294_, 2, v___x_293_);
                leanh::lean_ctor_set(v___x_294_, 3, v_descr_291_);
                leanh::lean_ctor_set(v___x_294_, 4, v_deprecation_x3f_292_);
                v___x_295_ = lean_register_option(v_name_286_, v___x_294_);
                if leanh::lean_obj_tag(v___x_295_) == 0 {
                    v_isSharedCheck_303_ = (!leanh::lean_is_exclusive(v___x_295_)) as u8;
                    if v_isSharedCheck_303_ == 0 {
                        v_unused_304_ = leanh::lean_ctor_get(v___x_295_, 0);
                        leanh::lean_dec(v_unused_304_);
                        v___x_297_ = v___x_295_;
                        v_isShared_298_ = v_isSharedCheck_303_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_295_);
                        v___x_297_ = leanh::lean_box(0);
                        v_isShared_298_ = v_isSharedCheck_303_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_286_);
                    v_a_305_ = leanh::lean_ctor_get(v___x_295_, 0);
                    v_isSharedCheck_312_ = (!leanh::lean_is_exclusive(v___x_295_)) as u8;
                    if v_isSharedCheck_312_ == 0 {
                        v___x_307_ = v___x_295_;
                        v_isShared_308_ = v_isSharedCheck_312_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_305_);
                        leanh::lean_dec(v___x_295_);
                        v___x_307_ = leanh::lean_box(0);
                        v_isShared_308_ = v_isSharedCheck_312_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_290_);
                v___x_299_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_299_, 0, v_name_286_);
                leanh::lean_ctor_set(v___x_299_, 1, v_defValue_290_);
                if v_isShared_298_ == 0 {
                    leanh::lean_ctor_set(v___x_297_, 0, v___x_299_);
                    v___x_301_ = v___x_297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_301_;
            }
            3 => {
                if v_isShared_308_ == 0 {
                    v___x_310_ = v___x_307_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
                    v___x_310_ = v_reuseFailAlloc_311_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_313_: *mut leanh::LeanObject,
    mut v_decl_314_: *mut leanh::LeanObject,
    mut v_ref_315_: *mut leanh::LeanObject,
    mut v_a_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(v_name_313_, v_decl_314_, v_ref_315_);
    leanh::lean_dec_ref(v_decl_314_);
    return v_res_317_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_;
    v___x_339_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_;
    v___x_340_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_;
    v___x_341_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(v___x_338_, v___x_339_, v___x_340_);
    return v___x_341_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4____boxed(
    mut v_a_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_();
    return v_res_343_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_;
    v___x_361_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_;
    v___x_362_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_;
    v___x_363_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(v___x_360_, v___x_361_, v___x_362_);
    return v___x_363_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4____boxed(
    mut v_a_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_365_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_();
    return v_res_365_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_;
    v___x_383_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_;
    v___x_384_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_;
    v___x_385_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(v___x_382_, v___x_383_, v___x_384_);
    return v___x_385_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4____boxed(
    mut v_a_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_();
    return v_res_387_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0(
    mut v_name_388_: *mut leanh::LeanObject,
    mut v_decl_389_: *mut leanh::LeanObject,
    mut v_ref_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v_unused_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_411_: u8 = 0;
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_392_ = leanh::lean_ctor_get(v_decl_389_, 0);
                v_descr_393_ = leanh::lean_ctor_get(v_decl_389_, 1);
                v_deprecation_x3f_394_ = leanh::lean_ctor_get(v_decl_389_, 2);
                v___x_395_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_396_ = (leanh::lean_unbox(v_defValue_392_) as u8);
                leanh::lean_ctor_set_uint8(v___x_395_, 0 as u32, v___x_396_);
                leanh::lean_inc(v_deprecation_x3f_394_);
                leanh::lean_inc_ref(v_descr_393_);
                leanh::lean_inc_n(v_name_388_, 2);
                v___x_397_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_397_, 0, v_name_388_);
                leanh::lean_ctor_set(v___x_397_, 1, v_ref_390_);
                leanh::lean_ctor_set(v___x_397_, 2, v___x_395_);
                leanh::lean_ctor_set(v___x_397_, 3, v_descr_393_);
                leanh::lean_ctor_set(v___x_397_, 4, v_deprecation_x3f_394_);
                v___x_398_ = lean_register_option(v_name_388_, v___x_397_);
                if leanh::lean_obj_tag(v___x_398_) == 0 {
                    v_isSharedCheck_406_ = (!leanh::lean_is_exclusive(v___x_398_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v_unused_407_ = leanh::lean_ctor_get(v___x_398_, 0);
                        leanh::lean_dec(v_unused_407_);
                        v___x_400_ = v___x_398_;
                        v_isShared_401_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_398_);
                        v___x_400_ = leanh::lean_box(0);
                        v_isShared_401_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_388_);
                    v_a_408_ = leanh::lean_ctor_get(v___x_398_, 0);
                    v_isSharedCheck_415_ = (!leanh::lean_is_exclusive(v___x_398_)) as u8;
                    if v_isSharedCheck_415_ == 0 {
                        v___x_410_ = v___x_398_;
                        v_isShared_411_ = v_isSharedCheck_415_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_408_);
                        leanh::lean_dec(v___x_398_);
                        v___x_410_ = leanh::lean_box(0);
                        v_isShared_411_ = v_isSharedCheck_415_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_392_);
                v___x_402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_402_, 0, v_name_388_);
                leanh::lean_ctor_set(v___x_402_, 1, v_defValue_392_);
                if v_isShared_401_ == 0 {
                    leanh::lean_ctor_set(v___x_400_, 0, v___x_402_);
                    v___x_404_ = v___x_400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
                    v___x_404_ = v_reuseFailAlloc_405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_404_;
            }
            3 => {
                if v_isShared_411_ == 0 {
                    v___x_413_ = v___x_410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
                    v___x_413_ = v_reuseFailAlloc_414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_416_: *mut leanh::LeanObject,
    mut v_decl_417_: *mut leanh::LeanObject,
    mut v_ref_418_: *mut leanh::LeanObject,
    mut v_a_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0(v_name_416_, v_decl_417_, v_ref_418_);
    leanh::lean_dec_ref(v_decl_417_);
    return v_res_420_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_;
    v___x_439_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_;
    v___x_440_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_;
    v___x_441_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0(v___x_438_, v___x_439_, v___x_440_);
    return v___x_441_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4____boxed(
    mut v_a_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_();
    return v_res_443_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_461_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_;
    v___x_462_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_;
    v___x_463_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_;
    v___x_464_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0(v___x_461_, v___x_462_, v___x_463_);
    return v___x_464_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4____boxed(
    mut v_a_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_466_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_();
    return v_res_466_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_;
    v___x_484_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_;
    v___x_485_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_;
    v___x_486_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4__spec__0(v___x_483_, v___x_484_, v___x_485_);
    return v___x_486_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4____boxed(
    mut v_a_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_488_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_();
    return v_res_488_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_;
    v___x_507_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_;
    v___x_508_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_;
    v___x_509_ = l_Lean_Option_register___at___00__private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4__spec__0(v___x_506_, v___x_507_, v___x_508_);
    return v___x_509_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4____boxed(
    mut v_a_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_511_ = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_();
    return v_res_511_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
    mut v_opts_512_: *mut leanh::LeanObject,
    mut v_opt_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_514_ = leanh::lean_ctor_get(v_opt_513_, 0);
    v_defValue_515_ = leanh::lean_ctor_get(v_opt_513_, 1);
    v_map_516_ = leanh::lean_ctor_get(v_opts_512_, 0);
    v___x_517_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_516_,
            v_name_514_,
        );
    if leanh::lean_obj_tag(v___x_517_) == 0 {
        leanh::lean_inc(v_defValue_515_);
        return v_defValue_515_;
    } else {
        let mut v_val_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_518_ = leanh::lean_ctor_get(v___x_517_, 0);
        leanh::lean_inc(v_val_518_);
        leanh::lean_dec_ref_known(v___x_517_, 1);
        if leanh::lean_obj_tag(v_val_518_) == 3 {
            let mut v_v_519_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_519_ = leanh::lean_ctor_get(v_val_518_, 0);
            leanh::lean_inc(v_v_519_);
            leanh::lean_dec_ref_known(v_val_518_, 1);
            return v_v_519_;
        } else {
            leanh::lean_dec(v_val_518_);
            leanh::lean_inc(v_defValue_515_);
            return v_defValue_515_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0___boxed(
    mut v_opts_520_: *mut leanh::LeanObject,
    mut v_opt_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_522_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
        v_opts_520_,
        v_opt_521_,
    );
    leanh::lean_dec_ref(v_opt_521_);
    leanh::lean_dec_ref(v_opts_520_);
    return v_res_522_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1(
    mut v_opts_523_: *mut leanh::LeanObject,
    mut v_opt_524_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_525_ = leanh::lean_ctor_get(v_opt_524_, 0);
    v_defValue_526_ = leanh::lean_ctor_get(v_opt_524_, 1);
    v_map_527_ = leanh::lean_ctor_get(v_opts_523_, 0);
    v___x_528_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_527_,
            v_name_525_,
        );
    if leanh::lean_obj_tag(v___x_528_) == 0 {
        let mut v___x_529_: u8 = 0;
        v___x_529_ = (leanh::lean_unbox(v_defValue_526_) as u8);
        return v___x_529_;
    } else {
        let mut v_val_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_530_ = leanh::lean_ctor_get(v___x_528_, 0);
        leanh::lean_inc(v_val_530_);
        leanh::lean_dec_ref_known(v___x_528_, 1);
        if leanh::lean_obj_tag(v_val_530_) == 1 {
            let mut v_v_531_: u8 = 0;
            v_v_531_ = leanh::lean_ctor_get_uint8(v_val_530_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_530_, 0);
            return v_v_531_;
        } else {
            let mut v___x_532_: u8 = 0;
            leanh::lean_dec(v_val_530_);
            v___x_532_ = (leanh::lean_unbox(v_defValue_526_) as u8);
            return v___x_532_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1___boxed(
    mut v_opts_533_: *mut leanh::LeanObject,
    mut v_opt_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_535_: u8 = 0;
    let mut v_r_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1(
        v_opts_533_,
        v_opt_534_,
    );
    leanh::lean_dec_ref(v_opt_534_);
    leanh::lean_dec_ref(v_opts_533_);
    v_r_536_ = leanh::lean_box((v_res_535_) as usize);
    return v_r_536_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toConfigOptions(
    mut v_opts_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lean_Compiler_LCNF_compiler_small;
    v___x_539_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
        v_opts_537_,
        v___x_538_,
    );
    v___x_540_ = l_Lean_Compiler_LCNF_compiler_maxRecInline;
    v___x_541_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
        v_opts_537_,
        v___x_540_,
    );
    v___x_542_ = l_Lean_Compiler_LCNF_compiler_maxRecInlineIfReduce;
    v___x_543_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
        v_opts_537_,
        v___x_542_,
    );
    v___x_544_ = l_Lean_Compiler_LCNF_compiler_checkTypes;
    v___x_545_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1(
        v_opts_537_,
        v___x_544_,
    );
    v___x_546_ = l_Lean_Compiler_LCNF_compiler_extract__closed;
    v___x_547_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1(
        v_opts_537_,
        v___x_546_,
    );
    v___x_548_ = l_Lean_Compiler_LCNF_compiler_maxRecSpecialize;
    v___x_549_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__0(
        v_opts_537_,
        v___x_548_,
    );
    v___x_550_ = l_Lean_Compiler_LCNF_compiler_reuse;
    v___x_551_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toConfigOptions_spec__1(
        v_opts_537_,
        v___x_550_,
    );
    v___x_552_ = leanh::lean_alloc_ctor(0, 4, (3) as u32);
    leanh::lean_ctor_set(v___x_552_, 0, v___x_539_);
    leanh::lean_ctor_set(v___x_552_, 1, v___x_541_);
    leanh::lean_ctor_set(v___x_552_, 2, v___x_543_);
    leanh::lean_ctor_set(v___x_552_, 3, v___x_549_);
    leanh::lean_ctor_set_uint8(
        v___x_552_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_545_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_552_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_547_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_552_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 2) as u32,
        v___x_551_,
    );
    return v___x_552_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toConfigOptions___boxed(
    mut v_opts_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Lean_Compiler_LCNF_toConfigOptions(v_opts_553_);
    leanh::lean_dec_ref(v_opts_553_);
    return v_res_554_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2418604597____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_small = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_small);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_966831148____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_maxRecInline = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_maxRecInline);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2649851602____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_maxRecInlineIfReduce =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_maxRecInlineIfReduce);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_1257955899____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_checkTypes = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_checkTypes);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_840336701____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_extract__closed = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_extract__closed);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_2867675980____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_maxRecSpecialize = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_maxRecSpecialize);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ConfigOptions_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ConfigOptions_583794373____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_compiler_reuse = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_compiler_reuse);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ConfigOptions(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ConfigOptions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
}