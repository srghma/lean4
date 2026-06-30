// Lean compiler output
// Module: Lean.DeprecatedModule
// Imports: Lean.Compiler.ModPkgExt
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_name_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_append, lean_usize_add, lean_usize_dec_eq,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Compiler::ModPkgExt::{
    initialize_Lean_Compiler_ModPkgExt, l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg,
    l_Lean_registerModuleEnvExtension___redArg, runtime_initialize_Lean_Compiler_ModPkgExt,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_header, l_Lean_PersistentEnvExtension_setState___redArg,
    l_Lean_instInhabitedModuleData_default,
};
pub static l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedDeprecatedModuleEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedDeprecatedModuleEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5701751079888345786 as *mut leanh::LeanObject] };
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13546154976408593379 as *mut leanh::LeanObject] };
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6940304854702209343 as *mut leanh::LeanObject] };
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanStringObject<61> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [105, 102, 32, 116, 114, 117, 101, 44, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 119, 97, 114, 110, 105, 110, 103, 115, 32, 119, 104, 101, 110, 32, 105, 109, 112, 111, 114, 116, 105, 110, 103, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 115, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,2225194685056464603 as *mut leanh::LeanObject] };
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,18325004576448962094 as *mut leanh::LeanObject] };
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,9886691069155331686 as *mut leanh::LeanObject] };
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_linter_deprecated_module: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 77, 111, 100, 117, 108, 101, 69, 120, 116, 0]};
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14236438790327215984 as *mut leanh::LeanObject] };
static mut l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_deprecatedModuleExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 105, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value) as *mut leanh::LeanObject,1882184448842950296 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_formatDeprecatedModuleWarning___closed__0_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [10, 39, 0],
};
static mut l_Lean_formatDeprecatedModuleWarning___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatDeprecatedModuleWarning___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_formatDeprecatedModuleWarning___closed__1_value: leanh::LeanStringObject<
    55,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        39, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101,
        100, 58, 32, 112, 108, 101, 97, 115, 101, 32, 114, 101, 112, 108, 97, 99, 101, 32, 116,
        104, 105, 115, 32, 105, 109, 112, 111, 114, 116, 32, 98, 121, 10, 10, 0,
    ],
};
static mut l_Lean_formatDeprecatedModuleWarning___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatDeprecatedModuleWarning___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_formatDeprecatedModuleWarning___closed__2_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
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
static mut l_Lean_formatDeprecatedModuleWarning___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatDeprecatedModuleWarning___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_formatDeprecatedModuleWarning___closed__3_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_formatDeprecatedModuleWarning___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_formatDeprecatedModuleWarning___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(
    mut v_name_210_: *mut leanh::LeanObject,
    mut v_decl_211_: *mut leanh::LeanObject,
    mut v_ref_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_223_: u8 = 0;
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_228_: u8 = 0;
    let mut v_unused_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_214_ = leanh::lean_ctor_get(v_decl_211_, 0);
                v_descr_215_ = leanh::lean_ctor_get(v_decl_211_, 1);
                v_deprecation_x3f_216_ = leanh::lean_ctor_get(v_decl_211_, 2);
                v___x_217_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_218_ = (leanh::lean_unbox(v_defValue_214_) as u8);
                leanh::lean_ctor_set_uint8(v___x_217_, 0 as u32, v___x_218_);
                leanh::lean_inc(v_deprecation_x3f_216_);
                leanh::lean_inc_ref(v_descr_215_);
                leanh::lean_inc_n(v_name_210_, 2);
                v___x_219_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_219_, 0, v_name_210_);
                leanh::lean_ctor_set(v___x_219_, 1, v_ref_212_);
                leanh::lean_ctor_set(v___x_219_, 2, v___x_217_);
                leanh::lean_ctor_set(v___x_219_, 3, v_descr_215_);
                leanh::lean_ctor_set(v___x_219_, 4, v_deprecation_x3f_216_);
                v___x_220_ = lean_register_option(v_name_210_, v___x_219_);
                if leanh::lean_obj_tag(v___x_220_) == 0 {
                    v_isSharedCheck_228_ = (!leanh::lean_is_exclusive(v___x_220_)) as u8;
                    if v_isSharedCheck_228_ == 0 {
                        v_unused_229_ = leanh::lean_ctor_get(v___x_220_, 0);
                        leanh::lean_dec(v_unused_229_);
                        v___x_222_ = v___x_220_;
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_220_);
                        v___x_222_ = leanh::lean_box(0);
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_210_);
                    v_a_230_ = leanh::lean_ctor_get(v___x_220_, 0);
                    v_isSharedCheck_237_ = (!leanh::lean_is_exclusive(v___x_220_)) as u8;
                    if v_isSharedCheck_237_ == 0 {
                        v___x_232_ = v___x_220_;
                        v_isShared_233_ = v_isSharedCheck_237_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_230_);
                        leanh::lean_dec(v___x_220_);
                        v___x_232_ = leanh::lean_box(0);
                        v_isShared_233_ = v_isSharedCheck_237_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_214_);
                v___x_224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_224_, 0, v_name_210_);
                leanh::lean_ctor_set(v___x_224_, 1, v_defValue_214_);
                if v_isShared_223_ == 0 {
                    leanh::lean_ctor_set(v___x_222_, 0, v___x_224_);
                    v___x_226_ = v___x_222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
                    v___x_226_ = v_reuseFailAlloc_227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_226_;
            }
            3 => {
                if v_isShared_233_ == 0 {
                    v___x_235_ = v___x_232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
                    v___x_235_ = v_reuseFailAlloc_236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_238_: *mut leanh::LeanObject,
    mut v_decl_239_: *mut leanh::LeanObject,
    mut v_ref_240_: *mut leanh::LeanObject,
    mut v_a_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v_name_238_, v_decl_239_, v_ref_240_);
    leanh::lean_dec_ref(v_decl_239_);
    return v_res_242_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_;
    v___x_264_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_;
    v___x_265_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_;
    v___x_266_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v___x_263_, v___x_264_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4____boxed(
    mut v_a_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
    return v_res_268_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(
    mut v___x_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_271_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_271_, 0, v___x_269_);
    return v___x_271_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(
    mut v___x_272_: *mut leanh::LeanObject,
    mut v___y_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(v___x_272_);
    return v_res_274_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_282_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_;
    v___x_283_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_;
    v___x_284_ = l_Lean_registerModuleEnvExtension___redArg(v___f_282_, v___x_283_);
    return v___x_284_;
}
pub unsafe fn l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(
    mut v_a_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
    return v_res_286_;
}
pub unsafe fn l_Lean_Environment_getDeprecatedModuleByIdx_x3f(
    mut v_env_287_: *mut leanh::LeanObject,
    mut v_idx_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = leanh::lean_box(0);
    v___x_290_ = l_Lean_deprecatedModuleExt;
    v___x_291_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(
        v___x_289_, v___x_290_, v_env_287_, v_idx_288_,
    );
    if leanh::lean_obj_tag(v___x_291_) == 0 {
        return v___x_289_;
    } else {
        let mut v_val_292_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_292_ = leanh::lean_ctor_get(v___x_291_, 0);
        leanh::lean_inc(v_val_292_);
        leanh::lean_dec_ref_known(v___x_291_, 1);
        return v_val_292_;
    }
}
pub unsafe fn l_Lean_Environment_getDeprecatedModuleByIdx_x3f___boxed(
    mut v_env_293_: *mut leanh::LeanObject,
    mut v_idx_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_293_, v_idx_294_);
    leanh::lean_dec(v_idx_294_);
    leanh::lean_dec_ref(v_env_293_);
    return v_res_295_;
}
pub unsafe fn l_Lean_Environment_setDeprecatedModule(
    mut v_entry_296_: *mut leanh::LeanObject,
    mut v_env_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Lean_deprecatedModuleExt;
    v___x_299_ =
        l_Lean_PersistentEnvExtension_setState___redArg(v___x_298_, v_env_297_, v_entry_296_);
    return v___x_299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(
    mut v_as_302_: *mut leanh::LeanObject,
    mut v_i_303_: usize,
    mut v_stop_304_: usize,
    mut v_b_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_306_: u8 = 0;
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: u8 = 0;
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: usize = 0;
    let mut v___x_317_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_306_ = lean_usize_dec_eq(v_i_303_, v_stop_304_);
                if v___x_306_ == 0 {
                    v___x_307_ = lean_array_uget_borrowed(v_as_302_, v_i_303_);
                    v_module_308_ = leanh::lean_ctor_get(v___x_307_, 0);
                    v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0;
                    v___x_310_ = 1;
                    leanh::lean_inc(v_module_308_);
                    v___x_311_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_308_,
                        v___x_310_,
                    );
                    v___x_312_ = lean_string_append(v___x_309_, v___x_311_);
                    leanh::lean_dec_ref(v___x_311_);
                    v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1;
                    v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
                    v___x_315_ = lean_string_append(v_b_305_, v___x_314_);
                    leanh::lean_dec_ref(v___x_314_);
                    v___x_316_ = 1usize;
                    v___x_317_ = lean_usize_add(v_i_303_, v___x_316_);
                    v_i_303_ = v___x_317_;
                    v_b_305_ = v___x_315_;
                    state = 0;
                    continue;
                } else {
                    return v_b_305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___boxed(
    mut v_as_319_: *mut leanh::LeanObject,
    mut v_i_320_: *mut leanh::LeanObject,
    mut v_stop_321_: *mut leanh::LeanObject,
    mut v_b_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_323_: usize = 0;
    let mut v_stop_boxed_324_: usize = 0;
    let mut v_res_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_323_ = leanh::lean_unbox_usize(v_i_320_);
    leanh::lean_dec(v_i_320_);
    v_stop_boxed_324_ = leanh::lean_unbox_usize(v_stop_321_);
    leanh::lean_dec(v_stop_321_);
    v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v_as_319_, v_i_boxed_323_, v_stop_boxed_324_, v_b_322_);
    leanh::lean_dec_ref(v_as_319_);
    return v_res_325_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(
    mut v_as_329_: *mut leanh::LeanObject,
    mut v_i_330_: usize,
    mut v_stop_331_: usize,
    mut v_b_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: usize = 0;
    let mut v___x_336_: usize = 0;
    let mut v___x_338_: u8 = 0;
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: u8 = 0;
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_338_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
                if v___x_338_ == 0 {
                    v___x_339_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
                    v_module_340_ = leanh::lean_ctor_get(v___x_339_, 0);
                    v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1;
                    v___x_342_ = lean_name_eq(v_module_340_, v___x_341_);
                    if v___x_342_ == 0 {
                        leanh::lean_inc(v___x_339_);
                        v___x_343_ = lean_array_push(v_b_332_, v___x_339_);
                        v___y_334_ = v___x_343_;
                        state = 1;
                        continue;
                    } else {
                        v___y_334_ = v_b_332_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_332_;
                }
            }
            1 => {
                v___x_335_ = 1usize;
                v___x_336_ = lean_usize_add(v_i_330_, v___x_335_);
                v_i_330_ = v___x_336_;
                v_b_332_ = v___y_334_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___boxed(
    mut v_as_344_: *mut leanh::LeanObject,
    mut v_i_345_: *mut leanh::LeanObject,
    mut v_stop_346_: *mut leanh::LeanObject,
    mut v_b_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_348_: usize = 0;
    let mut v_stop_boxed_349_: usize = 0;
    let mut v_res_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_348_ = leanh::lean_unbox_usize(v_i_345_);
    leanh::lean_dec(v_i_345_);
    v_stop_boxed_349_ = leanh::lean_unbox_usize(v_stop_346_);
    leanh::lean_dec(v_stop_346_);
    v_res_350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_as_344_, v_i_boxed_348_, v_stop_boxed_349_, v_b_347_);
    leanh::lean_dec_ref(v_as_344_);
    return v_res_350_;
}
pub unsafe fn l_Lean_formatDeprecatedModuleWarning(
    mut v_env_356_: *mut leanh::LeanObject,
    mut v_idx_357_: *mut leanh::LeanObject,
    mut v_modName_358_: *mut leanh::LeanObject,
    mut v_entry_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: u8 = 0;
    let mut v___x_378_: u8 = 0;
    let mut v___x_379_: usize = 0;
    let mut v___x_380_: usize = 0;
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: usize = 0;
    let mut v___x_383_: usize = 0;
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_x3f_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleData_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    let mut v___x_397_: u8 = 0;
    let mut v___x_398_: usize = 0;
    let mut v___x_399_: usize = 0;
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: usize = 0;
    let mut v___x_402_: usize = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_message_x3f_385_ = leanh::lean_ctor_get(v_entry_359_, 0);
                leanh::lean_inc(v_message_x3f_385_);
                leanh::lean_dec_ref(v_entry_359_);
                v___x_386_ = l_Lean_instInhabitedModuleData_default;
                if leanh::lean_obj_tag(v_message_x3f_385_) == 0 {
                    v___x_404_ = l_Lean_formatDeprecatedModuleWarning___closed__2;
                    v___y_388_ = v___x_404_;
                    state = 3;
                    continue;
                } else {
                    v_val_405_ = leanh::lean_ctor_get(v_message_x3f_385_, 0);
                    leanh::lean_inc(v_val_405_);
                    leanh::lean_dec_ref_known(v_message_x3f_385_, 1);
                    v___y_388_ = v_val_405_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_363_ = l_Lean_formatDeprecatedModuleWarning___closed__0;
                v___x_364_ = lean_string_append(v___y_361_, v___x_363_);
                v___x_365_ = 1;
                v___x_366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_modName_358_,
                    v___x_365_,
                );
                v___x_367_ = lean_string_append(v___x_364_, v___x_366_);
                leanh::lean_dec_ref(v___x_366_);
                v___x_368_ = l_Lean_formatDeprecatedModuleWarning___closed__1;
                v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
                v___x_370_ = lean_string_append(v___x_369_, v___y_362_);
                leanh::lean_dec_ref(v___y_362_);
                return v___x_370_;
            }
            2 => {
                v___x_375_ = l_Lean_formatDeprecatedModuleWarning___closed__2;
                v___x_376_ = lean_array_get_size(v___y_374_);
                v___x_377_ = lean_nat_dec_lt(v___y_372_, v___x_376_);
                if v___x_377_ == 0 {
                    leanh::lean_dec_ref(v___y_374_);
                    v___y_361_ = v___y_373_;
                    v___y_362_ = v___x_375_;
                    state = 1;
                    continue;
                } else {
                    v___x_378_ = lean_nat_dec_le(v___x_376_, v___x_376_);
                    if v___x_378_ == 0 {
                        if v___x_377_ == 0 {
                            leanh::lean_dec_ref(v___y_374_);
                            v___y_361_ = v___y_373_;
                            v___y_362_ = v___x_375_;
                            state = 1;
                            continue;
                        } else {
                            v___x_379_ = 0usize;
                            v___x_380_ = lean_usize_of_nat(v___x_376_);
                            v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_374_, v___x_379_, v___x_380_, v___x_375_);
                            leanh::lean_dec_ref(v___y_374_);
                            v___y_361_ = v___y_373_;
                            v___y_362_ = v___x_381_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_382_ = 0usize;
                        v___x_383_ = lean_usize_of_nat(v___x_376_);
                        v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_374_, v___x_382_, v___x_383_, v___x_375_);
                        leanh::lean_dec_ref(v___y_374_);
                        v___y_361_ = v___y_373_;
                        v___y_362_ = v___x_384_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_389_ = l_Lean_Environment_header(v_env_356_);
                v_moduleData_390_ = leanh::lean_ctor_get(v___x_389_, 6);
                leanh::lean_inc_ref(v_moduleData_390_);
                leanh::lean_dec_ref(v___x_389_);
                v___x_391_ = lean_array_get(v___x_386_, v_moduleData_390_, v_idx_357_);
                leanh::lean_dec_ref(v_moduleData_390_);
                v_imports_392_ = leanh::lean_ctor_get(v___x_391_, 0);
                leanh::lean_inc_ref(v_imports_392_);
                leanh::lean_dec(v___x_391_);
                v___x_393_ = leanh::lean_unsigned_to_nat(0);
                v___x_394_ = lean_array_get_size(v_imports_392_);
                v___x_395_ = l_Lean_formatDeprecatedModuleWarning___closed__3;
                v___x_396_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
                if v___x_396_ == 0 {
                    leanh::lean_dec_ref(v_imports_392_);
                    v___y_372_ = v___x_393_;
                    v___y_373_ = v___y_388_;
                    v___y_374_ = v___x_395_;
                    state = 2;
                    continue;
                } else {
                    v___x_397_ = lean_nat_dec_le(v___x_394_, v___x_394_);
                    if v___x_397_ == 0 {
                        if v___x_396_ == 0 {
                            leanh::lean_dec_ref(v_imports_392_);
                            v___y_372_ = v___x_393_;
                            v___y_373_ = v___y_388_;
                            v___y_374_ = v___x_395_;
                            state = 2;
                            continue;
                        } else {
                            v___x_398_ = 0usize;
                            v___x_399_ = lean_usize_of_nat(v___x_394_);
                            v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_392_, v___x_398_, v___x_399_, v___x_395_);
                            leanh::lean_dec_ref(v_imports_392_);
                            v___y_372_ = v___x_393_;
                            v___y_373_ = v___y_388_;
                            v___y_374_ = v___x_400_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_401_ = 0usize;
                        v___x_402_ = lean_usize_of_nat(v___x_394_);
                        v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_392_, v___x_401_, v___x_402_, v___x_395_);
                        leanh::lean_dec_ref(v_imports_392_);
                        v___y_372_ = v___x_393_;
                        v___y_373_ = v___y_388_;
                        v___y_374_ = v___x_403_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_formatDeprecatedModuleWarning___boxed(
    mut v_env_406_: *mut leanh::LeanObject,
    mut v_idx_407_: *mut leanh::LeanObject,
    mut v_modName_408_: *mut leanh::LeanObject,
    mut v_entry_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_410_ =
        l_Lean_formatDeprecatedModuleWarning(v_env_406_, v_idx_407_, v_modName_408_, v_entry_409_);
    leanh::lean_dec(v_idx_407_);
    leanh::lean_dec_ref(v_env_406_);
    return v_res_410_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DeprecatedModule(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_linter_deprecated_module = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_linter_deprecated_module);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_deprecatedModuleExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_deprecatedModuleExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DeprecatedModule(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DeprecatedModule(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ModPkgExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeprecatedModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DeprecatedModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DeprecatedModule(builtin);
}