// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.Format Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.Checker Lean.Compiler.IR.UnboxResult Lean.Compiler.IR.Sorry Lean.Compiler.IR.ToIR Lean.Compiler.IR.ToIRType Lean.Compiler.IR.Meta Lean.Compiler.IR.LLVMBindings Lean.Compiler.IR.EmitLLVM
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::IR::Basic::{
    initialize_Lean_Compiler_IR_Basic, runtime_initialize_Lean_Compiler_IR_Basic,
};
use crate::r#gen::Lean::Compiler::IR::Checker::{
    initialize_Lean_Compiler_IR_Checker, l_Lean_IR_checkDecls,
    runtime_initialize_Lean_Compiler_IR_Checker,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM,
    l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux, l_Lean_IR_addDecls,
    l_Lean_IR_tracePrefixOptionName, runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::IR::EmitLLVM::{
    initialize_Lean_Compiler_IR_EmitLLVM, runtime_initialize_Lean_Compiler_IR_EmitLLVM,
};
use crate::r#gen::Lean::Compiler::IR::Format::{
    initialize_Lean_Compiler_IR_Format, runtime_initialize_Lean_Compiler_IR_Format,
};
use crate::r#gen::Lean::Compiler::IR::LLVMBindings::{
    initialize_Lean_Compiler_IR_LLVMBindings, runtime_initialize_Lean_Compiler_IR_LLVMBindings,
};
use crate::r#gen::Lean::Compiler::IR::Meta::{
    initialize_Lean_Compiler_IR_Meta, l_Lean_IR_inferMeta, runtime_initialize_Lean_Compiler_IR_Meta,
};
use crate::r#gen::Lean::Compiler::IR::NormIds::{
    initialize_Lean_Compiler_IR_NormIds, runtime_initialize_Lean_Compiler_IR_NormIds,
};
use crate::r#gen::Lean::Compiler::IR::Sorry::{
    initialize_Lean_Compiler_IR_Sorry, l_Lean_IR_updateSorryDep,
    runtime_initialize_Lean_Compiler_IR_Sorry,
};
use crate::r#gen::Lean::Compiler::IR::ToIR::{
    initialize_Lean_Compiler_IR_ToIR, runtime_initialize_Lean_Compiler_IR_ToIR,
};
use crate::r#gen::Lean::Compiler::IR::ToIRType::{
    initialize_Lean_Compiler_IR_ToIRType, runtime_initialize_Lean_Compiler_IR_ToIRType,
};
use crate::r#gen::Lean::Compiler::IR::UnboxResult::{
    initialize_Lean_Compiler_IR_UnboxResult, runtime_initialize_Lean_Compiler_IR_UnboxResult,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
};
pub static l_Lean_IR_compile___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 110, 105, 116, 0],
};
static mut l_Lean_IR_compile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_compile___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_compile___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_IR_compile___closed__0_value) as *mut LeanObject,
        15209775132330820936 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_compile___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_compile___closed__1_value) as *mut LeanObject;
static mut l_Lean_IR_compile___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_compile___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_compile___closed__3_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 115, 117, 108, 116, 0],
};
static mut l_Lean_IR_compile___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_compile___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_compile___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_IR_compile___closed__3_value) as *mut LeanObject,
        5998540102806111156 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_compile___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_compile___closed__4_value) as *mut LeanObject;
static mut l_Lean_IR_compile___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_compile___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 114, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,7476836525069983911 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [73, 82, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,5089948989189718287 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2334764735333895074 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,11317296629602541699 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,5601417139861915576 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,14645199714203030773 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,16072918902492008456 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,10845145278414702049 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,6707275784260296079 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,14482848446190948964 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,((( 640659120 as usize) << 1) | 1) as *mut LeanObject,11683398585659696357 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,12149887226112169654 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,1626452768174561418 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,15637900355009296435 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,7476836525069983911 as *mut LeanObject] };
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_IR_compile___closed__0_value) as *mut LeanObject,614658974476769860 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject,7476836525069983911 as *mut LeanObject] };
pub static l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_IR_compile___closed__3_value) as *mut LeanObject,912455677897450840 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_IR_compile___closed__2() -> *mut LeanObject {
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_165_ = l_Lean_IR_compile___closed__1;
    v___x_166_ = l_Lean_IR_tracePrefixOptionName;
    v___x_167_ = l_Lean_Name_append(v___x_166_, v___x_165_);
    return v___x_167_;
}
pub unsafe fn _init_l_Lean_IR_compile___closed__5() -> *mut LeanObject {
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v___x_171_ = l_Lean_IR_compile___closed__4;
    v___x_172_ = l_Lean_IR_tracePrefixOptionName;
    v___x_173_ = l_Lean_Name_append(v___x_172_, v___x_171_);
    return v___x_173_;
}
pub unsafe fn l_Lean_IR_compile(
    mut v_decls_174_: *mut LeanObject,
    mut v_a_175_: *mut LeanObject,
    mut v_a_176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_191_: u8 = 0;
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_195_: u8 = 0;
    let mut v_unused_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut v_a_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_208_: u8 = 0;
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut v_a_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_216_: u8 = 0;
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_220_: u8 = 0;
    let mut v_a_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_224_: u8 = 0;
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_228_: u8 = 0;
    let mut v_a_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_232_: u8 = 0;
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_178_ = l_Lean_IR_compile___closed__1;
                v___x_179_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_compile___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_IR_compile___closed__2_once),
                    _init_l_Lean_IR_compile___closed__2,
                );
                lean_inc_ref(v_decls_174_);
                v___x_180_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(
                    v___x_179_,
                    v___x_178_,
                    v_decls_174_,
                    v_a_175_,
                    v_a_176_,
                );
                if lean_obj_tag(v___x_180_) == 0 {
                    lean_dec_ref_known(v___x_180_, 1);
                    lean_inc_ref(v_decls_174_);
                    v___x_181_ = l_Lean_IR_checkDecls(v_decls_174_, v_a_175_, v_a_176_);
                    if lean_obj_tag(v___x_181_) == 0 {
                        lean_dec_ref_known(v___x_181_, 1);
                        v___x_182_ = l_Lean_IR_updateSorryDep(v_decls_174_, v_a_175_, v_a_176_);
                        if lean_obj_tag(v___x_182_) == 0 {
                            v_a_183_ = lean_ctor_get(v___x_182_, 0);
                            lean_inc_n(v_a_183_, 2);
                            lean_dec_ref_known(v___x_182_, 1);
                            v___x_184_ = l_Lean_IR_compile___closed__4;
                            v___x_185_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_IR_compile___closed__5),
                                core::ptr::addr_of_mut!(l_Lean_IR_compile___closed__5_once),
                                _init_l_Lean_IR_compile___closed__5,
                            );
                            v___x_186_ =
                                l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(
                                    v___x_185_, v___x_184_, v_a_183_, v_a_175_, v_a_176_,
                                );
                            if lean_obj_tag(v___x_186_) == 0 {
                                lean_dec_ref_known(v___x_186_, 1);
                                v___x_187_ = l_Lean_IR_addDecls(v_a_183_, v_a_175_, v_a_176_);
                                if lean_obj_tag(v___x_187_) == 0 {
                                    lean_dec_ref_known(v___x_187_, 1);
                                    v___x_188_ = l_Lean_IR_inferMeta(v_a_183_, v_a_175_, v_a_176_);
                                    if lean_obj_tag(v___x_188_) == 0 {
                                        v_isSharedCheck_195_ =
                                            (!lean_is_exclusive(v___x_188_)) as u8;
                                        if v_isSharedCheck_195_ == 0 {
                                            v_unused_196_ = lean_ctor_get(v___x_188_, 0);
                                            lean_dec(v_unused_196_);
                                            v___x_190_ = v___x_188_;
                                            v_isShared_191_ = v_isSharedCheck_195_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v___x_188_);
                                            v___x_190_ = lean_box(0);
                                            v_isShared_191_ = v_isSharedCheck_195_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_183_);
                                        v_a_197_ = lean_ctor_get(v___x_188_, 0);
                                        v_isSharedCheck_204_ =
                                            (!lean_is_exclusive(v___x_188_)) as u8;
                                        if v_isSharedCheck_204_ == 0 {
                                            v___x_199_ = v___x_188_;
                                            v_isShared_200_ = v_isSharedCheck_204_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_197_);
                                            lean_dec(v___x_188_);
                                            v___x_199_ = lean_box(0);
                                            v_isShared_200_ = v_isSharedCheck_204_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_183_);
                                    v_a_205_ = lean_ctor_get(v___x_187_, 0);
                                    v_isSharedCheck_212_ = (!lean_is_exclusive(v___x_187_)) as u8;
                                    if v_isSharedCheck_212_ == 0 {
                                        v___x_207_ = v___x_187_;
                                        v_isShared_208_ = v_isSharedCheck_212_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_205_);
                                        lean_dec(v___x_187_);
                                        v___x_207_ = lean_box(0);
                                        v_isShared_208_ = v_isSharedCheck_212_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_183_);
                                v_a_213_ = lean_ctor_get(v___x_186_, 0);
                                v_isSharedCheck_220_ = (!lean_is_exclusive(v___x_186_)) as u8;
                                if v_isSharedCheck_220_ == 0 {
                                    v___x_215_ = v___x_186_;
                                    v_isShared_216_ = v_isSharedCheck_220_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_213_);
                                    lean_dec(v___x_186_);
                                    v___x_215_ = lean_box(0);
                                    v_isShared_216_ = v_isSharedCheck_220_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_182_;
                        }
                    } else {
                        lean_dec_ref(v_decls_174_);
                        v_a_221_ = lean_ctor_get(v___x_181_, 0);
                        v_isSharedCheck_228_ = (!lean_is_exclusive(v___x_181_)) as u8;
                        if v_isSharedCheck_228_ == 0 {
                            v___x_223_ = v___x_181_;
                            v_isShared_224_ = v_isSharedCheck_228_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_221_);
                            lean_dec(v___x_181_);
                            v___x_223_ = lean_box(0);
                            v_isShared_224_ = v_isSharedCheck_228_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_decls_174_);
                    v_a_229_ = lean_ctor_get(v___x_180_, 0);
                    v_isSharedCheck_236_ = (!lean_is_exclusive(v___x_180_)) as u8;
                    if v_isSharedCheck_236_ == 0 {
                        v___x_231_ = v___x_180_;
                        v_isShared_232_ = v_isSharedCheck_236_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_229_);
                        lean_dec(v___x_180_);
                        v___x_231_ = lean_box(0);
                        v_isShared_232_ = v_isSharedCheck_236_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_191_ == 0 {
                    lean_ctor_set(v___x_190_, 0, v_a_183_);
                    v___x_193_ = v___x_190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_183_);
                    v___x_193_ = v_reuseFailAlloc_194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_193_;
            }
            3 => {
                if v_isShared_200_ == 0 {
                    v___x_202_ = v___x_199_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
                    v___x_202_ = v_reuseFailAlloc_203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_202_;
            }
            5 => {
                if v_isShared_208_ == 0 {
                    v___x_210_ = v___x_207_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
                    v___x_210_ = v_reuseFailAlloc_211_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_210_;
            }
            7 => {
                if v_isShared_216_ == 0 {
                    v___x_218_ = v___x_215_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
                    v___x_218_ = v_reuseFailAlloc_219_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_218_;
            }
            9 => {
                if v_isShared_224_ == 0 {
                    v___x_226_ = v___x_223_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
                    v___x_226_ = v_reuseFailAlloc_227_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_226_;
            }
            11 => {
                if v_isShared_232_ == 0 {
                    v___x_234_ = v___x_231_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
                    v___x_234_ = v_reuseFailAlloc_235_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_compile___boxed(
    mut v_decls_237_: *mut LeanObject,
    mut v_a_238_: *mut LeanObject,
    mut v_a_239_: *mut LeanObject,
    mut v_a_240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_241_: *mut LeanObject = core::ptr::null_mut();
    v_res_241_ = l_Lean_IR_compile(v_decls_237_, v_a_238_, v_a_239_);
    lean_dec(v_a_239_);
    lean_dec_ref(v_a_238_);
    return v_res_241_;
}
pub unsafe fn l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: u8 = 0;
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
    v___x_313_ = 0;
    v___x_314_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
    v___x_315_ = l_Lean_registerTraceClass(v___x_312_, v___x_313_, v___x_314_);
    if lean_obj_tag(v___x_315_) == 0 {
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_317_: u8 = 0;
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_315_, 1);
        v___x_316_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__27_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
        v___x_317_ = 1;
        v___x_318_ = l_Lean_registerTraceClass(v___x_316_, v___x_317_, v___x_314_);
        if lean_obj_tag(v___x_318_) == 0 {
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_318_, 1);
            v___x_319_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__28_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
            v___x_320_ = l_Lean_registerTraceClass(v___x_319_, v___x_317_, v___x_314_);
            return v___x_320_;
        } else {
            return v___x_318_;
        }
    } else {
        return v___x_315_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(
    mut v_a_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_322_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
    return v_res_322_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_NormIds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Checker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_UnboxResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_EmitLLVM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Compiler_IR_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_NormIds(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_Checker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_UnboxResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_ToIR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_ToIRType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_LLVMBindings(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_EmitLLVM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR(builtin);
}
