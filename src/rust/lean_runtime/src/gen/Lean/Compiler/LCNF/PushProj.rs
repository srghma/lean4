// Lean compiler output
// Module: Lean.Compiler.LCNF.PushProj
// Imports: Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Internalize
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Code_collectUsed, l_Lean_Compiler_LCNF_CodeDecl_collectUsed,
    l_Lean_Compiler_LCNF_attachCodeDecls, l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Decl_internalize,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_instInhabitedFVarIdHashSet,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_pushProj___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 117, 115, 104, 80, 114, 111, 106, 0],
    };
static mut l_Lean_Compiler_LCNF_pushProj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_pushProj___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value) as *mut LeanObject,
        4906690443001084389 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_pushProj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_pushProj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_pushProj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_pushProj___closed__0_value) as *mut LeanObject,6002029543643796387 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 117, 115, 104, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,1790360179806483262 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9410697049790244999 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,9338128937441115898 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,5262479513608925480 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,14794927585209949633 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,7175746045895695224 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,4801555735692583369 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,16516678141487640844 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,6161148531420215382 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,14462547702771714495 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,14594966017329367672 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,((( 1777867010 as usize) << 1) | 1) as *mut LeanObject,18309865256079098078 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,2769903573489266121 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,361694778570169441 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,14425366255458452540 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(
    mut v_alt_876_: *mut LeanObject,
    mut v_f_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
    mut v___y_879_: *mut LeanObject,
    mut v___y_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut v_a_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut v_code_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_alt_876_) {
                0 => {
                    v_code_903_ = lean_ctor_get(v_alt_876_, 2);
                    lean_inc_ref(v_code_903_);
                    v___y_884_ = v_code_903_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_code_904_ = lean_ctor_get(v_alt_876_, 1);
                    lean_inc_ref(v_code_904_);
                    v___y_884_ = v_code_904_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_code_905_ = lean_ctor_get(v_alt_876_, 0);
                    lean_inc_ref(v_code_905_);
                    v___y_884_ = v_code_905_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                lean_inc(v___y_881_);
                lean_inc_ref(v___y_880_);
                lean_inc(v___y_879_);
                lean_inc_ref(v___y_878_);
                v___x_885_ = lean_apply_6(
                    v_f_877_,
                    v___y_884_,
                    v___y_878_,
                    v___y_879_,
                    v___y_880_,
                    v___y_881_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_885_) == 0 {
                    v_a_886_ = lean_ctor_get(v___x_885_, 0);
                    v_isSharedCheck_894_ = (!lean_is_exclusive(v___x_885_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_888_ = v___x_885_;
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_886_);
                        lean_dec(v___x_885_);
                        v___x_888_ = lean_box(0);
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_alt_876_);
                    v_a_895_ = lean_ctor_get(v___x_885_, 0);
                    v_isSharedCheck_902_ = (!lean_is_exclusive(v___x_885_)) as u8;
                    if v_isSharedCheck_902_ == 0 {
                        v___x_897_ = v___x_885_;
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_895_);
                        lean_dec(v___x_885_);
                        v___x_897_ = lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_890_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_876_, v_a_886_);
                if v_isShared_889_ == 0 {
                    lean_ctor_set(v___x_888_, 0, v___x_890_);
                    v___x_892_ = v___x_888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
                    v___x_892_ = v_reuseFailAlloc_893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_892_;
            }
            4 => {
                if v_isShared_898_ == 0 {
                    v___x_900_ = v___x_897_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg___boxed(
    mut v_alt_906_: *mut LeanObject,
    mut v_f_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
    mut v___y_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_913_: *mut LeanObject = core::ptr::null_mut();
    v_res_913_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_906_, v_f_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
    lean_dec(v___y_911_);
    lean_dec_ref(v___y_910_);
    lean_dec(v___y_909_);
    lean_dec_ref(v___y_908_);
    return v_res_913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(
    mut v_pu_914_: u8,
    mut v_alt_915_: *mut LeanObject,
    mut v_f_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
    mut v___y_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    v___x_922_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_alt_915_, v_f_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
    return v___x_922_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___boxed(
    mut v_pu_923_: *mut LeanObject,
    mut v_alt_924_: *mut LeanObject,
    mut v_f_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
    mut v___y_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_931_: u8 = 0;
    let mut v_res_932_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_931_ = (lean_unbox(v_pu_923_) as u8);
    v_res_932_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1(v_pu_boxed_931_, v_alt_924_, v_f_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
    lean_dec(v___y_929_);
    lean_dec_ref(v___y_928_);
    lean_dec(v___y_927_);
    lean_dec_ref(v___y_926_);
    return v_res_932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(
    mut v_a_933_: *mut LeanObject,
    mut v_x_934_: *mut LeanObject,
) -> u8 {
    let mut v___x_935_: u8 = 0;
    let mut v_key_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_934_) == 0 {
                    v___x_935_ = 0;
                    return v___x_935_;
                } else {
                    v_key_936_ = lean_ctor_get(v_x_934_, 0);
                    v_tail_937_ = lean_ctor_get(v_x_934_, 2);
                    v___x_938_ = l_Lean_instBEqFVarId_beq(v_key_936_, v_a_933_);
                    if v___x_938_ == 0 {
                        v_x_934_ = v_tail_937_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_938_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg___boxed(
    mut v_a_940_: *mut LeanObject,
    mut v_x_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_942_: u8 = 0;
    let mut v_r_943_: *mut LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_940_, v_x_941_);
    lean_dec(v_x_941_);
    lean_dec(v_a_940_);
    v_r_943_ = lean_box((v_res_942_) as usize);
    return v_r_943_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(
    mut v_m_944_: *mut LeanObject,
    mut v_a_945_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u64 = 0;
    let mut v___x_949_: u64 = 0;
    let mut v___x_950_: u64 = 0;
    let mut v_fold_951_: u64 = 0;
    let mut v___x_952_: u64 = 0;
    let mut v___x_953_: u64 = 0;
    let mut v___x_954_: u64 = 0;
    let mut v___x_955_: usize = 0;
    let mut v___x_956_: usize = 0;
    let mut v___x_957_: usize = 0;
    let mut v___x_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    v_buckets_946_ = lean_ctor_get(v_m_944_, 1);
    v___x_947_ = lean_array_get_size(v_buckets_946_);
    v___x_948_ = l_Lean_instHashableFVarId_hash(v_a_945_);
    v___x_949_ = 32u64;
    v___x_950_ = lean_uint64_shift_right(v___x_948_, v___x_949_);
    v_fold_951_ = lean_uint64_xor(v___x_948_, v___x_950_);
    v___x_952_ = 16u64;
    v___x_953_ = lean_uint64_shift_right(v_fold_951_, v___x_952_);
    v___x_954_ = lean_uint64_xor(v_fold_951_, v___x_953_);
    v___x_955_ = lean_uint64_to_usize(v___x_954_);
    v___x_956_ = lean_usize_of_nat(v___x_947_);
    v___x_957_ = 1usize;
    v___x_958_ = lean_usize_sub(v___x_956_, v___x_957_);
    v___x_959_ = lean_usize_land(v___x_955_, v___x_958_);
    v___x_960_ = lean_array_uget_borrowed(v_buckets_946_, v___x_959_);
    v___x_961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_945_, v___x_960_);
    return v___x_961_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg___boxed(
    mut v_m_962_: *mut LeanObject,
    mut v_a_963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_964_: u8 = 0;
    let mut v_r_965_: *mut LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_962_, v_a_963_);
    lean_dec(v_a_963_);
    lean_dec_ref(v_m_962_);
    v_r_965_ = lean_box((v_res_964_) as usize);
    return v_r_965_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(
    mut v_altsUsed_966_: *mut LeanObject,
    mut v_j_967_: *mut LeanObject,
    mut v_fvar_968_: *mut LeanObject,
    mut v_b_969_: *mut LeanObject,
    mut v___x_970_: u8,
    mut v_k_971_: *mut LeanObject,
    mut v___y_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    v___x_977_ = l_Lean_instInhabitedFVarIdHashSet;
    v___x_978_ = lean_array_get_borrowed(v___x_977_, v_altsUsed_966_, v_j_967_);
    v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v___x_978_, v_fvar_968_);
    if v___x_979_ == 0 {
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_b_969_);
        v___x_980_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_980_, 0, v_k_971_);
        return v___x_980_;
    } else {
        let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
        v___x_981_ = lean_unsigned_to_nat(1);
        v___x_982_ = lean_mk_empty_array_with_capacity(v___x_981_);
        v___x_983_ = lean_array_push(v___x_982_, v_b_969_);
        v___x_984_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_970_, v___x_983_, v_k_971_);
        lean_dec_ref(v___x_983_);
        v___x_985_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_985_, 0, v___x_984_);
        return v___x_985_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed(
    mut v_altsUsed_986_: *mut LeanObject,
    mut v_j_987_: *mut LeanObject,
    mut v_fvar_988_: *mut LeanObject,
    mut v_b_989_: *mut LeanObject,
    mut v___x_990_: *mut LeanObject,
    mut v_k_991_: *mut LeanObject,
    mut v___y_992_: *mut LeanObject,
    mut v___y_993_: *mut LeanObject,
    mut v___y_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2347__boxed_997_: u8 = 0;
    let mut v_res_998_: *mut LeanObject = core::ptr::null_mut();
    v___x_2347__boxed_997_ = (lean_unbox(v___x_990_) as u8);
    v_res_998_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0(v_altsUsed_986_, v_j_987_, v_fvar_988_, v_b_989_, v___x_2347__boxed_997_, v_k_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
    lean_dec(v___y_995_);
    lean_dec_ref(v___y_994_);
    lean_dec(v___y_993_);
    lean_dec_ref(v___y_992_);
    lean_dec(v_fvar_988_);
    lean_dec(v_j_987_);
    lean_dec_ref(v_altsUsed_986_);
    return v_res_998_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(
    mut v_altsUsed_999_: *mut LeanObject,
    mut v_fvar_1000_: *mut LeanObject,
    mut v_b_1001_: *mut LeanObject,
    mut v_as_1002_: *mut LeanObject,
    mut v_i_1003_: *mut LeanObject,
    mut v_j_1004_: *mut LeanObject,
    mut v_bs_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1012_: u8 = 0;
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1028_: u8 = 0;
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1011_ = lean_unsigned_to_nat(0);
                v_isZero_1012_ = lean_nat_dec_eq(v_i_1003_, v_zero_1011_);
                if v_isZero_1012_ == 1 {
                    lean_dec(v_j_1004_);
                    lean_dec(v_i_1003_);
                    lean_dec_ref(v_b_1001_);
                    lean_dec(v_fvar_1000_);
                    lean_dec_ref(v_altsUsed_999_);
                    v___x_1013_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1013_, 0, v_bs_1005_);
                    return v___x_1013_;
                } else {
                    v___x_1014_ = 1;
                    v___x_1015_ = lean_box((v___x_1014_) as usize);
                    lean_inc_ref(v_b_1001_);
                    lean_inc(v_fvar_1000_);
                    lean_inc(v_j_1004_);
                    lean_inc_ref(v_altsUsed_999_);
                    v___f_1016_ = lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                    lean_closure_set(v___f_1016_, 0, v_altsUsed_999_);
                    lean_closure_set(v___f_1016_, 1, v_j_1004_);
                    lean_closure_set(v___f_1016_, 2, v_fvar_1000_);
                    lean_closure_set(v___f_1016_, 3, v_b_1001_);
                    lean_closure_set(v___f_1016_, 4, v___x_1015_);
                    v___x_1017_ = lean_array_fget_borrowed(v_as_1002_, v_j_1004_);
                    lean_inc(v___x_1017_);
                    v___x_1018_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v___x_1017_, v___f_1016_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
                    if lean_obj_tag(v___x_1018_) == 0 {
                        v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
                        lean_inc(v_a_1019_);
                        lean_dec_ref_known(v___x_1018_, 1);
                        v_one_1020_ = lean_unsigned_to_nat(1);
                        v_n_1021_ = lean_nat_sub(v_i_1003_, v_one_1020_);
                        lean_dec(v_i_1003_);
                        v___x_1022_ = lean_nat_add(v_j_1004_, v_one_1020_);
                        lean_dec(v_j_1004_);
                        v___x_1023_ = lean_array_push(v_bs_1005_, v_a_1019_);
                        v_i_1003_ = v_n_1021_;
                        v_j_1004_ = v___x_1022_;
                        v_bs_1005_ = v___x_1023_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1005_);
                        lean_dec(v_j_1004_);
                        lean_dec(v_i_1003_);
                        lean_dec_ref(v_b_1001_);
                        lean_dec(v_fvar_1000_);
                        lean_dec_ref(v_altsUsed_999_);
                        v_a_1025_ = lean_ctor_get(v___x_1018_, 0);
                        v_isSharedCheck_1032_ = (!lean_is_exclusive(v___x_1018_)) as u8;
                        if v_isSharedCheck_1032_ == 0 {
                            v___x_1027_ = v___x_1018_;
                            v_isShared_1028_ = v_isSharedCheck_1032_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1025_);
                            lean_dec(v___x_1018_);
                            v___x_1027_ = lean_box(0);
                            v_isShared_1028_ = v_isSharedCheck_1032_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1028_ == 0 {
                    v___x_1030_ = v___x_1027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
                    v___x_1030_ = v_reuseFailAlloc_1031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg___boxed(
    mut v_altsUsed_1033_: *mut LeanObject,
    mut v_fvar_1034_: *mut LeanObject,
    mut v_b_1035_: *mut LeanObject,
    mut v_as_1036_: *mut LeanObject,
    mut v_i_1037_: *mut LeanObject,
    mut v_j_1038_: *mut LeanObject,
    mut v_bs_1039_: *mut LeanObject,
    mut v___y_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
    mut v___y_1043_: *mut LeanObject,
    mut v___y_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1045_: *mut LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1033_, v_fvar_1034_, v_b_1035_, v_as_1036_, v_i_1037_, v_j_1038_, v_bs_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
    lean_dec(v___y_1043_);
    lean_dec_ref(v___y_1042_);
    lean_dec(v___y_1041_);
    lean_dec_ref(v___y_1040_);
    lean_dec_ref(v_as_1036_);
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(
    mut v_fvar_1046_: *mut LeanObject,
    mut v_b_1047_: *mut LeanObject,
    mut v_sz_1048_: usize,
    mut v_i_1049_: usize,
    mut v_bs_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1051_: u8 = 0;
    let mut v_v_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: usize = 0;
    let mut v___x_1058_: usize = 0;
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: u8 = 0;
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1051_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
                if v___x_1051_ == 0 {
                    lean_dec_ref(v_b_1047_);
                    return v_bs_1050_;
                } else {
                    v_v_1052_ = lean_array_uget(v_bs_1050_, v_i_1049_);
                    v___x_1053_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1054_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1053_);
                    v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_v_1052_, v_fvar_1046_);
                    if v___x_1061_ == 0 {
                        v___y_1056_ = v_v_1052_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1062_ = 1;
                        lean_inc_ref(v_b_1047_);
                        v___x_1063_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(
                            v___x_1062_,
                            v_b_1047_,
                            v_v_1052_,
                        );
                        v___y_1056_ = v___x_1063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1057_ = 1usize;
                v___x_1058_ = lean_usize_add(v_i_1049_, v___x_1057_);
                v___x_1059_ = lean_array_uset(v_bs_x27_1054_, v_i_1049_, v___y_1056_);
                v_i_1049_ = v___x_1058_;
                v_bs_1050_ = v___x_1059_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3___boxed(
    mut v_fvar_1064_: *mut LeanObject,
    mut v_b_1065_: *mut LeanObject,
    mut v_sz_1066_: *mut LeanObject,
    mut v_i_1067_: *mut LeanObject,
    mut v_bs_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1069_: usize = 0;
    let mut v_i_boxed_1070_: usize = 0;
    let mut v_res_1071_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1066_);
    lean_dec(v_sz_1066_);
    v_i_boxed_1070_ = lean_unbox_usize(v_i_1067_);
    lean_dec(v_i_1067_);
    v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v_fvar_1064_, v_b_1065_, v_sz_boxed_1069_, v_i_boxed_1070_, v_bs_1068_);
    lean_dec(v_fvar_1064_);
    return v_res_1071_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0()
-> *mut LeanObject {
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = 1;
    v___x_1073_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(
    mut v_decls_1074_: *mut LeanObject,
    mut v_alts_1075_: *mut LeanObject,
    mut v_altsUsed_1076_: *mut LeanObject,
    mut v_ctx_1077_: *mut LeanObject,
    mut v_ctxUsed_1078_: *mut LeanObject,
    mut v_a_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1103_: usize = 0;
    let mut v___x_1104_: usize = 0;
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvar_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut v_unused_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1084_ = lean_array_get_size(v_decls_1074_);
                v___x_1085_ = lean_unsigned_to_nat(0);
                v___x_1086_ = lean_nat_dec_eq(v___x_1084_, v___x_1085_);
                if v___x_1086_ == 0 {
                    v___x_1087_ = 1;
                    v___x_1088_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___closed__0);
                    v___x_1089_ = lean_unsigned_to_nat(1);
                    v___x_1090_ = lean_nat_sub(v___x_1084_, v___x_1089_);
                    v_b_1091_ = lean_array_get(v___x_1088_, v_decls_1074_, v___x_1090_);
                    lean_dec(v___x_1090_);
                    v_bs_1092_ = lean_array_pop(v_decls_1074_);
                    lean_inc(v_b_1091_);
                    lean_inc_ref(v_bs_1092_);
                    v___x_1115_ = lean_array_push(v_bs_1092_, v_b_1091_);
                    lean_inc_ref(v_ctx_1077_);
                    v___x_1116_ = l_Array_reverse___redArg(v_ctx_1077_);
                    v___x_1117_ = l_Array_append___redArg(v___x_1115_, v___x_1116_);
                    lean_dec_ref(v___x_1116_);
                    lean_inc_ref(v_alts_1075_);
                    v___x_1118_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1118_, 0, v___x_1117_);
                    lean_ctor_set(v___x_1118_, 1, v_alts_1075_);
                    if lean_obj_tag(v_b_1091_) == 0 {
                        v_decl_1119_ = lean_ctor_get(v_b_1091_, 0);
                        v_fvarId_1120_ = lean_ctor_get(v_decl_1119_, 0);
                        v_value_1121_ = lean_ctor_get(v_decl_1119_, 3);
                        lean_inc_ref_n(v_b_1091_, 2);
                        lean_inc_ref(v_ctx_1077_);
                        v___x_1122_ = lean_array_push(v_ctx_1077_, v_b_1091_);
                        lean_inc_ref(v_ctxUsed_1078_);
                        v___x_1123_ = l_Lean_Compiler_LCNF_CodeDecl_collectUsed(
                            v___x_1087_,
                            v_b_1091_,
                            v_ctxUsed_1078_,
                        );
                        match lean_obj_tag(v_value_1121_) {
                            7 => {
                                lean_dec_ref_known(v___x_1118_, 2);
                                lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            6 => {
                                lean_dec_ref_known(v___x_1118_, 2);
                                lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            8 => {
                                lean_dec_ref_known(v___x_1118_, 2);
                                lean_inc(v_fvarId_1120_);
                                v_fvar_1125_ = v_fvarId_1120_;
                                v___y_1126_ = v_a_1079_;
                                v___y_1127_ = v_a_1080_;
                                v___y_1128_ = v_a_1081_;
                                v___y_1129_ = v_a_1082_;
                                state = 4;
                                continue;
                            }
                            _ => {
                                lean_dec_ref(v___x_1123_);
                                lean_dec_ref(v___x_1122_);
                                lean_dec_ref(v_bs_1092_);
                                lean_dec_ref(v_ctxUsed_1078_);
                                lean_dec_ref(v_ctx_1077_);
                                lean_dec_ref(v_altsUsed_1076_);
                                lean_dec_ref(v_alts_1075_);
                                v_isSharedCheck_1138_ = (!lean_is_exclusive(v_b_1091_)) as u8;
                                if v_isSharedCheck_1138_ == 0 {
                                    v_unused_1139_ = lean_ctor_get(v_b_1091_, 0);
                                    lean_dec(v_unused_1139_);
                                    v___x_1133_ = v_b_1091_;
                                    v_isShared_1134_ = v_isSharedCheck_1138_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v_b_1091_);
                                    v___x_1133_ = lean_box(0);
                                    v_isShared_1134_ = v_isSharedCheck_1138_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_bs_1092_);
                        lean_dec(v_b_1091_);
                        lean_dec_ref(v_ctxUsed_1078_);
                        lean_dec_ref(v_ctx_1077_);
                        lean_dec_ref(v_altsUsed_1076_);
                        lean_dec_ref(v_alts_1075_);
                        v___x_1140_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1140_, 0, v___x_1118_);
                        return v___x_1140_;
                    }
                } else {
                    lean_dec_ref(v_ctxUsed_1078_);
                    lean_dec_ref(v_altsUsed_1076_);
                    lean_dec_ref(v_decls_1074_);
                    v___x_1141_ = l_Array_reverse___redArg(v_ctx_1077_);
                    v___x_1142_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1142_, 0, v___x_1141_);
                    lean_ctor_set(v___x_1142_, 1, v_alts_1075_);
                    v___x_1143_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    return v___x_1143_;
                }
            }
            1 => {
                v___x_1099_ = lean_array_get_size(v_alts_1075_);
                v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
                lean_inc(v_b_1091_);
                lean_inc(v___y_1094_);
                lean_inc_ref(v_altsUsed_1076_);
                v___x_1101_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1076_, v___y_1094_, v_b_1091_, v_alts_1075_, v___x_1099_, v___x_1085_, v___x_1100_, v___y_1097_, v___y_1098_, v___y_1096_, v___y_1095_);
                lean_dec_ref(v_alts_1075_);
                if lean_obj_tag(v___x_1101_) == 0 {
                    v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
                    lean_inc(v_a_1102_);
                    lean_dec_ref_known(v___x_1101_, 1);
                    v_sz_1103_ = lean_array_size(v_altsUsed_1076_);
                    v___x_1104_ = 0usize;
                    v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__3(v___y_1094_, v_b_1091_, v_sz_1103_, v___x_1104_, v_altsUsed_1076_);
                    lean_dec(v___y_1094_);
                    v_decls_1074_ = v_bs_1092_;
                    v_alts_1075_ = v_a_1102_;
                    v_altsUsed_1076_ = v___x_1105_;
                    v_a_1079_ = v___y_1097_;
                    v_a_1080_ = v___y_1098_;
                    v_a_1081_ = v___y_1096_;
                    v_a_1082_ = v___y_1095_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___y_1094_);
                    lean_dec_ref(v_bs_1092_);
                    lean_dec(v_b_1091_);
                    lean_dec_ref(v_ctxUsed_1078_);
                    lean_dec_ref(v_ctx_1077_);
                    lean_dec_ref(v_altsUsed_1076_);
                    v_a_1107_ = lean_ctor_get(v___x_1101_, 0);
                    v_isSharedCheck_1114_ = (!lean_is_exclusive(v___x_1101_)) as u8;
                    if v_isSharedCheck_1114_ == 0 {
                        v___x_1109_ = v___x_1101_;
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1107_);
                        lean_dec(v___x_1101_);
                        v___x_1109_ = lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1110_ == 0 {
                    v___x_1112_ = v___x_1109_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1112_;
            }
            4 => {
                v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_ctxUsed_1078_, v_fvar_1125_);
                if v___x_1130_ == 0 {
                    lean_dec_ref(v___x_1123_);
                    lean_dec_ref(v___x_1122_);
                    v___y_1094_ = v_fvar_1125_;
                    v___y_1095_ = v___y_1129_;
                    v___y_1096_ = v___y_1128_;
                    v___y_1097_ = v___y_1126_;
                    v___y_1098_ = v___y_1127_;
                    state = 1;
                    continue;
                } else {
                    if v___x_1086_ == 0 {
                        lean_dec(v_fvar_1125_);
                        lean_dec_ref_known(v_b_1091_, 1);
                        lean_dec_ref(v_ctxUsed_1078_);
                        lean_dec_ref(v_ctx_1077_);
                        v_decls_1074_ = v_bs_1092_;
                        v_ctx_1077_ = v___x_1122_;
                        v_ctxUsed_1078_ = v___x_1123_;
                        v_a_1079_ = v___y_1126_;
                        v_a_1080_ = v___y_1127_;
                        v_a_1081_ = v___y_1128_;
                        v_a_1082_ = v___y_1129_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_1123_);
                        lean_dec_ref(v___x_1122_);
                        v___y_1094_ = v_fvar_1125_;
                        v___y_1095_ = v___y_1129_;
                        v___y_1096_ = v___y_1128_;
                        v___y_1097_ = v___y_1126_;
                        v___y_1098_ = v___y_1127_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1134_ == 0 {
                    lean_ctor_set(v___x_1133_, 0, v___x_1118_);
                    v___x_1136_ = v___x_1133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1118_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go___boxed(
    mut v_decls_1144_: *mut LeanObject,
    mut v_alts_1145_: *mut LeanObject,
    mut v_altsUsed_1146_: *mut LeanObject,
    mut v_ctx_1147_: *mut LeanObject,
    mut v_ctxUsed_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
    mut v_a_1150_: *mut LeanObject,
    mut v_a_1151_: *mut LeanObject,
    mut v_a_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(
        v_decls_1144_,
        v_alts_1145_,
        v_altsUsed_1146_,
        v_ctx_1147_,
        v_ctxUsed_1148_,
        v_a_1149_,
        v_a_1150_,
        v_a_1151_,
        v_a_1152_,
    );
    lean_dec(v_a_1152_);
    lean_dec_ref(v_a_1151_);
    lean_dec(v_a_1150_);
    lean_dec_ref(v_a_1149_);
    return v_res_1154_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(
    mut v_00_u03b2_1155_: *mut LeanObject,
    mut v_m_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
) -> u8 {
    let mut v___x_1158_: u8 = 0;
    v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___redArg(v_m_1156_, v_a_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0___boxed(
    mut v_00_u03b2_1159_: *mut LeanObject,
    mut v_m_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1162_: u8 = 0;
    let mut v_r_1163_: *mut LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0(v_00_u03b2_1159_, v_m_1160_, v_a_1161_);
    lean_dec(v_a_1161_);
    lean_dec_ref(v_m_1160_);
    v_r_1163_ = lean_box((v_res_1162_) as usize);
    return v_r_1163_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(
    mut v_altsUsed_1164_: *mut LeanObject,
    mut v_fvar_1165_: *mut LeanObject,
    mut v_b_1166_: *mut LeanObject,
    mut v_as_1167_: *mut LeanObject,
    mut v_i_1168_: *mut LeanObject,
    mut v_j_1169_: *mut LeanObject,
    mut v_inv_1170_: *mut LeanObject,
    mut v_bs_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___redArg(v_altsUsed_1164_, v_fvar_1165_, v_b_1166_, v_as_1167_, v_i_1168_, v_j_1169_, v_bs_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    return v___x_1177_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2___boxed(
    mut v_altsUsed_1178_: *mut LeanObject,
    mut v_fvar_1179_: *mut LeanObject,
    mut v_b_1180_: *mut LeanObject,
    mut v_as_1181_: *mut LeanObject,
    mut v_i_1182_: *mut LeanObject,
    mut v_j_1183_: *mut LeanObject,
    mut v_inv_1184_: *mut LeanObject,
    mut v_bs_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1191_: *mut LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__2(v_altsUsed_1178_, v_fvar_1179_, v_b_1180_, v_as_1181_, v_i_1182_, v_j_1183_, v_inv_1184_, v_bs_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
    lean_dec(v___y_1189_);
    lean_dec_ref(v___y_1188_);
    lean_dec(v___y_1187_);
    lean_dec_ref(v___y_1186_);
    lean_dec_ref(v_as_1181_);
    return v_res_1191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(
    mut v_00_u03b2_1192_: *mut LeanObject,
    mut v_a_1193_: *mut LeanObject,
    mut v_x_1194_: *mut LeanObject,
) -> u8 {
    let mut v___x_1195_: u8 = 0;
    v___x_1195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_1193_, v_x_1194_);
    return v___x_1195_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1196_: *mut LeanObject,
    mut v_a_1197_: *mut LeanObject,
    mut v_x_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1199_: u8 = 0;
    let mut v_r_1200_: *mut LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0(v_00_u03b2_1196_, v_a_1197_, v_x_1198_);
    lean_dec(v_x_1198_);
    lean_dec(v_a_1197_);
    v_r_1200_ = lean_box((v_res_1199_) as usize);
    return v_r_1200_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(
    mut v_sz_1201_: usize,
    mut v_i_1202_: usize,
    mut v_bs_1203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u8 = 0;
    let mut v___y_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: usize = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1204_ = lean_usize_dec_lt(v_i_1202_, v_sz_1201_);
                if v___x_1204_ == 0 {
                    return v_bs_1203_;
                } else {
                    v___x_1205_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                    v_v_1206_ = lean_array_uget(v_bs_1203_, v_i_1202_);
                    v___x_1207_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1208_ = lean_array_uset(v_bs_1203_, v_i_1202_, v___x_1207_);
                    v___x_1209_ = 1;
                    match lean_obj_tag(v_v_1206_) {
                        0 => {
                            v_code_1217_ = lean_ctor_get(v_v_1206_, 2);
                            lean_inc_ref(v_code_1217_);
                            lean_dec_ref_known(v_v_1206_, 3);
                            v___y_1211_ = v_code_1217_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1218_ = lean_ctor_get(v_v_1206_, 1);
                            lean_inc_ref(v_code_1218_);
                            lean_dec_ref_known(v_v_1206_, 2);
                            v___y_1211_ = v_code_1218_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1219_ = lean_ctor_get(v_v_1206_, 0);
                            lean_inc_ref(v_code_1219_);
                            lean_dec_ref_known(v_v_1206_, 1);
                            v___y_1211_ = v_code_1219_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1212_ =
                    l_Lean_Compiler_LCNF_Code_collectUsed(v___x_1209_, v___y_1211_, v___x_1205_);
                v___x_1213_ = 1usize;
                v___x_1214_ = lean_usize_add(v_i_1202_, v___x_1213_);
                v___x_1215_ = lean_array_uset(v_bs_x27_1208_, v_i_1202_, v___x_1212_);
                v_i_1202_ = v___x_1214_;
                v_bs_1203_ = v___x_1215_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1___boxed(
    mut v_sz_1220_: *mut LeanObject,
    mut v_i_1221_: *mut LeanObject,
    mut v_bs_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1223_: usize = 0;
    let mut v_i_boxed_1224_: usize = 0;
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1223_ = lean_unbox_usize(v_sz_1220_);
    lean_dec(v_sz_1220_);
    v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
    lean_dec(v_i_1221_);
    v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_boxed_1223_, v_i_boxed_1224_, v_bs_1222_);
    return v_res_1225_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_1226_: *mut LeanObject,
    mut v_x_1227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u64 = 0;
    let mut v___x_1236_: u64 = 0;
    let mut v___x_1237_: u64 = 0;
    let mut v_fold_1238_: u64 = 0;
    let mut v___x_1239_: u64 = 0;
    let mut v___x_1240_: u64 = 0;
    let mut v___x_1241_: u64 = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: usize = 0;
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1227_) == 0 {
                    return v_x_1226_;
                } else {
                    v_key_1228_ = lean_ctor_get(v_x_1227_, 0);
                    v_value_1229_ = lean_ctor_get(v_x_1227_, 1);
                    v_tail_1230_ = lean_ctor_get(v_x_1227_, 2);
                    v_isSharedCheck_1253_ = (!lean_is_exclusive(v_x_1227_)) as u8;
                    if v_isSharedCheck_1253_ == 0 {
                        v___x_1232_ = v_x_1227_;
                        v_isShared_1233_ = v_isSharedCheck_1253_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1230_);
                        lean_inc(v_value_1229_);
                        lean_inc(v_key_1228_);
                        lean_dec(v_x_1227_);
                        v___x_1232_ = lean_box(0);
                        v_isShared_1233_ = v_isSharedCheck_1253_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v_x_1226_);
                v___x_1235_ = l_Lean_instHashableFVarId_hash(v_key_1228_);
                v___x_1236_ = 32u64;
                v___x_1237_ = lean_uint64_shift_right(v___x_1235_, v___x_1236_);
                v_fold_1238_ = lean_uint64_xor(v___x_1235_, v___x_1237_);
                v___x_1239_ = 16u64;
                v___x_1240_ = lean_uint64_shift_right(v_fold_1238_, v___x_1239_);
                v___x_1241_ = lean_uint64_xor(v_fold_1238_, v___x_1240_);
                v___x_1242_ = lean_uint64_to_usize(v___x_1241_);
                v___x_1243_ = lean_usize_of_nat(v___x_1234_);
                v___x_1244_ = 1usize;
                v___x_1245_ = lean_usize_sub(v___x_1243_, v___x_1244_);
                v___x_1246_ = lean_usize_land(v___x_1242_, v___x_1245_);
                v___x_1247_ = lean_array_uget_borrowed(v_x_1226_, v___x_1246_);
                lean_inc(v___x_1247_);
                if v_isShared_1233_ == 0 {
                    lean_ctor_set(v___x_1232_, 2, v___x_1247_);
                    v___x_1249_ = v___x_1232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_key_1228_);
                    lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_value_1229_);
                    lean_ctor_set(v_reuseFailAlloc_1252_, 2, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1250_ = lean_array_uset(v_x_1226_, v___x_1246_, v___x_1249_);
                v_x_1226_ = v___x_1250_;
                v_x_1227_ = v_tail_1230_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(
    mut v_i_1254_: *mut LeanObject,
    mut v_source_1255_: *mut LeanObject,
    mut v_target_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    let mut v_es_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1257_ = lean_array_get_size(v_source_1255_);
                v___x_1258_ = lean_nat_dec_lt(v_i_1254_, v___x_1257_);
                if v___x_1258_ == 0 {
                    lean_dec_ref(v_source_1255_);
                    lean_dec(v_i_1254_);
                    return v_target_1256_;
                } else {
                    v_es_1259_ = lean_array_fget(v_source_1255_, v_i_1254_);
                    v___x_1260_ = lean_box(0);
                    v_source_1261_ = lean_array_fset(v_source_1255_, v_i_1254_, v___x_1260_);
                    v_target_1262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_target_1256_, v_es_1259_);
                    v___x_1263_ = lean_unsigned_to_nat(1);
                    v___x_1264_ = lean_nat_add(v_i_1254_, v___x_1263_);
                    lean_dec(v_i_1254_);
                    v_i_1254_ = v___x_1264_;
                    v_source_1255_ = v_source_1261_;
                    v_target_1256_ = v_target_1262_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(
    mut v_data_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ = lean_array_get_size(v_data_1266_);
    v___x_1268_ = lean_unsigned_to_nat(2);
    v_nbuckets_1269_ = lean_nat_mul(v___x_1267_, v___x_1268_);
    v___x_1270_ = lean_unsigned_to_nat(0);
    v___x_1271_ = lean_box(0);
    v___x_1272_ = lean_mk_array(v_nbuckets_1269_, v___x_1271_);
    v___x_1273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v___x_1270_, v_data_1266_, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(
    mut v_m_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_b_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    let mut v_fold_1283_: u64 = 0;
    let mut v___x_1284_: u64 = 0;
    let mut v___x_1285_: u64 = 0;
    let mut v___x_1286_: u64 = 0;
    let mut v___x_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v_bkt_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v_val_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_unused_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1277_ = lean_ctor_get(v_m_1274_, 0);
                v_buckets_1278_ = lean_ctor_get(v_m_1274_, 1);
                v___x_1279_ = lean_array_get_size(v_buckets_1278_);
                v___x_1280_ = l_Lean_instHashableFVarId_hash(v_a_1275_);
                v___x_1281_ = 32u64;
                v___x_1282_ = lean_uint64_shift_right(v___x_1280_, v___x_1281_);
                v_fold_1283_ = lean_uint64_xor(v___x_1280_, v___x_1282_);
                v___x_1284_ = 16u64;
                v___x_1285_ = lean_uint64_shift_right(v_fold_1283_, v___x_1284_);
                v___x_1286_ = lean_uint64_xor(v_fold_1283_, v___x_1285_);
                v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
                v___x_1288_ = lean_usize_of_nat(v___x_1279_);
                v___x_1289_ = 1usize;
                v___x_1290_ = lean_usize_sub(v___x_1288_, v___x_1289_);
                v___x_1291_ = lean_usize_land(v___x_1287_, v___x_1290_);
                v_bkt_1292_ = lean_array_uget_borrowed(v_buckets_1278_, v___x_1291_);
                v___x_1293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__0_spec__0___redArg(v_a_1275_, v_bkt_1292_);
                if v___x_1293_ == 0 {
                    lean_inc_ref(v_buckets_1278_);
                    lean_inc(v_size_1277_);
                    v_isSharedCheck_1314_ = (!lean_is_exclusive(v_m_1274_)) as u8;
                    if v_isSharedCheck_1314_ == 0 {
                        v_unused_1315_ = lean_ctor_get(v_m_1274_, 1);
                        lean_dec(v_unused_1315_);
                        v_unused_1316_ = lean_ctor_get(v_m_1274_, 0);
                        lean_dec(v_unused_1316_);
                        v___x_1295_ = v_m_1274_;
                        v_isShared_1296_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1274_);
                        v___x_1295_ = lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1314_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1276_);
                    lean_dec(v_a_1275_);
                    return v_m_1274_;
                }
            }
            1 => {
                v___x_1297_ = lean_unsigned_to_nat(1);
                v_size_x27_1298_ = lean_nat_add(v_size_1277_, v___x_1297_);
                lean_dec(v_size_1277_);
                lean_inc(v_bkt_1292_);
                v___x_1299_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1299_, 0, v_a_1275_);
                lean_ctor_set(v___x_1299_, 1, v_b_1276_);
                lean_ctor_set(v___x_1299_, 2, v_bkt_1292_);
                v_buckets_x27_1300_ = lean_array_uset(v_buckets_1278_, v___x_1291_, v___x_1299_);
                v___x_1301_ = lean_unsigned_to_nat(4);
                v___x_1302_ = lean_nat_mul(v_size_x27_1298_, v___x_1301_);
                v___x_1303_ = lean_unsigned_to_nat(3);
                v___x_1304_ = lean_nat_div(v___x_1302_, v___x_1303_);
                lean_dec(v___x_1302_);
                v___x_1305_ = lean_array_get_size(v_buckets_x27_1300_);
                v___x_1306_ = lean_nat_dec_le(v___x_1304_, v___x_1305_);
                lean_dec(v___x_1304_);
                if v___x_1306_ == 0 {
                    v_val_1307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_buckets_x27_1300_);
                    if v_isShared_1296_ == 0 {
                        lean_ctor_set(v___x_1295_, 1, v_val_1307_);
                        lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1309_ = v___x_1295_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_size_x27_1298_);
                        lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_val_1307_);
                        v___x_1309_ = v_reuseFailAlloc_1310_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1296_ == 0 {
                        lean_ctor_set(v___x_1295_, 1, v_buckets_x27_1300_);
                        lean_ctor_set(v___x_1295_, 0, v_size_x27_1298_);
                        v___x_1312_ = v___x_1295_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_size_x27_1298_);
                        lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_buckets_x27_1300_);
                        v___x_1312_ = v_reuseFailAlloc_1313_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1309_;
            }
            3 => {
                return v___x_1312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed(
    mut v_code_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
    mut v_a_1321_: *mut LeanObject,
    mut v_a_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
    mut v_a_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1325_: *mut LeanObject = core::ptr::null_mut();
    v_res_1325_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(
        v_code_1319_,
        v_a_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
    );
    lean_dec(v_a_1323_);
    lean_dec_ref(v_a_1322_);
    lean_dec(v_a_1321_);
    lean_dec_ref(v_a_1320_);
    return v_res_1325_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(
    mut v_i_1326_: *mut LeanObject,
    mut v_as_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
    mut v___y_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: usize = 0;
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = lean_array_get_size(v_as_1327_);
                v___x_1334_ = lean_nat_dec_lt(v_i_1326_, v___x_1333_);
                if v___x_1334_ == 0 {
                    lean_dec(v_i_1326_);
                    v___x_1335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1335_, 0, v_as_1327_);
                    return v___x_1335_;
                } else {
                    v_a_1336_ = lean_array_fget_borrowed(v_as_1327_, v_i_1326_);
                    v___x_1337_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___boxed as *mut core::ffi::c_void, 6, 0);
                    lean_inc(v_a_1336_);
                    v___x_1338_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go_spec__1___redArg(v_a_1336_, v___x_1337_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
                    if lean_obj_tag(v___x_1338_) == 0 {
                        v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
                        lean_inc(v_a_1339_);
                        lean_dec_ref_known(v___x_1338_, 1);
                        v___x_1340_ = lean_ptr_addr(v_a_1336_);
                        v___x_1341_ = lean_ptr_addr(v_a_1339_);
                        v___x_1342_ = lean_usize_dec_eq(v___x_1340_, v___x_1341_);
                        if v___x_1342_ == 0 {
                            v___x_1343_ = lean_unsigned_to_nat(1);
                            v___x_1344_ = lean_nat_add(v_i_1326_, v___x_1343_);
                            v___x_1345_ = lean_array_fset(v_as_1327_, v_i_1326_, v_a_1339_);
                            lean_dec(v_i_1326_);
                            v_i_1326_ = v___x_1344_;
                            v_as_1327_ = v___x_1345_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_1339_);
                            v___x_1347_ = lean_unsigned_to_nat(1);
                            v___x_1348_ = lean_nat_add(v_i_1326_, v___x_1347_);
                            lean_dec(v_i_1326_);
                            v_i_1326_ = v___x_1348_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_1327_);
                        lean_dec(v_i_1326_);
                        v_a_1350_ = lean_ctor_get(v___x_1338_, 0);
                        v_isSharedCheck_1357_ = (!lean_is_exclusive(v___x_1338_)) as u8;
                        if v_isSharedCheck_1357_ == 0 {
                            v___x_1352_ = v___x_1338_;
                            v_isShared_1353_ = v_isSharedCheck_1357_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1350_);
                            lean_dec(v___x_1338_);
                            v___x_1352_ = lean_box(0);
                            v_isShared_1353_ = v_isSharedCheck_1357_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1353_ == 0 {
                    v___x_1355_ = v___x_1352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
                    v___x_1355_ = v_reuseFailAlloc_1356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(
    mut v_c_1358_: *mut LeanObject,
    mut v_decls_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_typeName_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v_altsUsed_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctxUsed_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_a_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_1365_ = lean_ctor_get(v_c_1358_, 0);
                v_resultType_1366_ = lean_ctor_get(v_c_1358_, 1);
                v_discr_1367_ = lean_ctor_get(v_c_1358_, 2);
                v_alts_1368_ = lean_ctor_get(v_c_1358_, 3);
                v_isSharedCheck_1415_ = (!lean_is_exclusive(v_c_1358_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1370_ = v_c_1358_;
                    v_isShared_1371_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_alts_1368_);
                    lean_inc(v_discr_1367_);
                    lean_inc(v_resultType_1366_);
                    lean_inc(v_typeName_1365_);
                    lean_dec(v_c_1358_);
                    v___x_1370_ = lean_box(0);
                    v_isShared_1371_ = v_isSharedCheck_1415_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1372_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v_sz_1373_ = lean_array_size(v_alts_1368_);
                v___x_1374_ = 0usize;
                lean_inc_ref(v_alts_1368_);
                v_altsUsed_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__1(v_sz_1373_, v___x_1374_, v_alts_1368_);
                v___x_1376_ = lean_box(0);
                lean_inc(v_discr_1367_);
                v_ctxUsed_1377_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v___x_1372_, v_discr_1367_, v___x_1376_);
                v___x_1378_ = lean_unsigned_to_nat(0);
                v___x_1379_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0;
                v___x_1380_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_go(v_decls_1359_, v_alts_1368_, v_altsUsed_1375_, v___x_1379_, v_ctxUsed_1377_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                if lean_obj_tag(v___x_1380_) == 0 {
                    v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
                    lean_inc(v_a_1381_);
                    lean_dec_ref_known(v___x_1380_, 1);
                    v_fst_1382_ = lean_ctor_get(v_a_1381_, 0);
                    lean_inc(v_fst_1382_);
                    v_snd_1383_ = lean_ctor_get(v_a_1381_, 1);
                    lean_inc(v_snd_1383_);
                    lean_dec(v_a_1381_);
                    v___x_1384_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v___x_1378_, v_snd_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                    if lean_obj_tag(v___x_1384_) == 0 {
                        v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
                        v_isSharedCheck_1398_ = (!lean_is_exclusive(v___x_1384_)) as u8;
                        if v_isSharedCheck_1398_ == 0 {
                            v___x_1387_ = v___x_1384_;
                            v_isShared_1388_ = v_isSharedCheck_1398_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1385_);
                            lean_dec(v___x_1384_);
                            v___x_1387_ = lean_box(0);
                            v_isShared_1388_ = v_isSharedCheck_1398_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_1382_);
                        lean_del_object(v___x_1370_);
                        lean_dec(v_discr_1367_);
                        lean_dec_ref(v_resultType_1366_);
                        lean_dec(v_typeName_1365_);
                        v_a_1399_ = lean_ctor_get(v___x_1384_, 0);
                        v_isSharedCheck_1406_ = (!lean_is_exclusive(v___x_1384_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1401_ = v___x_1384_;
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1399_);
                            lean_dec(v___x_1384_);
                            v___x_1401_ = lean_box(0);
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1370_);
                    lean_dec(v_discr_1367_);
                    lean_dec_ref(v_resultType_1366_);
                    lean_dec(v_typeName_1365_);
                    v_a_1407_ = lean_ctor_get(v___x_1380_, 0);
                    v_isSharedCheck_1414_ = (!lean_is_exclusive(v___x_1380_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v___x_1409_ = v___x_1380_;
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1407_);
                        lean_dec(v___x_1380_);
                        v___x_1409_ = lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1389_ = 1;
                if v_isShared_1371_ == 0 {
                    lean_ctor_set(v___x_1370_, 3, v_a_1385_);
                    v___x_1391_ = v___x_1370_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_typeName_1365_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_resultType_1366_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_discr_1367_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_a_1385_);
                    v___x_1391_ = v_reuseFailAlloc_1397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1392_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                v___x_1393_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1389_, v_fst_1382_, v___x_1392_);
                lean_dec(v_fst_1382_);
                if v_isShared_1388_ == 0 {
                    lean_ctor_set(v___x_1387_, 0, v___x_1393_);
                    v___x_1395_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
                    v___x_1395_ = v_reuseFailAlloc_1396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1395_;
            }
            5 => {
                if v_isShared_1402_ == 0 {
                    v___x_1404_ = v___x_1401_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1404_;
            }
            7 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
    mut v_c_1416_: *mut LeanObject,
    mut v_decls_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_cases_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_1488_: u8 = 0;
    let mut v_persistent_1489_: u8 = 0;
    let mut v_k_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_1496_: u8 = 0;
    let mut v_persistent_1497_: u8 = 0;
    let mut v_objs_x3f_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_c_1416_) {
                    0 => {
                        v_decl_1423_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc_ref(v_decl_1423_);
                        v_k_1424_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc_ref(v_k_1424_);
                        lean_dec_ref_known(v_c_1416_, 2);
                        v___x_1425_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1425_, 0, v_decl_1423_);
                        v___x_1426_ = lean_array_push(v_decls_1417_, v___x_1425_);
                        v_c_1416_ = v_k_1424_;
                        v_decls_1417_ = v___x_1426_;
                        state = 0;
                        continue;
                    }
                    2 => {
                        v_decl_1428_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc_ref(v_decl_1428_);
                        v_k_1429_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc_ref(v_k_1429_);
                        lean_dec_ref_known(v_c_1416_, 2);
                        v_params_1430_ = lean_ctor_get(v_decl_1428_, 2);
                        lean_inc_ref(v_params_1430_);
                        v_type_1431_ = lean_ctor_get(v_decl_1428_, 3);
                        lean_inc_ref(v_type_1431_);
                        v_value_1432_ = lean_ctor_get(v_decl_1428_, 4);
                        lean_inc_ref(v_value_1432_);
                        v___x_1433_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(v_value_1432_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
                        if lean_obj_tag(v___x_1433_) == 0 {
                            v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
                            v_isSharedCheck_1454_ = (!lean_is_exclusive(v___x_1433_)) as u8;
                            if v_isSharedCheck_1454_ == 0 {
                                v___x_1436_ = v___x_1433_;
                                v_isShared_1437_ = v_isSharedCheck_1454_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1434_);
                                lean_dec(v___x_1433_);
                                v___x_1436_ = lean_box(0);
                                v_isShared_1437_ = v_isSharedCheck_1454_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_type_1431_);
                            lean_dec_ref(v_params_1430_);
                            lean_dec_ref(v_k_1429_);
                            lean_dec_ref(v_decl_1428_);
                            lean_dec_ref(v_decls_1417_);
                            return v___x_1433_;
                        }
                    }
                    4 => {
                        v_cases_1455_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc_ref(v_cases_1455_);
                        lean_dec_ref_known(v_c_1416_, 1);
                        v___x_1456_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(v_cases_1455_, v_decls_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
                        return v___x_1456_;
                    }
                    7 => {
                        v_fvarId_1457_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1457_);
                        v_i_1458_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_i_1458_);
                        v_y_1459_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc(v_y_1459_);
                        v_k_1460_ = lean_ctor_get(v_c_1416_, 3);
                        lean_inc_ref(v_k_1460_);
                        lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1461_ = lean_alloc_ctor(3, 3, (0) as u32);
                        lean_ctor_set(v___x_1461_, 0, v_fvarId_1457_);
                        lean_ctor_set(v___x_1461_, 1, v_i_1458_);
                        lean_ctor_set(v___x_1461_, 2, v_y_1459_);
                        v___x_1462_ = lean_array_push(v_decls_1417_, v___x_1461_);
                        v_c_1416_ = v_k_1460_;
                        v_decls_1417_ = v___x_1462_;
                        state = 0;
                        continue;
                    }
                    8 => {
                        v_fvarId_1464_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1464_);
                        v_i_1465_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_i_1465_);
                        v_y_1466_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc(v_y_1466_);
                        v_k_1467_ = lean_ctor_get(v_c_1416_, 3);
                        lean_inc_ref(v_k_1467_);
                        lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1468_ = lean_alloc_ctor(4, 3, (0) as u32);
                        lean_ctor_set(v___x_1468_, 0, v_fvarId_1464_);
                        lean_ctor_set(v___x_1468_, 1, v_i_1465_);
                        lean_ctor_set(v___x_1468_, 2, v_y_1466_);
                        v___x_1469_ = lean_array_push(v_decls_1417_, v___x_1468_);
                        v_c_1416_ = v_k_1467_;
                        v_decls_1417_ = v___x_1469_;
                        state = 0;
                        continue;
                    }
                    9 => {
                        v_fvarId_1471_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1471_);
                        v_i_1472_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_i_1472_);
                        v_offset_1473_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc(v_offset_1473_);
                        v_y_1474_ = lean_ctor_get(v_c_1416_, 3);
                        lean_inc(v_y_1474_);
                        v_ty_1475_ = lean_ctor_get(v_c_1416_, 4);
                        lean_inc_ref(v_ty_1475_);
                        v_k_1476_ = lean_ctor_get(v_c_1416_, 5);
                        lean_inc_ref(v_k_1476_);
                        lean_dec_ref_known(v_c_1416_, 6);
                        v___x_1477_ = lean_alloc_ctor(5, 5, (0) as u32);
                        lean_ctor_set(v___x_1477_, 0, v_fvarId_1471_);
                        lean_ctor_set(v___x_1477_, 1, v_i_1472_);
                        lean_ctor_set(v___x_1477_, 2, v_offset_1473_);
                        lean_ctor_set(v___x_1477_, 3, v_y_1474_);
                        lean_ctor_set(v___x_1477_, 4, v_ty_1475_);
                        v___x_1478_ = lean_array_push(v_decls_1417_, v___x_1477_);
                        v_c_1416_ = v_k_1476_;
                        v_decls_1417_ = v___x_1478_;
                        state = 0;
                        continue;
                    }
                    10 => {
                        v_fvarId_1480_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1480_);
                        v_cidx_1481_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_cidx_1481_);
                        v_k_1482_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc_ref(v_k_1482_);
                        lean_dec_ref_known(v_c_1416_, 3);
                        v___x_1483_ = lean_alloc_ctor(6, 2, (0) as u32);
                        lean_ctor_set(v___x_1483_, 0, v_fvarId_1480_);
                        lean_ctor_set(v___x_1483_, 1, v_cidx_1481_);
                        v___x_1484_ = lean_array_push(v_decls_1417_, v___x_1483_);
                        v_c_1416_ = v_k_1482_;
                        v_decls_1417_ = v___x_1484_;
                        state = 0;
                        continue;
                    }
                    11 => {
                        v_fvarId_1486_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1486_);
                        v_n_1487_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_n_1487_);
                        v_check_1488_ = lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_1489_ = lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_1490_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc_ref(v_k_1490_);
                        lean_dec_ref_known(v_c_1416_, 3);
                        v___x_1491_ = lean_alloc_ctor(7, 2, (2) as u32);
                        lean_ctor_set(v___x_1491_, 0, v_fvarId_1486_);
                        lean_ctor_set(v___x_1491_, 1, v_n_1487_);
                        lean_ctor_set_uint8(
                            v___x_1491_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_check_1488_,
                        );
                        lean_ctor_set_uint8(
                            v___x_1491_,
                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            v_persistent_1489_,
                        );
                        v___x_1492_ = lean_array_push(v_decls_1417_, v___x_1491_);
                        v_c_1416_ = v_k_1490_;
                        v_decls_1417_ = v___x_1492_;
                        state = 0;
                        continue;
                    }
                    12 => {
                        v_fvarId_1494_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1494_);
                        v_n_1495_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc(v_n_1495_);
                        v_check_1496_ = lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        );
                        v_persistent_1497_ = lean_ctor_get_uint8(
                            v_c_1416_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_1498_ = lean_ctor_get(v_c_1416_, 2);
                        lean_inc(v_objs_x3f_1498_);
                        v_k_1499_ = lean_ctor_get(v_c_1416_, 3);
                        lean_inc_ref(v_k_1499_);
                        lean_dec_ref_known(v_c_1416_, 4);
                        v___x_1500_ = lean_alloc_ctor(8, 3, (2) as u32);
                        lean_ctor_set(v___x_1500_, 0, v_fvarId_1494_);
                        lean_ctor_set(v___x_1500_, 1, v_n_1495_);
                        lean_ctor_set(v___x_1500_, 2, v_objs_x3f_1498_);
                        lean_ctor_set_uint8(
                            v___x_1500_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_check_1496_,
                        );
                        lean_ctor_set_uint8(
                            v___x_1500_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_persistent_1497_,
                        );
                        v___x_1501_ = lean_array_push(v_decls_1417_, v___x_1500_);
                        v_c_1416_ = v_k_1499_;
                        v_decls_1417_ = v___x_1501_;
                        state = 0;
                        continue;
                    }
                    13 => {
                        v_fvarId_1503_ = lean_ctor_get(v_c_1416_, 0);
                        lean_inc(v_fvarId_1503_);
                        v_k_1504_ = lean_ctor_get(v_c_1416_, 1);
                        lean_inc_ref(v_k_1504_);
                        lean_dec_ref_known(v_c_1416_, 2);
                        v___x_1505_ = lean_alloc_ctor(9, 1, (0) as u32);
                        lean_ctor_set(v___x_1505_, 0, v_fvarId_1503_);
                        v___x_1506_ = lean_array_push(v_decls_1417_, v___x_1505_);
                        v_c_1416_ = v_k_1504_;
                        v_decls_1417_ = v___x_1506_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        v___x_1508_ = 1;
                        v___x_1509_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                            v___x_1508_,
                            v_decls_1417_,
                            v_c_1416_,
                        );
                        lean_dec_ref(v_decls_1417_);
                        v___x_1510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1510_, 0, v___x_1509_);
                        return v___x_1510_;
                    }
                }
            }
            1 => {
                v___x_1438_ = 1;
                v___x_1439_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1438_, v_decl_1428_, v_type_1431_, v_params_1430_, v_a_1434_, v_a_1419_);
                if lean_obj_tag(v___x_1439_) == 0 {
                    v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
                    lean_inc(v_a_1440_);
                    lean_dec_ref_known(v___x_1439_, 1);
                    if v_isShared_1437_ == 0 {
                        lean_ctor_set_tag(v___x_1436_, 2);
                        lean_ctor_set(v___x_1436_, 0, v_a_1440_);
                        v___x_1442_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1445_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1440_);
                        v___x_1442_ = v_reuseFailAlloc_1445_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1436_);
                    lean_dec_ref(v_k_1429_);
                    lean_dec_ref(v_decls_1417_);
                    v_a_1446_ = lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1453_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1448_ = v___x_1439_;
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1446_);
                        lean_dec(v___x_1439_);
                        v___x_1448_ = lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1443_ = lean_array_push(v_decls_1417_, v___x_1442_);
                v_c_1416_ = v_k_1429_;
                v_decls_1417_ = v___x_1443_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj(
    mut v_code_1511_: *mut LeanObject,
    mut v_a_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
    mut v_a_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    v___x_1517_ =
        l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj___closed__0;
    v___x_1518_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
        v_code_1511_,
        v___x_1517_,
        v_a_1512_,
        v_a_1513_,
        v_a_1514_,
        v_a_1515_,
    );
    return v___x_1518_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3___boxed(
    mut v_i_1519_: *mut LeanObject,
    mut v_as_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1526_: *mut LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__3(v_i_1519_, v_as_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    lean_dec(v___y_1524_);
    lean_dec_ref(v___y_1523_);
    lean_dec(v___y_1522_);
    lean_dec_ref(v___y_1521_);
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs___boxed(
    mut v_c_1527_: *mut LeanObject,
    mut v_decls_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
    mut v_a_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1534_: *mut LeanObject = core::ptr::null_mut();
    v_res_1534_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs(
        v_c_1527_,
        v_decls_1528_,
        v_a_1529_,
        v_a_1530_,
        v_a_1531_,
        v_a_1532_,
    );
    lean_dec(v_a_1532_);
    lean_dec_ref(v_a_1531_);
    lean_dec(v_a_1530_);
    lean_dec_ref(v_a_1529_);
    return v_res_1534_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go___boxed(
    mut v_c_1535_: *mut LeanObject,
    mut v_decls_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
    mut v_a_1539_: *mut LeanObject,
    mut v_a_1540_: *mut LeanObject,
    mut v_a_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Code_pushProj_go(
        v_c_1535_,
        v_decls_1536_,
        v_a_1537_,
        v_a_1538_,
        v_a_1539_,
        v_a_1540_,
    );
    lean_dec(v_a_1540_);
    lean_dec_ref(v_a_1539_);
    lean_dec(v_a_1538_);
    lean_dec_ref(v_a_1537_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2(
    mut v_00_u03b2_1543_: *mut LeanObject,
    mut v_m_1544_: *mut LeanObject,
    mut v_a_1545_: *mut LeanObject,
    mut v_b_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2___redArg(v_m_1544_, v_a_1545_, v_b_1546_);
    return v___x_1547_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3(
    mut v_00_u03b2_1548_: *mut LeanObject,
    mut v_data_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3___redArg(v_data_1549_);
    return v___x_1550_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1551_: *mut LeanObject,
    mut v_i_1552_: *mut LeanObject,
    mut v_source_1553_: *mut LeanObject,
    mut v_target_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4___redArg(v_i_1552_, v_source_1553_, v_target_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1556_: *mut LeanObject,
    mut v_x_1557_: *mut LeanObject,
    mut v_x_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1559_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Cases_pushProjs_spec__2_spec__3_spec__4_spec__6___redArg(v_x_1557_, v_x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(
    mut v_f_1560_: *mut LeanObject,
    mut v_v_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
    mut v___y_1563_: *mut LeanObject,
    mut v___y_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_a_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1561_) == 0 {
                    v_code_1567_ = lean_ctor_get(v_v_1561_, 0);
                    v_isSharedCheck_1591_ = (!lean_is_exclusive(v_v_1561_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1569_ = v_v_1561_;
                        v_isShared_1570_ = v_isSharedCheck_1591_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_1567_);
                        lean_dec(v_v_1561_);
                        v___x_1569_ = lean_box(0);
                        v_isShared_1570_ = v_isSharedCheck_1591_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_1560_);
                    v___x_1592_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1592_, 0, v_v_1561_);
                    return v___x_1592_;
                }
            }
            1 => {
                lean_inc(v___y_1565_);
                lean_inc_ref(v___y_1564_);
                lean_inc(v___y_1563_);
                lean_inc_ref(v___y_1562_);
                v___x_1571_ = lean_apply_6(
                    v_f_1560_,
                    v_code_1567_,
                    v___y_1562_,
                    v___y_1563_,
                    v___y_1564_,
                    v___y_1565_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1571_) == 0 {
                    v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1582_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1582_ == 0 {
                        v___x_1574_ = v___x_1571_;
                        v_isShared_1575_ = v_isSharedCheck_1582_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1572_);
                        lean_dec(v___x_1571_);
                        v___x_1574_ = lean_box(0);
                        v_isShared_1575_ = v_isSharedCheck_1582_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1569_);
                    v_a_1583_ = lean_ctor_get(v___x_1571_, 0);
                    v_isSharedCheck_1590_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1590_ == 0 {
                        v___x_1585_ = v___x_1571_;
                        v_isShared_1586_ = v_isSharedCheck_1590_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1583_);
                        lean_dec(v___x_1571_);
                        v___x_1585_ = lean_box(0);
                        v_isShared_1586_ = v_isSharedCheck_1590_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1570_ == 0 {
                    lean_ctor_set(v___x_1569_, 0, v_a_1572_);
                    v___x_1577_ = v___x_1569_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1572_);
                    v___x_1577_ = v_reuseFailAlloc_1581_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1575_ == 0 {
                    lean_ctor_set(v___x_1574_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1579_;
            }
            5 => {
                if v_isShared_1586_ == 0 {
                    v___x_1588_ = v___x_1585_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg___boxed(
    mut v_f_1593_: *mut LeanObject,
    mut v_v_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_1593_, v_v_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
    lean_dec(v___y_1598_);
    lean_dec_ref(v___y_1597_);
    lean_dec(v___y_1596_);
    lean_dec_ref(v___y_1595_);
    return v_res_1600_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(
    mut v_pu_1601_: u8,
    mut v_f_1602_: *mut LeanObject,
    mut v_v_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v_f_1602_, v_v_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___boxed(
    mut v_pu_1610_: *mut LeanObject,
    mut v_f_1611_: *mut LeanObject,
    mut v_v_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1618_: u8 = 0;
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1618_ = (lean_unbox(v_pu_1610_) as u8);
    v_res_1619_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0(v_pu_boxed_1618_, v_f_1611_, v_v_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
    lean_dec(v___y_1616_);
    lean_dec_ref(v___y_1615_);
    lean_dec(v___y_1614_);
    lean_dec_ref(v___y_1613_);
    return v_res_1619_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1()
-> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ = lean_box(0);
    v___x_1622_ = lean_unsigned_to_nat(16);
    v___x_1623_ = lean_mk_array(v___x_1622_, v___x_1621_);
    return v___x_1623_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2()
-> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__1);
    v___x_1625_ = lean_unsigned_to_nat(0);
    v___x_1626_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1626_, 0, v___x_1625_);
    lean_ctor_set(v___x_1626_, 1, v___x_1624_);
    return v___x_1626_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(
    mut v_decl_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_1635_: u8 = 0;
    let mut v_inlineAttr_x3f_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___f_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1653_: u8 = 0;
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1633_ = lean_ctor_get(v_decl_1627_, 0);
                v_value_1634_ = lean_ctor_get(v_decl_1627_, 1);
                v_recursive_1635_ = lean_ctor_get_uint8(
                    v_decl_1627_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1636_ = lean_ctor_get(v_decl_1627_, 2);
                v_isSharedCheck_1658_ = (!lean_is_exclusive(v_decl_1627_)) as u8;
                if v_isSharedCheck_1658_ == 0 {
                    v___x_1638_ = v_decl_1627_;
                    v_isShared_1639_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_1636_);
                    lean_inc(v_value_1634_);
                    lean_inc(v_toSignature_1633_);
                    lean_dec(v_decl_1627_);
                    v___x_1638_ = lean_box(0);
                    v_isShared_1639_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1640_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__0;
                v___x_1641_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj_spec__0___redArg(v___f_1640_, v_value_1634_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
                if lean_obj_tag(v___x_1641_) == 0 {
                    v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
                    lean_inc(v_a_1642_);
                    lean_dec_ref_known(v___x_1641_, 1);
                    v___x_1643_ = 1;
                    if v_isShared_1639_ == 0 {
                        lean_ctor_set(v___x_1638_, 1, v_a_1642_);
                        v___x_1645_ = v___x_1638_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_toSignature_1633_);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_a_1642_);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_inlineAttr_x3f_1636_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1649_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_recursive_1635_,
                        );
                        v___x_1645_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1638_);
                    lean_dec(v_inlineAttr_x3f_1636_);
                    lean_dec_ref(v_toSignature_1633_);
                    v_a_1650_ = lean_ctor_get(v___x_1641_, 0);
                    v_isSharedCheck_1657_ = (!lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v___x_1652_ = v___x_1641_;
                        v_isShared_1653_ = v_isSharedCheck_1657_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1650_);
                        lean_dec(v___x_1641_);
                        v___x_1652_ = lean_box(0);
                        v_isShared_1653_ = v_isSharedCheck_1657_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1646_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2_once), _init_l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___closed__2);
                v___x_1647_ = 0;
                v___x_1648_ = l_Lean_Compiler_LCNF_Decl_internalize(
                    v___x_1643_,
                    v___x_1645_,
                    v___x_1646_,
                    v___x_1647_,
                    v_a_1628_,
                    v_a_1629_,
                    v_a_1630_,
                    v_a_1631_,
                );
                return v___x_1648_;
            }
            3 => {
                if v_isShared_1653_ == 0 {
                    v___x_1655_ = v___x_1652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
                    v___x_1655_ = v_reuseFailAlloc_1656_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj___boxed(
    mut v_decl_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
    mut v_a_1662_: *mut LeanObject,
    mut v_a_1663_: *mut LeanObject,
    mut v_a_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1665_: *mut LeanObject = core::ptr::null_mut();
    v_res_1665_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_Decl_pushProj(
        v_decl_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
        v_a_1663_,
    );
    lean_dec(v_a_1663_);
    lean_dec_ref(v_a_1662_);
    lean_dec(v_a_1661_);
    lean_dec_ref(v_a_1660_);
    return v_res_1665_;
}
pub unsafe fn l_Lean_Compiler_LCNF_pushProj(
    mut v_occurrence_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_Compiler_LCNF_pushProj___closed__1;
    v___x_1672_ = 2;
    v___x_1673_ = l_Lean_Compiler_LCNF_pushProj___closed__2;
    v___x_1674_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_1671_,
        v___x_1672_,
        v___x_1673_,
        v_occurrence_1670_,
    );
    return v___x_1674_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1745_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_;
    v___x_1746_ = 1;
    v___x_1747_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_;
    v___x_1748_ = l_Lean_registerTraceClass(v___x_1745_, v___x_1746_, v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2____boxed(
    mut v_a_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
    return v_res_1750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_PushProj_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PushProj_1777867010____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PushProj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_PushProj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PushProj(builtin);
}
