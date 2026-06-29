// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceJpArity
// Imports: Lean.Compiler.LCNF.InferType
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Code_collectUsed,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseParam___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, l_Lean_Compiler_LCNF_Code_inferType,
    l_Lean_Compiler_LCNF_mkForallParams, runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg, l_Lean_Compiler_LCNF_instInhabitedPass,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        114, 101, 100, 117, 99, 101, 74, 112, 65, 114, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8550123126068977529 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2_value:
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
    m_fun: l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,6897217663849447951 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [82, 101, 100, 117, 99, 101, 74, 112, 65, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12331030006121242318 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16112769537961872119 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15743977403804370826 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11384531706685157208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2941981136042525329 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5700569467797085288 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3526734762254514713 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5101131859295122684 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2588805912275888294 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12059689623181931887 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5058358680727609464 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 563472653 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15141132279948100820 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16068942657267841435 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12508265142184441723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5862461103334136590 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(
    mut v_t_802_: *mut crate::leanh::LeanObject,
    mut v_k_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_802_) == 0 {
                    v_k_804_ = crate::leanh::lean_ctor_get(v_t_802_, 1);
                    v_v_805_ = crate::leanh::lean_ctor_get(v_t_802_, 2);
                    v_l_806_ = crate::leanh::lean_ctor_get(v_t_802_, 3);
                    v_r_807_ = crate::leanh::lean_ctor_get(v_t_802_, 4);
                    v___x_808_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_803_, v_k_804_);
                    match v___x_808_ {
                        0 => {
                            v_t_802_ = v_l_806_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_805_);
                            v___x_810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_810_, 0, v_v_805_);
                            return v___x_810_;
                        }
                        _ => {
                            v_t_802_ = v_r_807_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_812_ = crate::leanh::lean_box(0);
                    return v___x_812_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(
    mut v_t_813_: *mut crate::leanh::LeanObject,
    mut v_k_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_815_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_813_, v_k_814_);
    crate::leanh::lean_dec(v_k_814_);
    crate::leanh::lean_dec(v_t_813_);
    return v_res_815_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(
    mut v_as_816_: *mut crate::leanh::LeanObject,
    mut v_sz_817_: usize,
    mut v_i_818_: usize,
    mut v_b_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: usize = 0;
    let mut v___x_824_: usize = 0;
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v_array_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_843_: u8 = 0;
    let mut v_a_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_unused_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_826_ = lean_usize_dec_lt(v_i_818_, v_sz_817_);
                if v___x_826_ == 0 {
                    v___x_827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_827_, 0, v_b_819_);
                    return v___x_827_;
                } else {
                    v_snd_828_ = crate::leanh::lean_ctor_get(v_b_819_, 1);
                    v_fst_829_ = crate::leanh::lean_ctor_get(v_b_819_, 0);
                    v_isSharedCheck_863_ = (!crate::leanh::lean_is_exclusive(v_b_819_)) as u8;
                    if v_isSharedCheck_863_ == 0 {
                        v___x_831_ = v_b_819_;
                        v_isShared_832_ = v_isSharedCheck_863_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_828_);
                        crate::leanh::lean_inc(v_fst_829_);
                        crate::leanh::lean_dec(v_b_819_);
                        v___x_831_ = crate::leanh::lean_box(0);
                        v_isShared_832_ = v_isSharedCheck_863_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_823_ = 1usize;
                v___x_824_ = lean_usize_add(v_i_818_, v___x_823_);
                v_i_818_ = v___x_824_;
                v_b_819_ = v_a_822_;
                state = 0;
                continue;
            }
            2 => {
                v_array_833_ = crate::leanh::lean_ctor_get(v_snd_828_, 0);
                v_start_834_ = crate::leanh::lean_ctor_get(v_snd_828_, 1);
                v_stop_835_ = crate::leanh::lean_ctor_get(v_snd_828_, 2);
                v___x_836_ = lean_nat_dec_lt(v_start_834_, v_stop_835_);
                if v___x_836_ == 0 {
                    if v_isShared_832_ == 0 {
                        v___x_838_ = v___x_831_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_840_, 0, v_fst_829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_840_, 1, v_snd_828_);
                        v___x_838_ = v_reuseFailAlloc_840_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_835_);
                    crate::leanh::lean_inc(v_start_834_);
                    crate::leanh::lean_inc_ref(v_array_833_);
                    v_isSharedCheck_859_ = (!crate::leanh::lean_is_exclusive(v_snd_828_)) as u8;
                    if v_isSharedCheck_859_ == 0 {
                        v_unused_860_ = crate::leanh::lean_ctor_get(v_snd_828_, 2);
                        crate::leanh::lean_dec(v_unused_860_);
                        v_unused_861_ = crate::leanh::lean_ctor_get(v_snd_828_, 1);
                        crate::leanh::lean_dec(v_unused_861_);
                        v_unused_862_ = crate::leanh::lean_ctor_get(v_snd_828_, 0);
                        crate::leanh::lean_dec(v_unused_862_);
                        v___x_842_ = v_snd_828_;
                        v_isShared_843_ = v_isSharedCheck_859_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_828_);
                        v___x_842_ = crate::leanh::lean_box(0);
                        v_isShared_843_ = v_isSharedCheck_859_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_839_, 0, v___x_838_);
                return v___x_839_;
            }
            4 => {
                v_a_844_ = lean_array_uget_borrowed(v_as_816_, v_i_818_);
                v___x_845_ = lean_array_fget(v_array_833_, v_start_834_);
                v___x_846_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_847_ = lean_nat_add(v_start_834_, v___x_846_);
                crate::leanh::lean_dec(v_start_834_);
                if v_isShared_843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_842_, 1, v___x_847_);
                    v___x_849_ = v___x_842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_858_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 0, v_array_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_858_, 2, v_stop_835_);
                    v___x_849_ = v_reuseFailAlloc_858_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_850_ = (crate::leanh::lean_unbox(v_a_844_) as u8);
                if v___x_850_ == 0 {
                    crate::leanh::lean_dec(v___x_845_);
                    if v_isShared_832_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_831_, 1, v___x_849_);
                        v___x_852_ = v___x_831_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v_fst_829_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_849_);
                        v___x_852_ = v_reuseFailAlloc_853_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_854_ = lean_array_push(v_fst_829_, v___x_845_);
                    if v_isShared_832_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_831_, 1, v___x_849_);
                        crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_854_);
                        v___x_856_ = v___x_831_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_849_);
                        v___x_856_ = v_reuseFailAlloc_857_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_822_ = v___x_852_;
                state = 1;
                continue;
            }
            7 => {
                v_a_822_ = v___x_856_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg___boxed(
    mut v_as_864_: *mut crate::leanh::LeanObject,
    mut v_sz_865_: *mut crate::leanh::LeanObject,
    mut v_i_866_: *mut crate::leanh::LeanObject,
    mut v_b_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_869_: usize = 0;
    let mut v_i_boxed_870_: usize = 0;
    let mut v_res_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_869_ = crate::leanh::lean_unbox_usize(v_sz_865_);
    crate::leanh::lean_dec(v_sz_865_);
    v_i_boxed_870_ = crate::leanh::lean_unbox_usize(v_i_866_);
    crate::leanh::lean_dec(v_i_866_);
    v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_864_, v_sz_boxed_869_, v_i_boxed_870_, v_b_867_);
    crate::leanh::lean_dec_ref(v_as_864_);
    return v_res_871_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_x_873_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_874_: u8 = 0;
    let mut v_key_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_873_) == 0 {
                    v___x_874_ = 0;
                    return v___x_874_;
                } else {
                    v_key_875_ = crate::leanh::lean_ctor_get(v_x_873_, 0);
                    v_tail_876_ = crate::leanh::lean_ctor_get(v_x_873_, 2);
                    v___x_877_ = l_Lean_instBEqFVarId_beq(v_key_875_, v_a_872_);
                    if v___x_877_ == 0 {
                        v_x_873_ = v_tail_876_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_877_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg___boxed(
    mut v_a_879_: *mut crate::leanh::LeanObject,
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_881_: u8 = 0;
    let mut v_r_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_879_, v_x_880_);
    crate::leanh::lean_dec(v_x_880_);
    crate::leanh::lean_dec(v_a_879_);
    v_r_882_ = crate::leanh::lean_box((v_res_881_) as usize);
    return v_r_882_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(
    mut v_m_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u64 = 0;
    let mut v___x_888_: u64 = 0;
    let mut v___x_889_: u64 = 0;
    let mut v_fold_890_: u64 = 0;
    let mut v___x_891_: u64 = 0;
    let mut v___x_892_: u64 = 0;
    let mut v___x_893_: u64 = 0;
    let mut v___x_894_: usize = 0;
    let mut v___x_895_: usize = 0;
    let mut v___x_896_: usize = 0;
    let mut v___x_897_: usize = 0;
    let mut v___x_898_: usize = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u8 = 0;
    v_buckets_885_ = crate::leanh::lean_ctor_get(v_m_883_, 1);
    v___x_886_ = lean_array_get_size(v_buckets_885_);
    v___x_887_ = l_Lean_instHashableFVarId_hash(v_a_884_);
    v___x_888_ = 32u64;
    v___x_889_ = lean_uint64_shift_right(v___x_887_, v___x_888_);
    v_fold_890_ = lean_uint64_xor(v___x_887_, v___x_889_);
    v___x_891_ = 16u64;
    v___x_892_ = lean_uint64_shift_right(v_fold_890_, v___x_891_);
    v___x_893_ = lean_uint64_xor(v_fold_890_, v___x_892_);
    v___x_894_ = lean_uint64_to_usize(v___x_893_);
    v___x_895_ = lean_usize_of_nat(v___x_886_);
    v___x_896_ = 1usize;
    v___x_897_ = lean_usize_sub(v___x_895_, v___x_896_);
    v___x_898_ = lean_usize_land(v___x_894_, v___x_897_);
    v___x_899_ = lean_array_uget_borrowed(v_buckets_885_, v___x_898_);
    v___x_900_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_884_, v___x_899_);
    return v___x_900_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(
    mut v_m_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_903_: u8 = 0;
    let mut v_r_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_901_, v_a_902_);
    crate::leanh::lean_dec(v_a_902_);
    crate::leanh::lean_dec_ref(v_m_901_);
    v_r_904_ = crate::leanh::lean_box((v_res_903_) as usize);
    return v_r_904_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(
    mut v_as_905_: *mut crate::leanh::LeanObject,
    mut v_sz_906_: usize,
    mut v_i_907_: usize,
    mut v_b_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: usize = 0;
    let mut v___x_914_: usize = 0;
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_922_: u8 = 0;
    let mut v_fst_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v_a_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: u8 = 0;
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_945_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_916_ = lean_usize_dec_lt(v_i_907_, v_sz_906_);
                if v___x_916_ == 0 {
                    v___x_917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_917_, 0, v_b_908_);
                    return v___x_917_;
                } else {
                    v_snd_918_ = crate::leanh::lean_ctor_get(v_b_908_, 1);
                    v_fst_919_ = crate::leanh::lean_ctor_get(v_b_908_, 0);
                    v_isSharedCheck_961_ = (!crate::leanh::lean_is_exclusive(v_b_908_)) as u8;
                    if v_isSharedCheck_961_ == 0 {
                        v___x_921_ = v_b_908_;
                        v_isShared_922_ = v_isSharedCheck_961_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_918_);
                        crate::leanh::lean_inc(v_fst_919_);
                        crate::leanh::lean_dec(v_b_908_);
                        v___x_921_ = crate::leanh::lean_box(0);
                        v_isShared_922_ = v_isSharedCheck_961_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_913_ = 1usize;
                v___x_914_ = lean_usize_add(v_i_907_, v___x_913_);
                v_i_907_ = v___x_914_;
                v_b_908_ = v_a_912_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_923_ = crate::leanh::lean_ctor_get(v_snd_918_, 0);
                v_snd_924_ = crate::leanh::lean_ctor_get(v_snd_918_, 1);
                v_isSharedCheck_960_ = (!crate::leanh::lean_is_exclusive(v_snd_918_)) as u8;
                if v_isSharedCheck_960_ == 0 {
                    v___x_926_ = v_snd_918_;
                    v_isShared_927_ = v_isSharedCheck_960_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_924_);
                    crate::leanh::lean_inc(v_fst_923_);
                    crate::leanh::lean_dec(v_snd_918_);
                    v___x_926_ = crate::leanh::lean_box(0);
                    v_isShared_927_ = v_isSharedCheck_960_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_928_ = lean_array_uget_borrowed(v_as_905_, v_i_907_);
                v_fvarId_929_ = crate::leanh::lean_ctor_get(v_a_928_, 0);
                v_type_930_ = crate::leanh::lean_ctor_get(v_a_928_, 2);
                v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_fst_919_, v_fvarId_929_);
                if v___x_931_ == 0 {
                    v___x_932_ = 0;
                    v___x_933_ =
                        l_Lean_Compiler_LCNF_eraseParam___redArg(v___x_932_, v_a_928_, v___y_909_);
                    if crate::leanh::lean_obj_tag(v___x_933_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_933_, 1);
                        v___x_934_ = crate::leanh::lean_box((v___x_931_) as usize);
                        v___x_935_ = lean_array_push(v_fst_923_, v___x_934_);
                        if v_isShared_927_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_935_);
                            v___x_937_ = v___x_926_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 1, v_snd_924_);
                            v___x_937_ = v_reuseFailAlloc_941_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_926_);
                        crate::leanh::lean_dec(v_snd_924_);
                        crate::leanh::lean_dec(v_fst_923_);
                        crate::leanh::lean_del_object(v___x_921_);
                        crate::leanh::lean_dec(v_fst_919_);
                        v_a_942_ = crate::leanh::lean_ctor_get(v___x_933_, 0);
                        v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v___x_933_)) as u8;
                        if v_isSharedCheck_949_ == 0 {
                            v___x_944_ = v___x_933_;
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_942_);
                            crate::leanh::lean_dec(v___x_933_);
                            v___x_944_ = crate::leanh::lean_box(0);
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_type_930_);
                    v___x_950_ =
                        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(
                            v_type_930_,
                            v_fst_919_,
                        );
                    v___x_951_ = crate::leanh::lean_box((v___x_931_) as usize);
                    v___x_952_ = lean_array_push(v_fst_923_, v___x_951_);
                    crate::leanh::lean_inc(v_a_928_);
                    v___x_953_ = lean_array_push(v_snd_924_, v_a_928_);
                    if v_isShared_927_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_926_, 1, v___x_953_);
                        crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_952_);
                        v___x_955_ = v___x_926_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_953_);
                        v___x_955_ = v_reuseFailAlloc_959_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_921_, 1, v___x_937_);
                    v___x_939_ = v___x_921_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v_fst_919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_937_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_912_ = v___x_939_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_945_ == 0 {
                    v___x_947_ = v___x_944_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
                    v___x_947_ = v_reuseFailAlloc_948_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_947_;
            }
            8 => {
                if v_isShared_922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_921_, 1, v___x_955_);
                    crate::leanh::lean_ctor_set(v___x_921_, 0, v___x_950_);
                    v___x_957_ = v___x_921_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
                    v___x_957_ = v_reuseFailAlloc_958_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_912_ = v___x_957_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(
    mut v_as_962_: *mut crate::leanh::LeanObject,
    mut v_sz_963_: *mut crate::leanh::LeanObject,
    mut v_i_964_: *mut crate::leanh::LeanObject,
    mut v_b_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_968_: usize = 0;
    let mut v_i_boxed_969_: usize = 0;
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_968_ = crate::leanh::lean_unbox_usize(v_sz_963_);
    crate::leanh::lean_dec(v_sz_963_);
    v_i_boxed_969_ = crate::leanh::lean_unbox_usize(v_i_964_);
    crate::leanh::lean_dec(v_i_964_);
    v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_962_, v_sz_boxed_968_, v_i_boxed_969_, v_b_965_, v___y_966_);
    crate::leanh::lean_dec(v___y_966_);
    crate::leanh::lean_dec_ref(v_as_962_);
    return v_res_970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
    mut v_code_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___y_992_: u8 = 0;
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1002_: u8 = 0;
    let mut v_unused_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: usize = 0;
    let mut v___x_1010_: u8 = 0;
    let mut v___x_1011_: usize = 0;
    let mut v___x_1012_: u8 = 0;
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v_decl_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1028_: u8 = 0;
    let mut v___y_1030_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_unused_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: usize = 0;
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: usize = 0;
    let mut v___x_1050_: usize = 0;
    let mut v___x_1051_: u8 = 0;
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_a_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_decl_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1074_: usize = 0;
    let mut v___x_1075_: usize = 0;
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_a_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1120_: u8 = 0;
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut v_a_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_unused_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1142_: u8 = 0;
    let mut v___y_1144_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut v_unused_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: usize = 0;
    let mut v___x_1161_: usize = 0;
    let mut v___x_1162_: u8 = 0;
    let mut v___x_1163_: usize = 0;
    let mut v___x_1164_: usize = 0;
    let mut v___x_1165_: u8 = 0;
    let mut v_isSharedCheck_1166_: u8 = 0;
    let mut v_a_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1174_: u8 = 0;
    let mut v_a_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v_fvarId_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v_val_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1195_: usize = 0;
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v_fst_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1209_: u8 = 0;
    let mut v_a_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_unused_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1236_: usize = 0;
    let mut v___x_1237_: usize = 0;
    let mut v___x_1238_: u8 = 0;
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_unused_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1264_: u8 = 0;
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_977_) {
                0 => {
                    v_decl_984_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                    v_k_985_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                    crate::leanh::lean_inc_ref(v_k_985_);
                    v___x_986_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                        v_k_985_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_986_) == 0 {
                        v_a_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                        v_isSharedCheck_1013_ =
                            (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                        if v_isSharedCheck_1013_ == 0 {
                            v___x_989_ = v___x_986_;
                            v_isShared_990_ = v_isSharedCheck_1013_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_987_);
                            crate::leanh::lean_dec(v___x_986_);
                            v___x_989_ = crate::leanh::lean_box(0);
                            v_isShared_990_ = v_isSharedCheck_1013_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                        return v___x_986_;
                    }
                }
                1 => {
                    v_decl_1014_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                    v_k_1015_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                    v_params_1016_ = crate::leanh::lean_ctor_get(v_decl_1014_, 2);
                    v_type_1017_ = crate::leanh::lean_ctor_get(v_decl_1014_, 3);
                    v_value_1018_ = crate::leanh::lean_ctor_get(v_decl_1014_, 4);
                    crate::leanh::lean_inc_ref(v_value_1018_);
                    v___x_1019_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                        v_value_1018_,
                        v_a_978_,
                        v_a_979_,
                        v_a_980_,
                        v_a_981_,
                        v_a_982_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1019_) == 0 {
                        v_a_1020_ = crate::leanh::lean_ctor_get(v___x_1019_, 0);
                        crate::leanh::lean_inc(v_a_1020_);
                        crate::leanh::lean_dec_ref_known(v___x_1019_, 1);
                        v___x_1021_ = 0;
                        crate::leanh::lean_inc_ref(v_params_1016_);
                        crate::leanh::lean_inc_ref(v_type_1017_);
                        crate::leanh::lean_inc_ref(v_decl_1014_);
                        v___x_1022_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1021_, v_decl_1014_, v_type_1017_, v_params_1016_, v_a_1020_, v_a_980_);
                        if crate::leanh::lean_obj_tag(v___x_1022_) == 0 {
                            v_a_1023_ = crate::leanh::lean_ctor_get(v___x_1022_, 0);
                            crate::leanh::lean_inc(v_a_1023_);
                            crate::leanh::lean_dec_ref_known(v___x_1022_, 1);
                            crate::leanh::lean_inc_ref(v_k_1015_);
                            v___x_1024_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                                v_k_1015_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1024_) == 0 {
                                v_a_1025_ = crate::leanh::lean_ctor_get(v___x_1024_, 0);
                                v_isSharedCheck_1052_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1024_)) as u8;
                                if v_isSharedCheck_1052_ == 0 {
                                    v___x_1027_ = v___x_1024_;
                                    v_isShared_1028_ = v_isSharedCheck_1052_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1025_);
                                    crate::leanh::lean_dec(v___x_1024_);
                                    v___x_1027_ = crate::leanh::lean_box(0);
                                    v_isShared_1028_ = v_isSharedCheck_1052_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1023_);
                                crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                                return v___x_1024_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                            v_a_1053_ = crate::leanh::lean_ctor_get(v___x_1022_, 0);
                            v_isSharedCheck_1060_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1022_)) as u8;
                            if v_isSharedCheck_1060_ == 0 {
                                v___x_1055_ = v___x_1022_;
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1053_);
                                crate::leanh::lean_dec(v___x_1022_);
                                v___x_1055_ = crate::leanh::lean_box(0);
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                        return v___x_1019_;
                    }
                }
                2 => {
                    v_decl_1061_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                    v_k_1062_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                    v_params_1063_ = crate::leanh::lean_ctor_get(v_decl_1061_, 2);
                    v_type_1064_ = crate::leanh::lean_ctor_get(v_decl_1061_, 3);
                    v_value_1065_ = crate::leanh::lean_ctor_get(v_decl_1061_, 4);
                    crate::leanh::lean_inc_ref(v_value_1065_);
                    v___x_1066_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                        v_value_1065_,
                        v_a_978_,
                        v_a_979_,
                        v_a_980_,
                        v_a_981_,
                        v_a_982_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1066_) == 0 {
                        v_a_1067_ = crate::leanh::lean_ctor_get(v___x_1066_, 0);
                        crate::leanh::lean_inc_n(v_a_1067_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1066_, 1);
                        v___x_1068_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                        v___x_1069_ = 0;
                        v___x_1070_ = l_Lean_Compiler_LCNF_Code_collectUsed(
                            v___x_1069_,
                            v_a_1067_,
                            v___x_1068_,
                        );
                        crate::leanh::lean_inc_ref(v_params_1063_);
                        v___x_1071_ = l_Array_reverse___redArg(v_params_1063_);
                        v___x_1072_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__1;
                        v___x_1073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1070_);
                        crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1072_);
                        v_sz_1074_ = lean_array_size(v___x_1071_);
                        v___x_1075_ = 0usize;
                        v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v___x_1071_, v_sz_1074_, v___x_1075_, v___x_1073_, v_a_980_);
                        crate::leanh::lean_dec_ref(v___x_1071_);
                        if crate::leanh::lean_obj_tag(v___x_1076_) == 0 {
                            v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1076_, 0);
                            crate::leanh::lean_inc(v_a_1077_);
                            crate::leanh::lean_dec_ref_known(v___x_1076_, 1);
                            v_snd_1078_ = crate::leanh::lean_ctor_get(v_a_1077_, 1);
                            crate::leanh::lean_inc(v_snd_1078_);
                            crate::leanh::lean_dec(v_a_1077_);
                            v_fst_1079_ = crate::leanh::lean_ctor_get(v_snd_1078_, 0);
                            crate::leanh::lean_inc(v_fst_1079_);
                            v_snd_1080_ = crate::leanh::lean_ctor_get(v_snd_1078_, 1);
                            crate::leanh::lean_inc(v_snd_1080_);
                            crate::leanh::lean_dec(v_snd_1078_);
                            v___x_1081_ = l_Array_reverse___redArg(v_snd_1080_);
                            v___x_1082_ = lean_array_get_size(v___x_1081_);
                            v___x_1083_ = lean_array_get_size(v_params_1063_);
                            v___x_1084_ = lean_nat_dec_eq(v___x_1082_, v___x_1083_);
                            if v___x_1084_ == 0 {
                                crate::leanh::lean_inc_ref(v_k_1062_);
                                crate::leanh::lean_inc_ref(v_decl_1061_);
                                v_isSharedCheck_1133_ =
                                    (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                                if v_isSharedCheck_1133_ == 0 {
                                    v_unused_1134_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                                    crate::leanh::lean_dec(v_unused_1134_);
                                    v_unused_1135_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                                    crate::leanh::lean_dec(v_unused_1135_);
                                    v___x_1086_ = v_code_977_;
                                    v_isShared_1087_ = v_isSharedCheck_1133_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_code_977_);
                                    v___x_1086_ = crate::leanh::lean_box(0);
                                    v_isShared_1087_ = v_isSharedCheck_1133_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1081_);
                                crate::leanh::lean_dec(v_fst_1079_);
                                crate::leanh::lean_inc_ref(v_params_1063_);
                                crate::leanh::lean_inc_ref(v_type_1064_);
                                crate::leanh::lean_inc_ref(v_decl_1061_);
                                v___x_1136_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1069_, v_decl_1061_, v_type_1064_, v_params_1063_, v_a_1067_, v_a_980_);
                                if crate::leanh::lean_obj_tag(v___x_1136_) == 0 {
                                    v_a_1137_ = crate::leanh::lean_ctor_get(v___x_1136_, 0);
                                    crate::leanh::lean_inc(v_a_1137_);
                                    crate::leanh::lean_dec_ref_known(v___x_1136_, 1);
                                    crate::leanh::lean_inc_ref(v_k_1062_);
                                    v___x_1138_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                                        v_k_1062_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1138_) == 0 {
                                        v_a_1139_ = crate::leanh::lean_ctor_get(v___x_1138_, 0);
                                        v_isSharedCheck_1166_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1138_)) as u8;
                                        if v_isSharedCheck_1166_ == 0 {
                                            v___x_1141_ = v___x_1138_;
                                            v_isShared_1142_ = v_isSharedCheck_1166_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1139_);
                                            crate::leanh::lean_dec(v___x_1138_);
                                            v___x_1141_ = crate::leanh::lean_box(0);
                                            v_isShared_1142_ = v_isSharedCheck_1166_;
                                            state = 25;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1137_);
                                        crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                                        return v___x_1138_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                                    v_a_1167_ = crate::leanh::lean_ctor_get(v___x_1136_, 0);
                                    v_isSharedCheck_1174_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1136_)) as u8;
                                    if v_isSharedCheck_1174_ == 0 {
                                        v___x_1169_ = v___x_1136_;
                                        v_isShared_1170_ = v_isSharedCheck_1174_;
                                        state = 31;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1167_);
                                        crate::leanh::lean_dec(v___x_1136_);
                                        v___x_1169_ = crate::leanh::lean_box(0);
                                        v_isShared_1170_ = v_isSharedCheck_1174_;
                                        state = 31;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1067_);
                            crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                            v_a_1175_ = crate::leanh::lean_ctor_get(v___x_1076_, 0);
                            v_isSharedCheck_1182_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1076_)) as u8;
                            if v_isSharedCheck_1182_ == 0 {
                                v___x_1177_ = v___x_1076_;
                                v_isShared_1178_ = v_isSharedCheck_1182_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1175_);
                                crate::leanh::lean_dec(v___x_1076_);
                                v___x_1177_ = crate::leanh::lean_box(0);
                                v_isShared_1178_ = v_isSharedCheck_1182_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_977_, 2);
                        return v___x_1066_;
                    }
                }
                3 => {
                    v_fvarId_1183_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                    v_args_1184_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                    v___x_1185_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_a_978_, v_fvarId_1183_);
                    if crate::leanh::lean_obj_tag(v___x_1185_) == 1 {
                        crate::leanh::lean_inc_ref(v_args_1184_);
                        crate::leanh::lean_inc(v_fvarId_1183_);
                        v_isSharedCheck_1218_ =
                            (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                        if v_isSharedCheck_1218_ == 0 {
                            v_unused_1219_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                            crate::leanh::lean_dec(v_unused_1219_);
                            v_unused_1220_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                            crate::leanh::lean_dec(v_unused_1220_);
                            v___x_1187_ = v_code_977_;
                            v_isShared_1188_ = v_isSharedCheck_1218_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_977_);
                            v___x_1187_ = crate::leanh::lean_box(0);
                            v_isShared_1188_ = v_isSharedCheck_1218_;
                            state = 35;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1185_);
                        v___x_1221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1221_, 0, v_code_977_);
                        return v___x_1221_;
                    }
                }
                4 => {
                    v_cases_1222_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                    crate::leanh::lean_inc_ref(v_cases_1222_);
                    v_typeName_1223_ = crate::leanh::lean_ctor_get(v_cases_1222_, 0);
                    v_resultType_1224_ = crate::leanh::lean_ctor_get(v_cases_1222_, 1);
                    v_discr_1225_ = crate::leanh::lean_ctor_get(v_cases_1222_, 2);
                    v_alts_1226_ = crate::leanh::lean_ctor_get(v_cases_1222_, 3);
                    v_isSharedCheck_1265_ = (!crate::leanh::lean_is_exclusive(v_cases_1222_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1228_ = v_cases_1222_;
                        v_isShared_1229_ = v_isSharedCheck_1265_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_1226_);
                        crate::leanh::lean_inc(v_discr_1225_);
                        crate::leanh::lean_inc(v_resultType_1224_);
                        crate::leanh::lean_inc(v_typeName_1223_);
                        crate::leanh::lean_dec(v_cases_1222_);
                        v___x_1228_ = crate::leanh::lean_box(0);
                        v_isShared_1229_ = v_isSharedCheck_1265_;
                        state = 41;
                        continue;
                    }
                }
                _ => {
                    v___x_1266_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1266_, 0, v_code_977_);
                    return v___x_1266_;
                }
            },
            1 => {
                v___x_1008_ = lean_ptr_addr(v_k_985_);
                v___x_1009_ = lean_ptr_addr(v_a_987_);
                v___x_1010_ = lean_usize_dec_eq(v___x_1008_, v___x_1009_);
                if v___x_1010_ == 0 {
                    v___y_992_ = v___x_1010_;
                    state = 2;
                    continue;
                } else {
                    v___x_1011_ = lean_ptr_addr(v_decl_984_);
                    v___x_1012_ = lean_usize_dec_eq(v___x_1011_, v___x_1011_);
                    v___y_992_ = v___x_1012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_992_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_984_);
                    v_isSharedCheck_1002_ = (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                    if v_isSharedCheck_1002_ == 0 {
                        v_unused_1003_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                        crate::leanh::lean_dec(v_unused_1003_);
                        v_unused_1004_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                        crate::leanh::lean_dec(v_unused_1004_);
                        v___x_994_ = v_code_977_;
                        v_isShared_995_ = v_isSharedCheck_1002_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_977_);
                        v___x_994_ = crate::leanh::lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_1002_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_987_);
                    if v_isShared_990_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_989_, 0, v_code_977_);
                        v___x_1006_ = v___x_989_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_code_977_);
                        v___x_1006_ = v_reuseFailAlloc_1007_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_994_, 1, v_a_987_);
                    v___x_997_ = v___x_994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_decl_984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_987_);
                    v___x_997_ = v_reuseFailAlloc_1001_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_997_);
                    v___x_999_ = v___x_989_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
                    v___x_999_ = v_reuseFailAlloc_1000_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_999_;
            }
            6 => {
                return v___x_1006_;
            }
            7 => {
                v___x_1046_ = lean_ptr_addr(v_k_1015_);
                v___x_1047_ = lean_ptr_addr(v_a_1025_);
                v___x_1048_ = lean_usize_dec_eq(v___x_1046_, v___x_1047_);
                if v___x_1048_ == 0 {
                    v___y_1030_ = v___x_1048_;
                    state = 8;
                    continue;
                } else {
                    v___x_1049_ = lean_ptr_addr(v_decl_1014_);
                    v___x_1050_ = lean_ptr_addr(v_a_1023_);
                    v___x_1051_ = lean_usize_dec_eq(v___x_1049_, v___x_1050_);
                    v___y_1030_ = v___x_1051_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_1030_ == 0 {
                    v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                    if v_isSharedCheck_1040_ == 0 {
                        v_unused_1041_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                        crate::leanh::lean_dec(v_unused_1041_);
                        v_unused_1042_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                        crate::leanh::lean_dec(v_unused_1042_);
                        v___x_1032_ = v_code_977_;
                        v_isShared_1033_ = v_isSharedCheck_1040_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_977_);
                        v___x_1032_ = crate::leanh::lean_box(0);
                        v_isShared_1033_ = v_isSharedCheck_1040_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1025_);
                    crate::leanh::lean_dec(v_a_1023_);
                    if v_isShared_1028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1027_, 0, v_code_977_);
                        v___x_1044_ = v___x_1027_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_code_977_);
                        v___x_1044_ = v_reuseFailAlloc_1045_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1032_, 1, v_a_1025_);
                    crate::leanh::lean_ctor_set(v___x_1032_, 0, v_a_1023_);
                    v___x_1035_ = v___x_1032_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1025_);
                    v___x_1035_ = v_reuseFailAlloc_1039_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1035_);
                    v___x_1037_ = v___x_1027_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1037_;
            }
            12 => {
                return v___x_1044_;
            }
            13 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1058_;
            }
            15 => {
                crate::leanh::lean_inc(v_a_1067_);
                v___x_1088_ = l_Lean_Compiler_LCNF_Code_inferType(
                    v___x_1069_,
                    v_a_1067_,
                    v_a_979_,
                    v_a_980_,
                    v_a_981_,
                    v_a_982_,
                );
                if crate::leanh::lean_obj_tag(v___x_1088_) == 0 {
                    v_a_1089_ = crate::leanh::lean_ctor_get(v___x_1088_, 0);
                    crate::leanh::lean_inc(v_a_1089_);
                    crate::leanh::lean_dec_ref_known(v___x_1088_, 1);
                    crate::leanh::lean_inc_ref(v___x_1081_);
                    v___x_1090_ = l_Lean_Compiler_LCNF_mkForallParams(
                        v___x_1069_,
                        v___x_1081_,
                        v_a_1089_,
                        v_a_979_,
                        v_a_980_,
                        v_a_981_,
                        v_a_982_,
                    );
                    crate::leanh::lean_dec(v_a_1089_);
                    if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                        v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        crate::leanh::lean_inc(v_a_1091_);
                        crate::leanh::lean_dec_ref_known(v___x_1090_, 1);
                        v___x_1092_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1069_, v_decl_1061_, v_a_1091_, v___x_1081_, v_a_1067_, v_a_980_);
                        if crate::leanh::lean_obj_tag(v___x_1092_) == 0 {
                            v_a_1093_ = crate::leanh::lean_ctor_get(v___x_1092_, 0);
                            crate::leanh::lean_inc(v_a_1093_);
                            crate::leanh::lean_dec_ref_known(v___x_1092_, 1);
                            v_fvarId_1094_ = crate::leanh::lean_ctor_get(v_a_1093_, 0);
                            v___x_1095_ = l_Array_reverse___redArg(v_fst_1079_);
                            crate::leanh::lean_inc(v_a_978_);
                            crate::leanh::lean_inc(v_fvarId_1094_);
                            v___x_1096_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1094_, v___x_1095_, v_a_978_);
                            v___x_1097_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                                v_k_1062_,
                                v___x_1096_,
                                v_a_979_,
                                v_a_980_,
                                v_a_981_,
                                v_a_982_,
                            );
                            crate::leanh::lean_dec(v___x_1096_);
                            if crate::leanh::lean_obj_tag(v___x_1097_) == 0 {
                                v_a_1098_ = crate::leanh::lean_ctor_get(v___x_1097_, 0);
                                v_isSharedCheck_1108_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1097_)) as u8;
                                if v_isSharedCheck_1108_ == 0 {
                                    v___x_1100_ = v___x_1097_;
                                    v_isShared_1101_ = v_isSharedCheck_1108_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1098_);
                                    crate::leanh::lean_dec(v___x_1097_);
                                    v___x_1100_ = crate::leanh::lean_box(0);
                                    v_isShared_1101_ = v_isSharedCheck_1108_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1093_);
                                crate::leanh::lean_del_object(v___x_1086_);
                                return v___x_1097_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1086_);
                            crate::leanh::lean_dec(v_fst_1079_);
                            crate::leanh::lean_dec_ref(v_k_1062_);
                            v_a_1109_ = crate::leanh::lean_ctor_get(v___x_1092_, 0);
                            v_isSharedCheck_1116_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1092_)) as u8;
                            if v_isSharedCheck_1116_ == 0 {
                                v___x_1111_ = v___x_1092_;
                                v_isShared_1112_ = v_isSharedCheck_1116_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1109_);
                                crate::leanh::lean_dec(v___x_1092_);
                                v___x_1111_ = crate::leanh::lean_box(0);
                                v_isShared_1112_ = v_isSharedCheck_1116_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1086_);
                        crate::leanh::lean_dec_ref(v___x_1081_);
                        crate::leanh::lean_dec(v_fst_1079_);
                        crate::leanh::lean_dec(v_a_1067_);
                        crate::leanh::lean_dec_ref(v_k_1062_);
                        crate::leanh::lean_dec_ref(v_decl_1061_);
                        v_a_1117_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        v_isSharedCheck_1124_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                        if v_isSharedCheck_1124_ == 0 {
                            v___x_1119_ = v___x_1090_;
                            v_isShared_1120_ = v_isSharedCheck_1124_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1117_);
                            crate::leanh::lean_dec(v___x_1090_);
                            v___x_1119_ = crate::leanh::lean_box(0);
                            v_isShared_1120_ = v_isSharedCheck_1124_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1086_);
                    crate::leanh::lean_dec_ref(v___x_1081_);
                    crate::leanh::lean_dec(v_fst_1079_);
                    crate::leanh::lean_dec(v_a_1067_);
                    crate::leanh::lean_dec_ref(v_k_1062_);
                    crate::leanh::lean_dec_ref(v_decl_1061_);
                    v_a_1125_ = crate::leanh::lean_ctor_get(v___x_1088_, 0);
                    v_isSharedCheck_1132_ = (!crate::leanh::lean_is_exclusive(v___x_1088_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1127_ = v___x_1088_;
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1125_);
                        crate::leanh::lean_dec(v___x_1088_);
                        v___x_1127_ = crate::leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 23;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_1087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1086_, 1, v_a_1098_);
                    crate::leanh::lean_ctor_set(v___x_1086_, 0, v_a_1093_);
                    v___x_1103_ = v___x_1086_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_a_1098_);
                    v___x_1103_ = v_reuseFailAlloc_1107_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1103_);
                    v___x_1105_ = v___x_1100_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
                    v___x_1105_ = v_reuseFailAlloc_1106_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1105_;
            }
            19 => {
                if v_isShared_1112_ == 0 {
                    v___x_1114_ = v___x_1111_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
                    v___x_1114_ = v_reuseFailAlloc_1115_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1114_;
            }
            21 => {
                if v_isShared_1120_ == 0 {
                    v___x_1122_ = v___x_1119_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
                    v___x_1122_ = v_reuseFailAlloc_1123_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1122_;
            }
            23 => {
                if v_isShared_1128_ == 0 {
                    v___x_1130_ = v___x_1127_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
                    v___x_1130_ = v_reuseFailAlloc_1131_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1130_;
            }
            25 => {
                v___x_1160_ = lean_ptr_addr(v_k_1062_);
                v___x_1161_ = lean_ptr_addr(v_a_1139_);
                v___x_1162_ = lean_usize_dec_eq(v___x_1160_, v___x_1161_);
                if v___x_1162_ == 0 {
                    v___y_1144_ = v___x_1162_;
                    state = 26;
                    continue;
                } else {
                    v___x_1163_ = lean_ptr_addr(v_decl_1061_);
                    v___x_1164_ = lean_ptr_addr(v_a_1137_);
                    v___x_1165_ = lean_usize_dec_eq(v___x_1163_, v___x_1164_);
                    v___y_1144_ = v___x_1165_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v___y_1144_ == 0 {
                    v_isSharedCheck_1154_ = (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                    if v_isSharedCheck_1154_ == 0 {
                        v_unused_1155_ = crate::leanh::lean_ctor_get(v_code_977_, 1);
                        crate::leanh::lean_dec(v_unused_1155_);
                        v_unused_1156_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                        crate::leanh::lean_dec(v_unused_1156_);
                        v___x_1146_ = v_code_977_;
                        v_isShared_1147_ = v_isSharedCheck_1154_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_977_);
                        v___x_1146_ = crate::leanh::lean_box(0);
                        v_isShared_1147_ = v_isSharedCheck_1154_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1139_);
                    crate::leanh::lean_dec(v_a_1137_);
                    if v_isShared_1142_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1141_, 0, v_code_977_);
                        v___x_1158_ = v___x_1141_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_1159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_code_977_);
                        v___x_1158_ = v_reuseFailAlloc_1159_;
                        state = 30;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_1147_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1146_, 1, v_a_1139_);
                    crate::leanh::lean_ctor_set(v___x_1146_, 0, v_a_1137_);
                    v___x_1149_ = v___x_1146_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_a_1139_);
                    v___x_1149_ = v_reuseFailAlloc_1153_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_1142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1141_, 0, v___x_1149_);
                    v___x_1151_ = v___x_1141_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
                    v___x_1151_ = v_reuseFailAlloc_1152_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1151_;
            }
            30 => {
                return v___x_1158_;
            }
            31 => {
                if v_isShared_1170_ == 0 {
                    v___x_1172_ = v___x_1169_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
                    v___x_1172_ = v_reuseFailAlloc_1173_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1172_;
            }
            33 => {
                if v_isShared_1178_ == 0 {
                    v___x_1180_ = v___x_1177_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
                    v___x_1180_ = v_reuseFailAlloc_1181_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_1180_;
            }
            35 => {
                v_val_1189_ = crate::leanh::lean_ctor_get(v___x_1185_, 0);
                crate::leanh::lean_inc(v_val_1189_);
                crate::leanh::lean_dec_ref_known(v___x_1185_, 1);
                v___x_1190_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1191_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce___closed__2;
                v___x_1192_ = lean_array_get_size(v_args_1184_);
                v___x_1193_ = l_Array_toSubarray___redArg(v_args_1184_, v___x_1190_, v___x_1192_);
                v___x_1194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1194_, 0, v___x_1191_);
                crate::leanh::lean_ctor_set(v___x_1194_, 1, v___x_1193_);
                v_sz_1195_ = lean_array_size(v_val_1189_);
                v___x_1196_ = 0usize;
                v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_val_1189_, v_sz_1195_, v___x_1196_, v___x_1194_);
                crate::leanh::lean_dec(v_val_1189_);
                if crate::leanh::lean_obj_tag(v___x_1197_) == 0 {
                    v_a_1198_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
                    v_isSharedCheck_1209_ = (!crate::leanh::lean_is_exclusive(v___x_1197_)) as u8;
                    if v_isSharedCheck_1209_ == 0 {
                        v___x_1200_ = v___x_1197_;
                        v_isShared_1201_ = v_isSharedCheck_1209_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1198_);
                        crate::leanh::lean_dec(v___x_1197_);
                        v___x_1200_ = crate::leanh::lean_box(0);
                        v_isShared_1201_ = v_isSharedCheck_1209_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1187_);
                    crate::leanh::lean_dec(v_fvarId_1183_);
                    v_a_1210_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
                    v_isSharedCheck_1217_ = (!crate::leanh::lean_is_exclusive(v___x_1197_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1212_ = v___x_1197_;
                        v_isShared_1213_ = v_isSharedCheck_1217_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1210_);
                        crate::leanh::lean_dec(v___x_1197_);
                        v___x_1212_ = crate::leanh::lean_box(0);
                        v_isShared_1213_ = v_isSharedCheck_1217_;
                        state = 39;
                        continue;
                    }
                }
            }
            36 => {
                v_fst_1202_ = crate::leanh::lean_ctor_get(v_a_1198_, 0);
                crate::leanh::lean_inc(v_fst_1202_);
                crate::leanh::lean_dec(v_a_1198_);
                if v_isShared_1188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1187_, 1, v_fst_1202_);
                    v___x_1204_ = v___x_1187_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1208_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_fvarId_1183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_fst_1202_);
                    v___x_1204_ = v_reuseFailAlloc_1208_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1204_);
                    v___x_1206_ = v___x_1200_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
                    v___x_1206_ = v_reuseFailAlloc_1207_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1206_;
            }
            39 => {
                if v_isShared_1213_ == 0 {
                    v___x_1215_ = v___x_1212_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
                    v___x_1215_ = v_reuseFailAlloc_1216_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_1215_;
            }
            41 => {
                v___x_1230_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_1226_);
                v___x_1231_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v___x_1230_, v_alts_1226_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
                if crate::leanh::lean_obj_tag(v___x_1231_) == 0 {
                    v_a_1232_ = crate::leanh::lean_ctor_get(v___x_1231_, 0);
                    v_isSharedCheck_1256_ = (!crate::leanh::lean_is_exclusive(v___x_1231_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v___x_1234_ = v___x_1231_;
                        v_isShared_1235_ = v_isSharedCheck_1256_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1232_);
                        crate::leanh::lean_dec(v___x_1231_);
                        v___x_1234_ = crate::leanh::lean_box(0);
                        v_isShared_1235_ = v_isSharedCheck_1256_;
                        state = 42;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1228_);
                    crate::leanh::lean_dec_ref(v_alts_1226_);
                    crate::leanh::lean_dec(v_discr_1225_);
                    crate::leanh::lean_dec_ref(v_resultType_1224_);
                    crate::leanh::lean_dec(v_typeName_1223_);
                    crate::leanh::lean_dec_ref_known(v_code_977_, 1);
                    v_a_1257_ = crate::leanh::lean_ctor_get(v___x_1231_, 0);
                    v_isSharedCheck_1264_ = (!crate::leanh::lean_is_exclusive(v___x_1231_)) as u8;
                    if v_isSharedCheck_1264_ == 0 {
                        v___x_1259_ = v___x_1231_;
                        v_isShared_1260_ = v_isSharedCheck_1264_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1257_);
                        crate::leanh::lean_dec(v___x_1231_);
                        v___x_1259_ = crate::leanh::lean_box(0);
                        v_isShared_1260_ = v_isSharedCheck_1264_;
                        state = 48;
                        continue;
                    }
                }
            }
            42 => {
                v___x_1236_ = lean_ptr_addr(v_alts_1226_);
                crate::leanh::lean_dec_ref(v_alts_1226_);
                v___x_1237_ = lean_ptr_addr(v_a_1232_);
                v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
                if v___x_1238_ == 0 {
                    v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v_code_977_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v_unused_1252_ = crate::leanh::lean_ctor_get(v_code_977_, 0);
                        crate::leanh::lean_dec(v_unused_1252_);
                        v___x_1240_ = v_code_977_;
                        v_isShared_1241_ = v_isSharedCheck_1251_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_977_);
                        v___x_1240_ = crate::leanh::lean_box(0);
                        v_isShared_1241_ = v_isSharedCheck_1251_;
                        state = 43;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1232_);
                    crate::leanh::lean_del_object(v___x_1228_);
                    crate::leanh::lean_dec(v_discr_1225_);
                    crate::leanh::lean_dec_ref(v_resultType_1224_);
                    crate::leanh::lean_dec(v_typeName_1223_);
                    if v_isShared_1235_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1234_, 0, v_code_977_);
                        v___x_1254_ = v___x_1234_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_1255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_code_977_);
                        v___x_1254_ = v_reuseFailAlloc_1255_;
                        state = 47;
                        continue;
                    }
                }
            }
            43 => {
                if v_isShared_1229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1228_, 3, v_a_1232_);
                    v___x_1243_ = v___x_1228_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_typeName_1223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_resultType_1224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_discr_1225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_a_1232_);
                    v___x_1243_ = v_reuseFailAlloc_1250_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1243_);
                    v___x_1245_ = v___x_1240_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1243_);
                    v___x_1245_ = v_reuseFailAlloc_1249_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1234_, 0, v___x_1245_);
                    v___x_1247_ = v___x_1234_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
                    v___x_1247_ = v_reuseFailAlloc_1248_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_1247_;
            }
            47 => {
                return v___x_1254_;
            }
            48 => {
                if v_isShared_1260_ == 0 {
                    v___x_1262_ = v___x_1259_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
                    v___x_1262_ = v_reuseFailAlloc_1263_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_1262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(
    mut v_i_1267_: *mut crate::leanh::LeanObject,
    mut v_as_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut v_code_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1275_ = lean_array_get_size(v_as_1268_);
                v___x_1276_ = lean_nat_dec_lt(v_i_1267_, v___x_1275_);
                if v___x_1276_ == 0 {
                    crate::leanh::lean_dec(v_i_1267_);
                    v___x_1277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v_as_1268_);
                    return v___x_1277_;
                } else {
                    v_a_1278_ = lean_array_fget_borrowed(v_as_1268_, v_i_1267_);
                    match crate::leanh::lean_obj_tag(v_a_1278_) {
                        0 => {
                            v_code_1302_ = crate::leanh::lean_ctor_get(v_a_1278_, 2);
                            crate::leanh::lean_inc_ref(v_code_1302_);
                            v___y_1280_ = v_code_1302_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1303_ = crate::leanh::lean_ctor_get(v_a_1278_, 1);
                            crate::leanh::lean_inc_ref(v_code_1303_);
                            v___y_1280_ = v_code_1303_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1304_ = crate::leanh::lean_ctor_get(v_a_1278_, 0);
                            crate::leanh::lean_inc_ref(v_code_1304_);
                            v___y_1280_ = v_code_1304_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1281_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
                    v___y_1280_,
                    v___y_1269_,
                    v___y_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                );
                if crate::leanh::lean_obj_tag(v___x_1281_) == 0 {
                    v_a_1282_ = crate::leanh::lean_ctor_get(v___x_1281_, 0);
                    crate::leanh::lean_inc(v_a_1282_);
                    crate::leanh::lean_dec_ref_known(v___x_1281_, 1);
                    crate::leanh::lean_inc(v_a_1278_);
                    v___x_1283_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1278_, v_a_1282_);
                    v___x_1284_ = lean_ptr_addr(v_a_1278_);
                    v___x_1285_ = lean_ptr_addr(v___x_1283_);
                    v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
                    if v___x_1286_ == 0 {
                        v___x_1287_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1288_ = lean_nat_add(v_i_1267_, v___x_1287_);
                        v___x_1289_ = lean_array_fset(v_as_1268_, v_i_1267_, v___x_1283_);
                        crate::leanh::lean_dec(v_i_1267_);
                        v_i_1267_ = v___x_1288_;
                        v_as_1268_ = v___x_1289_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1283_);
                        v___x_1291_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1292_ = lean_nat_add(v_i_1267_, v___x_1291_);
                        crate::leanh::lean_dec(v_i_1267_);
                        v_i_1267_ = v___x_1292_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_as_1268_);
                    crate::leanh::lean_dec(v_i_1267_);
                    v_a_1294_ = crate::leanh::lean_ctor_get(v___x_1281_, 0);
                    v_isSharedCheck_1301_ = (!crate::leanh::lean_is_exclusive(v___x_1281_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1296_ = v___x_1281_;
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1294_);
                        crate::leanh::lean_dec(v___x_1281_);
                        v___x_1296_ = crate::leanh::lean_box(0);
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1297_ == 0 {
                    v___x_1299_ = v___x_1296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
                    v___x_1299_ = v_reuseFailAlloc_1300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4___boxed(
    mut v_i_1305_: *mut crate::leanh::LeanObject,
    mut v_as_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__4(v_i_1305_, v_as_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
    crate::leanh::lean_dec(v___y_1311_);
    crate::leanh::lean_dec_ref(v___y_1310_);
    crate::leanh::lean_dec(v___y_1309_);
    crate::leanh::lean_dec_ref(v___y_1308_);
    crate::leanh::lean_dec(v___y_1307_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(
    mut v_code_1314_: *mut crate::leanh::LeanObject,
    mut v_a_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(
        v_code_1314_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
        v_a_1318_,
        v_a_1319_,
    );
    crate::leanh::lean_dec(v_a_1319_);
    crate::leanh::lean_dec_ref(v_a_1318_);
    crate::leanh::lean_dec(v_a_1317_);
    crate::leanh::lean_dec_ref(v_a_1316_);
    crate::leanh::lean_dec(v_a_1315_);
    return v_res_1321_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(
    mut v_00_u03b2_1322_: *mut crate::leanh::LeanObject,
    mut v_m_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1325_: u8 = 0;
    v___x_1325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(v_m_1323_, v_a_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(
    mut v_00_u03b2_1326_: *mut crate::leanh::LeanObject,
    mut v_m_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1329_: u8 = 0;
    let mut v_r_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(v_00_u03b2_1326_, v_m_1327_, v_a_1328_);
    crate::leanh::lean_dec(v_a_1328_);
    crate::leanh::lean_dec_ref(v_m_1327_);
    v_r_1330_ = crate::leanh::lean_box((v_res_1329_) as usize);
    return v_r_1330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(
    mut v_as_1331_: *mut crate::leanh::LeanObject,
    mut v_sz_1332_: usize,
    mut v_i_1333_: usize,
    mut v_b_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(v_as_1331_, v_sz_1332_, v_i_1333_, v_b_1334_, v___y_1337_);
    return v___x_1341_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(
    mut v_as_1342_: *mut crate::leanh::LeanObject,
    mut v_sz_1343_: *mut crate::leanh::LeanObject,
    mut v_i_1344_: *mut crate::leanh::LeanObject,
    mut v_b_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1352_: usize = 0;
    let mut v_i_boxed_1353_: usize = 0;
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1352_ = crate::leanh::lean_unbox_usize(v_sz_1343_);
    crate::leanh::lean_dec(v_sz_1343_);
    v_i_boxed_1353_ = crate::leanh::lean_unbox_usize(v_i_1344_);
    crate::leanh::lean_dec(v_i_1344_);
    v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(v_as_1342_, v_sz_boxed_1352_, v_i_boxed_1353_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
    crate::leanh::lean_dec(v___y_1350_);
    crate::leanh::lean_dec_ref(v___y_1349_);
    crate::leanh::lean_dec(v___y_1348_);
    crate::leanh::lean_dec_ref(v___y_1347_);
    crate::leanh::lean_dec(v___y_1346_);
    crate::leanh::lean_dec_ref(v_as_1342_);
    return v_res_1354_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(
    mut v_00_u03b4_1355_: *mut crate::leanh::LeanObject,
    mut v_t_1356_: *mut crate::leanh::LeanObject,
    mut v_k_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(v_t_1356_, v_k_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(
    mut v_00_u03b4_1359_: *mut crate::leanh::LeanObject,
    mut v_t_1360_: *mut crate::leanh::LeanObject,
    mut v_k_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(v_00_u03b4_1359_, v_t_1360_, v_k_1361_);
    crate::leanh::lean_dec(v_k_1361_);
    crate::leanh::lean_dec(v_t_1360_);
    return v_res_1362_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(
    mut v_as_1363_: *mut crate::leanh::LeanObject,
    mut v_sz_1364_: usize,
    mut v_i_1365_: usize,
    mut v_b_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___redArg(v_as_1363_, v_sz_1364_, v_i_1365_, v_b_1366_);
    return v___x_1373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(
    mut v_as_1374_: *mut crate::leanh::LeanObject,
    mut v_sz_1375_: *mut crate::leanh::LeanObject,
    mut v_i_1376_: *mut crate::leanh::LeanObject,
    mut v_b_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1384_: usize = 0;
    let mut v_i_boxed_1385_: usize = 0;
    let mut v_res_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1384_ = crate::leanh::lean_unbox_usize(v_sz_1375_);
    crate::leanh::lean_dec(v_sz_1375_);
    v_i_boxed_1385_ = crate::leanh::lean_unbox_usize(v_i_1376_);
    crate::leanh::lean_dec(v_i_1376_);
    v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(v_as_1374_, v_sz_boxed_1384_, v_i_boxed_1385_, v_b_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
    crate::leanh::lean_dec(v___y_1382_);
    crate::leanh::lean_dec_ref(v___y_1381_);
    crate::leanh::lean_dec(v___y_1380_);
    crate::leanh::lean_dec_ref(v___y_1379_);
    crate::leanh::lean_dec(v___y_1378_);
    crate::leanh::lean_dec_ref(v_as_1374_);
    return v_res_1386_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(
    mut v_00_u03b2_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_x_1389_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1390_: u8 = 0;
    v___x_1390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___redArg(v_a_1388_, v_x_1389_);
    return v___x_1390_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0___boxed(
    mut v_00_u03b2_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_x_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1394_: u8 = 0;
    let mut v_r_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0_spec__0(v_00_u03b2_1391_, v_a_1392_, v_x_1393_);
    crate::leanh::lean_dec(v_x_1393_);
    crate::leanh::lean_dec(v_a_1392_);
    v_r_1395_ = crate::leanh::lean_box((v_res_1394_) as usize);
    return v_r_1395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(
    mut v_f_1396_: *mut crate::leanh::LeanObject,
    mut v_v_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1412_: u8 = 0;
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_a_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_1397_) == 0 {
                    v_code_1404_ = crate::leanh::lean_ctor_get(v_v_1397_, 0);
                    v_isSharedCheck_1428_ = (!crate::leanh::lean_is_exclusive(v_v_1397_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1406_ = v_v_1397_;
                        v_isShared_1407_ = v_isSharedCheck_1428_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_1404_);
                        crate::leanh::lean_dec(v_v_1397_);
                        v___x_1406_ = crate::leanh::lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1428_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_1396_);
                    v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_v_1397_);
                    return v___x_1429_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1402_);
                crate::leanh::lean_inc_ref(v___y_1401_);
                crate::leanh::lean_inc(v___y_1400_);
                crate::leanh::lean_inc_ref(v___y_1399_);
                crate::leanh::lean_inc(v___y_1398_);
                v___x_1408_ = crate::leanh::lean_apply_7(
                    v_f_1396_,
                    v_code_1404_,
                    v___y_1398_,
                    v___y_1399_,
                    v___y_1400_,
                    v___y_1401_,
                    v___y_1402_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1408_) == 0 {
                    v_a_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                    v_isSharedCheck_1419_ = (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1419_ == 0 {
                        v___x_1411_ = v___x_1408_;
                        v_isShared_1412_ = v_isSharedCheck_1419_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1409_);
                        crate::leanh::lean_dec(v___x_1408_);
                        v___x_1411_ = crate::leanh::lean_box(0);
                        v_isShared_1412_ = v_isSharedCheck_1419_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1406_);
                    v_a_1420_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                    v_isSharedCheck_1427_ = (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1427_ == 0 {
                        v___x_1422_ = v___x_1408_;
                        v_isShared_1423_ = v_isSharedCheck_1427_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1420_);
                        crate::leanh::lean_dec(v___x_1408_);
                        v___x_1422_ = crate::leanh::lean_box(0);
                        v_isShared_1423_ = v_isSharedCheck_1427_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v_a_1409_);
                    v___x_1414_ = v___x_1406_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1409_);
                    v___x_1414_ = v_reuseFailAlloc_1418_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1412_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1411_, 0, v___x_1414_);
                    v___x_1416_ = v___x_1411_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
                    v___x_1416_ = v_reuseFailAlloc_1417_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1416_;
            }
            5 => {
                if v_isShared_1423_ == 0 {
                    v___x_1425_ = v___x_1422_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
                    v___x_1425_ = v_reuseFailAlloc_1426_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg___boxed(
    mut v_f_1430_: *mut crate::leanh::LeanObject,
    mut v_v_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1438_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_1430_, v_v_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
    crate::leanh::lean_dec(v___y_1436_);
    crate::leanh::lean_dec_ref(v___y_1435_);
    crate::leanh::lean_dec(v___y_1434_);
    crate::leanh::lean_dec_ref(v___y_1433_);
    crate::leanh::lean_dec(v___y_1432_);
    return v_res_1438_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(
    mut v_pu_1439_: u8,
    mut v_f_1440_: *mut crate::leanh::LeanObject,
    mut v_v_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v_f_1440_, v_v_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___boxed(
    mut v_pu_1449_: *mut crate::leanh::LeanObject,
    mut v_f_1450_: *mut crate::leanh::LeanObject,
    mut v_v_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1458_: u8 = 0;
    let mut v_res_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1458_ = (crate::leanh::lean_unbox(v_pu_1449_) as u8);
    v_res_1459_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(v_pu_boxed_1458_, v_f_1450_, v_v_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
    crate::leanh::lean_dec(v___y_1456_);
    crate::leanh::lean_dec_ref(v___y_1455_);
    crate::leanh::lean_dec(v___y_1454_);
    crate::leanh::lean_dec_ref(v___y_1453_);
    crate::leanh::lean_dec(v___y_1452_);
    return v_res_1459_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceJpArity(
    mut v_decl_1461_: *mut crate::leanh::LeanObject,
    mut v_a_1462_: *mut crate::leanh::LeanObject,
    mut v_a_1463_: *mut crate::leanh::LeanObject,
    mut v_a_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1469_: u8 = 0;
    let mut v_inlineAttr_x3f_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v_a_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_1467_ = crate::leanh::lean_ctor_get(v_decl_1461_, 0);
                v_value_1468_ = crate::leanh::lean_ctor_get(v_decl_1461_, 1);
                v_recursive_1469_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_1461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_1470_ = crate::leanh::lean_ctor_get(v_decl_1461_, 2);
                v_isSharedCheck_1496_ = (!crate::leanh::lean_is_exclusive(v_decl_1461_)) as u8;
                if v_isSharedCheck_1496_ == 0 {
                    v___x_1472_ = v_decl_1461_;
                    v_isShared_1473_ = v_isSharedCheck_1496_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_1470_);
                    crate::leanh::lean_inc(v_value_1468_);
                    crate::leanh::lean_inc(v_toSignature_1467_);
                    crate::leanh::lean_dec(v_decl_1461_);
                    v___x_1472_ = crate::leanh::lean_box(0);
                    v_isShared_1473_ = v_isSharedCheck_1496_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1474_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity___closed__0;
                v___x_1475_ = crate::leanh::lean_box(1);
                v___x_1476_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0___redArg(v___x_1474_, v_value_1468_, v___x_1475_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
                if crate::leanh::lean_obj_tag(v___x_1476_) == 0 {
                    v_a_1477_ = crate::leanh::lean_ctor_get(v___x_1476_, 0);
                    v_isSharedCheck_1487_ = (!crate::leanh::lean_is_exclusive(v___x_1476_)) as u8;
                    if v_isSharedCheck_1487_ == 0 {
                        v___x_1479_ = v___x_1476_;
                        v_isShared_1480_ = v_isSharedCheck_1487_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1477_);
                        crate::leanh::lean_dec(v___x_1476_);
                        v___x_1479_ = crate::leanh::lean_box(0);
                        v_isShared_1480_ = v_isSharedCheck_1487_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1472_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_1470_);
                    crate::leanh::lean_dec_ref(v_toSignature_1467_);
                    v_a_1488_ = crate::leanh::lean_ctor_get(v___x_1476_, 0);
                    v_isSharedCheck_1495_ = (!crate::leanh::lean_is_exclusive(v___x_1476_)) as u8;
                    if v_isSharedCheck_1495_ == 0 {
                        v___x_1490_ = v___x_1476_;
                        v_isShared_1491_ = v_isSharedCheck_1495_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1488_);
                        crate::leanh::lean_dec(v___x_1476_);
                        v___x_1490_ = crate::leanh::lean_box(0);
                        v_isShared_1491_ = v_isSharedCheck_1495_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1472_, 1, v_a_1477_);
                    v___x_1482_ = v___x_1472_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_toSignature_1467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_inlineAttr_x3f_1470_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1486_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_1469_,
                    );
                    v___x_1482_ = v_reuseFailAlloc_1486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1482_);
                    v___x_1484_ = v___x_1479_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1484_;
            }
            5 => {
                if v_isShared_1491_ == 0 {
                    v___x_1493_ = v___x_1490_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceJpArity___boxed(
    mut v_decl_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(
        v_decl_1497_,
        v_a_1498_,
        v_a_1499_,
        v_a_1500_,
        v_a_1501_,
    );
    crate::leanh::lean_dec(v_a_1501_);
    crate::leanh::lean_dec_ref(v_a_1500_);
    crate::leanh::lean_dec(v_a_1499_);
    crate::leanh::lean_dec_ref(v_a_1498_);
    return v_res_1503_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceJpArity___lam__0(
    mut v_phase_1508_: u8,
    mut v_h_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__1;
    v___x_1511_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0___closed__2;
    v___x_1512_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1513_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_1510_,
        v_phase_1508_,
        v___x_1511_,
        v___x_1512_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed(
    mut v_phase_1514_: *mut crate::leanh::LeanObject,
    mut v_h_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_1516_: u8 = 0;
    let mut v_res_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1516_ = (crate::leanh::lean_unbox(v_phase_1514_) as u8);
    v_res_1517_ = l_Lean_Compiler_LCNF_reduceJpArity___lam__0(v_phase_boxed_1516_, v_h_1515_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceJpArity(
    mut v_phase_1518_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = crate::leanh::lean_box((v_phase_1518_) as usize);
    v___f_1520_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_reduceJpArity___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1520_, 0, v___x_1519_);
    v___x_1521_ = l_Lean_Compiler_LCNF_instInhabitedPass;
    v___x_1522_ = 0;
    v___x_1523_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v___x_1521_,
        v_phase_1518_,
        v___x_1522_,
        v___f_1520_,
    );
    return v___x_1523_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceJpArity___boxed(
    mut v_phase_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_1525_: u8 = 0;
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1525_ = (crate::leanh::lean_unbox(v_phase_1524_) as u8);
    v_res_1526_ = l_Lean_Compiler_LCNF_reduceJpArity(v_phase_boxed_1525_);
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_;
    v___x_1598_ = 1;
    v___x_1599_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_;
    v___x_1600_ = l_Lean_registerTraceClass(v___x_1597_, v___x_1598_, v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2____boxed(
    mut v_a_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
    return v_res_1602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ReduceJpArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceJpArity_563472653____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ReduceJpArity(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ReduceJpArity(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
}
