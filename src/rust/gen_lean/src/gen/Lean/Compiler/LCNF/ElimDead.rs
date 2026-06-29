// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Lean.Compiler.LCNF.PassManager
use crate::r#gen::Lean::Compiler::LCNF::Basic::l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_Phase_toPurity, l_Lean_Compiler_LCNF_eraseFunDecl___redArg,
    l_Lean_Compiler_LCNF_eraseLetDecl___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed,
    l_Lean_instEmptyCollectionFVarIdHashSet, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 108, 105, 109, 68, 101, 97, 100, 86, 97, 114, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_elimDeadVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3124881684459225322 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_elimDeadVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value) as *mut crate::leanh::LeanObject,9395430877909087188 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [69, 108, 105, 109, 68, 101, 97, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14163133238160151269 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6052363318432827440 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7554273778717026953 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5927455751105078039 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7620594354019787370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7193277325485164719 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17061857964176178842 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4186764511736025147 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4541933012811097981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9347070451442335048 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17143492271855544088 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 792928910 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10762227741200191793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7626176891831604562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4450015759653002622 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15569236097711012943 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1299_: u8 = 0;
    let mut v_key_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1298_) == 0 {
                    v___x_1299_ = 0;
                    return v___x_1299_;
                } else {
                    v_key_1300_ = crate::leanh::lean_ctor_get(v_x_1298_, 0);
                    v_tail_1301_ = crate::leanh::lean_ctor_get(v_x_1298_, 2);
                    v___x_1302_ = l_Lean_instBEqFVarId_beq(v_key_1300_, v_a_1297_);
                    if v___x_1302_ == 0 {
                        v_x_1298_ = v_tail_1301_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1302_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg___boxed(
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_x_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1306_: u8 = 0;
    let mut v_r_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1304_, v_x_1305_);
    crate::leanh::lean_dec(v_x_1305_);
    crate::leanh::lean_dec(v_a_1304_);
    v_r_1307_ = crate::leanh::lean_box((v_res_1306_) as usize);
    return v_r_1307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1308_: *mut crate::leanh::LeanObject,
    mut v_x_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u64 = 0;
    let mut v___x_1318_: u64 = 0;
    let mut v___x_1319_: u64 = 0;
    let mut v_fold_1320_: u64 = 0;
    let mut v___x_1321_: u64 = 0;
    let mut v___x_1322_: u64 = 0;
    let mut v___x_1323_: u64 = 0;
    let mut v___x_1324_: usize = 0;
    let mut v___x_1325_: usize = 0;
    let mut v___x_1326_: usize = 0;
    let mut v___x_1327_: usize = 0;
    let mut v___x_1328_: usize = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1309_) == 0 {
                    return v_x_1308_;
                } else {
                    v_key_1310_ = crate::leanh::lean_ctor_get(v_x_1309_, 0);
                    v_value_1311_ = crate::leanh::lean_ctor_get(v_x_1309_, 1);
                    v_tail_1312_ = crate::leanh::lean_ctor_get(v_x_1309_, 2);
                    v_isSharedCheck_1335_ = (!crate::leanh::lean_is_exclusive(v_x_1309_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v___x_1314_ = v_x_1309_;
                        v_isShared_1315_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1312_);
                        crate::leanh::lean_inc(v_value_1311_);
                        crate::leanh::lean_inc(v_key_1310_);
                        crate::leanh::lean_dec(v_x_1309_);
                        v___x_1314_ = crate::leanh::lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1316_ = lean_array_get_size(v_x_1308_);
                v___x_1317_ = l_Lean_instHashableFVarId_hash(v_key_1310_);
                v___x_1318_ = 32u64;
                v___x_1319_ = lean_uint64_shift_right(v___x_1317_, v___x_1318_);
                v_fold_1320_ = lean_uint64_xor(v___x_1317_, v___x_1319_);
                v___x_1321_ = 16u64;
                v___x_1322_ = lean_uint64_shift_right(v_fold_1320_, v___x_1321_);
                v___x_1323_ = lean_uint64_xor(v_fold_1320_, v___x_1322_);
                v___x_1324_ = lean_uint64_to_usize(v___x_1323_);
                v___x_1325_ = lean_usize_of_nat(v___x_1316_);
                v___x_1326_ = 1usize;
                v___x_1327_ = lean_usize_sub(v___x_1325_, v___x_1326_);
                v___x_1328_ = lean_usize_land(v___x_1324_, v___x_1327_);
                v___x_1329_ = lean_array_uget_borrowed(v_x_1308_, v___x_1328_);
                crate::leanh::lean_inc(v___x_1329_);
                if v_isShared_1315_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1314_, 2, v___x_1329_);
                    v___x_1331_ = v___x_1314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_key_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_value_1311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 2, v___x_1329_);
                    v___x_1331_ = v_reuseFailAlloc_1334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1332_ = lean_array_uset(v_x_1308_, v___x_1328_, v___x_1331_);
                v_x_1308_ = v___x_1332_;
                v_x_1309_ = v_tail_1312_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(
    mut v_i_1336_: *mut crate::leanh::LeanObject,
    mut v_source_1337_: *mut crate::leanh::LeanObject,
    mut v_target_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v_es_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1339_ = lean_array_get_size(v_source_1337_);
                v___x_1340_ = lean_nat_dec_lt(v_i_1336_, v___x_1339_);
                if v___x_1340_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1337_);
                    crate::leanh::lean_dec(v_i_1336_);
                    return v_target_1338_;
                } else {
                    v_es_1341_ = lean_array_fget(v_source_1337_, v_i_1336_);
                    v___x_1342_ = crate::leanh::lean_box(0);
                    v_source_1343_ = lean_array_fset(v_source_1337_, v_i_1336_, v___x_1342_);
                    v_target_1344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1338_, v_es_1341_);
                    v___x_1345_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1346_ = lean_nat_add(v_i_1336_, v___x_1345_);
                    crate::leanh::lean_dec(v_i_1336_);
                    v_i_1336_ = v___x_1346_;
                    v_source_1337_ = v_source_1343_;
                    v_target_1338_ = v_target_1344_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(
    mut v_data_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = lean_array_get_size(v_data_1348_);
    v___x_1350_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1351_ = lean_nat_mul(v___x_1349_, v___x_1350_);
    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1353_ = crate::leanh::lean_box(0);
    v___x_1354_ = lean_mk_array(v_nbuckets_1351_, v___x_1353_);
    v___x_1355_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v___x_1352_, v_data_1348_, v___x_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(
    mut v_m_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_b_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u64 = 0;
    let mut v___x_1363_: u64 = 0;
    let mut v___x_1364_: u64 = 0;
    let mut v_fold_1365_: u64 = 0;
    let mut v___x_1366_: u64 = 0;
    let mut v___x_1367_: u64 = 0;
    let mut v___x_1368_: u64 = 0;
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: usize = 0;
    let mut v___x_1372_: usize = 0;
    let mut v___x_1373_: usize = 0;
    let mut v_bkt_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v_val_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_unused_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1359_ = crate::leanh::lean_ctor_get(v_m_1356_, 0);
                v_buckets_1360_ = crate::leanh::lean_ctor_get(v_m_1356_, 1);
                v___x_1361_ = lean_array_get_size(v_buckets_1360_);
                v___x_1362_ = l_Lean_instHashableFVarId_hash(v_a_1357_);
                v___x_1363_ = 32u64;
                v___x_1364_ = lean_uint64_shift_right(v___x_1362_, v___x_1363_);
                v_fold_1365_ = lean_uint64_xor(v___x_1362_, v___x_1364_);
                v___x_1366_ = 16u64;
                v___x_1367_ = lean_uint64_shift_right(v_fold_1365_, v___x_1366_);
                v___x_1368_ = lean_uint64_xor(v_fold_1365_, v___x_1367_);
                v___x_1369_ = lean_uint64_to_usize(v___x_1368_);
                v___x_1370_ = lean_usize_of_nat(v___x_1361_);
                v___x_1371_ = 1usize;
                v___x_1372_ = lean_usize_sub(v___x_1370_, v___x_1371_);
                v___x_1373_ = lean_usize_land(v___x_1369_, v___x_1372_);
                v_bkt_1374_ = lean_array_uget_borrowed(v_buckets_1360_, v___x_1373_);
                v___x_1375_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1357_, v_bkt_1374_);
                if v___x_1375_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1360_);
                    crate::leanh::lean_inc(v_size_1359_);
                    v_isSharedCheck_1396_ = (!crate::leanh::lean_is_exclusive(v_m_1356_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v_unused_1397_ = crate::leanh::lean_ctor_get(v_m_1356_, 1);
                        crate::leanh::lean_dec(v_unused_1397_);
                        v_unused_1398_ = crate::leanh::lean_ctor_get(v_m_1356_, 0);
                        crate::leanh::lean_dec(v_unused_1398_);
                        v___x_1377_ = v_m_1356_;
                        v_isShared_1378_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1356_);
                        v___x_1377_ = crate::leanh::lean_box(0);
                        v_isShared_1378_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1358_);
                    crate::leanh::lean_dec(v_a_1357_);
                    return v_m_1356_;
                }
            }
            1 => {
                v___x_1379_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1380_ = lean_nat_add(v_size_1359_, v___x_1379_);
                crate::leanh::lean_dec(v_size_1359_);
                crate::leanh::lean_inc(v_bkt_1374_);
                v___x_1381_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1381_, 0, v_a_1357_);
                crate::leanh::lean_ctor_set(v___x_1381_, 1, v_b_1358_);
                crate::leanh::lean_ctor_set(v___x_1381_, 2, v_bkt_1374_);
                v_buckets_x27_1382_ = lean_array_uset(v_buckets_1360_, v___x_1373_, v___x_1381_);
                v___x_1383_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1384_ = lean_nat_mul(v_size_x27_1380_, v___x_1383_);
                v___x_1385_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1386_ = lean_nat_div(v___x_1384_, v___x_1385_);
                crate::leanh::lean_dec(v___x_1384_);
                v___x_1387_ = lean_array_get_size(v_buckets_x27_1382_);
                v___x_1388_ = lean_nat_dec_le(v___x_1386_, v___x_1387_);
                crate::leanh::lean_dec(v___x_1386_);
                if v___x_1388_ == 0 {
                    v_val_1389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_buckets_x27_1382_);
                    if v_isShared_1378_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1377_, 1, v_val_1389_);
                        crate::leanh::lean_ctor_set(v___x_1377_, 0, v_size_x27_1380_);
                        v___x_1391_ = v___x_1377_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_size_x27_1380_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_val_1389_);
                        v___x_1391_ = v_reuseFailAlloc_1392_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1378_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1377_, 1, v_buckets_x27_1382_);
                        crate::leanh::lean_ctor_set(v___x_1377_, 0, v_size_x27_1380_);
                        v___x_1394_ = v___x_1377_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_size_x27_1380_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_buckets_x27_1382_);
                        v___x_1394_ = v_reuseFailAlloc_1395_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1391_;
            }
            3 => {
                return v___x_1394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
    mut v_s_1399_: *mut crate::leanh::LeanObject,
    mut v_arg_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_arg_1400_) == 1 {
        let mut v_fvarId_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_1401_ = crate::leanh::lean_ctor_get(v_arg_1400_, 0);
        crate::leanh::lean_inc(v_fvarId_1401_);
        crate::leanh::lean_dec_ref_known(v_arg_1400_, 1);
        v___x_1402_ = crate::leanh::lean_box(0);
        v___x_1403_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1399_, v_fvarId_1401_, v___x_1402_);
        return v___x_1403_;
    } else {
        crate::leanh::lean_dec(v_arg_1400_);
        return v_s_1399_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(
    mut v_pu_1404_: u8,
    mut v_s_1405_: *mut crate::leanh::LeanObject,
    mut v_arg_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v_s_1405_,
            v_arg_1406_,
        );
    return v___x_1407_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(
    mut v_pu_1408_: *mut crate::leanh::LeanObject,
    mut v_s_1409_: *mut crate::leanh::LeanObject,
    mut v_arg_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1411_: u8 = 0;
    let mut v_res_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1411_ = (crate::leanh::lean_unbox(v_pu_1408_) as u8);
    v_res_1412_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(
            v_pu_boxed_1411_,
            v_s_1409_,
            v_arg_1410_,
        );
    return v_res_1412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(
    mut v_00_u03b2_1413_: *mut crate::leanh::LeanObject,
    mut v_m_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_b_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_m_1414_, v_a_1415_, v_b_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(
    mut v_00_u03b2_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_x_1420_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1421_: u8 = 0;
    v___x_1421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1419_, v_x_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___boxed(
    mut v_00_u03b2_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_x_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(v_00_u03b2_1422_, v_a_1423_, v_x_1424_);
    crate::leanh::lean_dec(v_x_1424_);
    crate::leanh::lean_dec(v_a_1423_);
    v_r_1426_ = crate::leanh::lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1(
    mut v_00_u03b2_1427_: *mut crate::leanh::LeanObject,
    mut v_data_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_data_1428_);
    return v___x_1429_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1430_: *mut crate::leanh::LeanObject,
    mut v_i_1431_: *mut crate::leanh::LeanObject,
    mut v_source_1432_: *mut crate::leanh::LeanObject,
    mut v_target_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v_i_1431_, v_source_1432_, v_target_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1435_: *mut crate::leanh::LeanObject,
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1436_, v_x_1437_);
    return v___x_1438_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(
    mut v_as_1439_: *mut crate::leanh::LeanObject,
    mut v_i_1440_: usize,
    mut v_stop_1441_: usize,
    mut v_b_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1443_ = lean_usize_dec_eq(v_i_1440_, v_stop_1441_);
                if v___x_1443_ == 0 {
                    v___x_1444_ = lean_array_uget_borrowed(v_as_1439_, v_i_1440_);
                    crate::leanh::lean_inc(v___x_1444_);
                    v___x_1445_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_b_1442_, v___x_1444_);
                    v___x_1446_ = 1usize;
                    v___x_1447_ = lean_usize_add(v_i_1440_, v___x_1446_);
                    v_i_1440_ = v___x_1447_;
                    v_b_1442_ = v___x_1445_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1442_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(
    mut v_as_1449_: *mut crate::leanh::LeanObject,
    mut v_i_1450_: *mut crate::leanh::LeanObject,
    mut v_stop_1451_: *mut crate::leanh::LeanObject,
    mut v_b_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1453_: usize = 0;
    let mut v_stop_boxed_1454_: usize = 0;
    let mut v_res_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1453_ = crate::leanh::lean_unbox_usize(v_i_1450_);
    crate::leanh::lean_dec(v_i_1450_);
    v_stop_boxed_1454_ = crate::leanh::lean_unbox_usize(v_stop_1451_);
    crate::leanh::lean_dec(v_stop_1451_);
    v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_1449_, v_i_boxed_1453_, v_stop_boxed_1454_, v_b_1452_);
    crate::leanh::lean_dec_ref(v_as_1449_);
    return v_res_1455_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(
    mut v_pu_1456_: u8,
    mut v_s_1457_: *mut crate::leanh::LeanObject,
    mut v_args_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    v___x_1459_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1460_ = lean_array_get_size(v_args_1458_);
    v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
    if v___x_1461_ == 0 {
        return v_s_1457_;
    } else {
        let mut v___x_1462_: u8 = 0;
        v___x_1462_ = lean_nat_dec_le(v___x_1460_, v___x_1460_);
        if v___x_1462_ == 0 {
            if v___x_1461_ == 0 {
                return v_s_1457_;
            } else {
                let mut v___x_1463_: usize = 0;
                let mut v___x_1464_: usize = 0;
                let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1463_ = 0usize;
                v___x_1464_ = lean_usize_of_nat(v___x_1460_);
                v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_1458_, v___x_1463_, v___x_1464_, v_s_1457_);
                return v___x_1465_;
            }
        } else {
            let mut v___x_1466_: usize = 0;
            let mut v___x_1467_: usize = 0;
            let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1466_ = 0usize;
            v___x_1467_ = lean_usize_of_nat(v___x_1460_);
            v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_1458_, v___x_1466_, v___x_1467_, v_s_1457_);
            return v___x_1468_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(
    mut v_pu_1469_: *mut crate::leanh::LeanObject,
    mut v_s_1470_: *mut crate::leanh::LeanObject,
    mut v_args_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1472_: u8 = 0;
    let mut v_res_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1472_ = (crate::leanh::lean_unbox(v_pu_1469_) as u8);
    v_res_1473_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(
            v_pu_boxed_1472_,
            v_s_1470_,
            v_args_1471_,
        );
    crate::leanh::lean_dec_ref(v_args_1471_);
    return v_res_1473_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(
    mut v_pu_1474_: u8,
    mut v_as_1475_: *mut crate::leanh::LeanObject,
    mut v_i_1476_: usize,
    mut v_stop_1477_: usize,
    mut v_b_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_1475_, v_i_1476_, v_stop_1477_, v_b_1478_);
    return v___x_1479_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(
    mut v_pu_1480_: *mut crate::leanh::LeanObject,
    mut v_as_1481_: *mut crate::leanh::LeanObject,
    mut v_i_1482_: *mut crate::leanh::LeanObject,
    mut v_stop_1483_: *mut crate::leanh::LeanObject,
    mut v_b_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1485_: u8 = 0;
    let mut v_i_boxed_1486_: usize = 0;
    let mut v_stop_boxed_1487_: usize = 0;
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1485_ = (crate::leanh::lean_unbox(v_pu_1480_) as u8);
    v_i_boxed_1486_ = crate::leanh::lean_unbox_usize(v_i_1482_);
    crate::leanh::lean_dec(v_i_1482_);
    v_stop_boxed_1487_ = crate::leanh::lean_unbox_usize(v_stop_1483_);
    crate::leanh::lean_dec(v_stop_1483_);
    v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_1485_, v_as_1481_, v_i_boxed_1486_, v_stop_boxed_1487_, v_b_1484_);
    crate::leanh::lean_dec_ref(v_as_1481_);
    return v_res_1488_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
    mut v_pu_1489_: u8,
    mut v_s_1490_: *mut crate::leanh::LeanObject,
    mut v_e_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_1491_) {
                2 => {
                    v_struct_1500_ = crate::leanh::lean_ctor_get(v_e_1491_, 2);
                    crate::leanh::lean_inc(v_struct_1500_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1501_ = crate::leanh::lean_box(0);
                    v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_struct_1500_, v___x_1501_);
                    return v___x_1502_;
                }
                3 => {
                    v_args_1503_ = crate::leanh::lean_ctor_get(v_e_1491_, 2);
                    crate::leanh::lean_inc_ref(v_args_1503_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1504_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1503_);
                    crate::leanh::lean_dec_ref(v_args_1503_);
                    return v___x_1504_;
                }
                4 => {
                    v_fvarId_1505_ = crate::leanh::lean_ctor_get(v_e_1491_, 0);
                    crate::leanh::lean_inc(v_fvarId_1505_);
                    v_args_1506_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc_ref(v_args_1506_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1507_ = crate::leanh::lean_box(0);
                    v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1505_, v___x_1507_);
                    v___x_1509_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v___x_1508_, v_args_1506_);
                    crate::leanh::lean_dec_ref(v_args_1506_);
                    return v___x_1509_;
                }
                5 => {
                    v_args_1510_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc_ref(v_args_1510_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1511_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1510_);
                    crate::leanh::lean_dec_ref(v_args_1510_);
                    return v___x_1511_;
                }
                6 => {
                    v_var_1512_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc(v_var_1512_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1512_;
                    state = 2;
                    continue;
                }
                7 => {
                    v_var_1513_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc(v_var_1513_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1513_;
                    state = 2;
                    continue;
                }
                8 => {
                    v_var_1514_ = crate::leanh::lean_ctor_get(v_e_1491_, 2);
                    crate::leanh::lean_inc(v_var_1514_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1515_ = crate::leanh::lean_box(0);
                    v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_var_1514_, v___x_1515_);
                    return v___x_1516_;
                }
                9 => {
                    v_args_1517_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc_ref(v_args_1517_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1518_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1517_);
                    crate::leanh::lean_dec_ref(v_args_1517_);
                    return v___x_1518_;
                }
                10 => {
                    v_args_1519_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc_ref(v_args_1519_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1520_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1519_);
                    crate::leanh::lean_dec_ref(v_args_1519_);
                    return v___x_1520_;
                }
                11 => {
                    v_var_1521_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc(v_var_1521_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1521_;
                    state = 2;
                    continue;
                }
                12 => {
                    v_var_1522_ = crate::leanh::lean_ctor_get(v_e_1491_, 0);
                    crate::leanh::lean_inc(v_var_1522_);
                    v_args_1523_ = crate::leanh::lean_ctor_get(v_e_1491_, 2);
                    crate::leanh::lean_inc_ref(v_args_1523_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1524_ = crate::leanh::lean_box(0);
                    v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_var_1522_, v___x_1524_);
                    v___x_1526_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v___x_1525_, v_args_1523_);
                    crate::leanh::lean_dec_ref(v_args_1523_);
                    return v___x_1526_;
                }
                13 => {
                    v_fvarId_1527_ = crate::leanh::lean_ctor_get(v_e_1491_, 1);
                    crate::leanh::lean_inc(v_fvarId_1527_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1528_ = crate::leanh::lean_box(0);
                    v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1527_, v___x_1528_);
                    return v___x_1529_;
                }
                14 => {
                    v_fvarId_1530_ = crate::leanh::lean_ctor_get(v_e_1491_, 0);
                    crate::leanh::lean_inc(v_fvarId_1530_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 1);
                    v_fvarId_1493_ = v_fvarId_1530_;
                    state = 1;
                    continue;
                }
                15 => {
                    v_fvarId_1531_ = crate::leanh::lean_ctor_get(v_e_1491_, 0);
                    crate::leanh::lean_inc(v_fvarId_1531_);
                    crate::leanh::lean_dec_ref_known(v_e_1491_, 1);
                    v_fvarId_1493_ = v_fvarId_1531_;
                    state = 1;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec(v_e_1491_);
                    return v_s_1490_;
                }
            },
            1 => {
                v___x_1494_ = crate::leanh::lean_box(0);
                v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1493_, v___x_1494_);
                return v___x_1495_;
            }
            2 => {
                v___x_1498_ = crate::leanh::lean_box(0);
                v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1497_, v___x_1498_);
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(
    mut v_pu_1532_: *mut crate::leanh::LeanObject,
    mut v_s_1533_: *mut crate::leanh::LeanObject,
    mut v_e_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1535_: u8 = 0;
    let mut v_res_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1535_ = (crate::leanh::lean_unbox(v_pu_1532_) as u8);
    v_res_1536_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_boxed_1535_,
            v_s_1533_,
            v_e_1534_,
        );
    return v_res_1536_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(
    mut v_arg_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_st_ref_take(v_a_1538_);
    v___x_1541_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v___x_1540_,
            v_arg_1537_,
        );
    v___x_1542_ = lean_st_ref_set(v_a_1538_, v___x_1541_);
    v___x_1543_ = crate::leanh::lean_box(0);
    v___x_1544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1544_, 0, v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(
    mut v_arg_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(
            v_arg_1545_,
            v_a_1546_,
        );
    crate::leanh::lean_dec(v_a_1546_);
    return v_res_1548_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(
    mut v_pu_1549_: u8,
    mut v_arg_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = lean_st_ref_take(v_a_1551_);
    v___x_1558_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v___x_1557_,
            v_arg_1550_,
        );
    v___x_1559_ = lean_st_ref_set(v_a_1551_, v___x_1558_);
    v___x_1560_ = crate::leanh::lean_box(0);
    v___x_1561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(
    mut v_pu_1562_: *mut crate::leanh::LeanObject,
    mut v_arg_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1570_: u8 = 0;
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1570_ = (crate::leanh::lean_unbox(v_pu_1562_) as u8);
    v_res_1571_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(
        v_pu_boxed_1570_,
        v_arg_1563_,
        v_a_1564_,
        v_a_1565_,
        v_a_1566_,
        v_a_1567_,
        v_a_1568_,
    );
    crate::leanh::lean_dec(v_a_1568_);
    crate::leanh::lean_dec_ref(v_a_1567_);
    crate::leanh::lean_dec(v_a_1566_);
    crate::leanh::lean_dec_ref(v_a_1565_);
    crate::leanh::lean_dec(v_a_1564_);
    return v_res_1571_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(
    mut v_pu_1572_: u8,
    mut v_e_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_st_ref_take(v_a_1574_);
    v___x_1577_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_1572_,
            v___x_1576_,
            v_e_1573_,
        );
    v___x_1578_ = lean_st_ref_set(v_a_1574_, v___x_1577_);
    v___x_1579_ = crate::leanh::lean_box(0);
    v___x_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1580_, 0, v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(
    mut v_pu_1581_: *mut crate::leanh::LeanObject,
    mut v_e_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1585_: u8 = 0;
    let mut v_res_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1585_ = (crate::leanh::lean_unbox(v_pu_1581_) as u8);
    v_res_1586_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(
            v_pu_boxed_1585_,
            v_e_1582_,
            v_a_1583_,
        );
    crate::leanh::lean_dec(v_a_1583_);
    return v_res_1586_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(
    mut v_pu_1587_: u8,
    mut v_e_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = lean_st_ref_take(v_a_1589_);
    v___x_1596_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_1587_,
            v___x_1595_,
            v_e_1588_,
        );
    v___x_1597_ = lean_st_ref_set(v_a_1589_, v___x_1596_);
    v___x_1598_ = crate::leanh::lean_box(0);
    v___x_1599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1599_, 0, v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(
    mut v_pu_1600_: *mut crate::leanh::LeanObject,
    mut v_e_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1608_: u8 = 0;
    let mut v_res_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1608_ = (crate::leanh::lean_unbox(v_pu_1600_) as u8);
    v_res_1609_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(
        v_pu_boxed_1608_,
        v_e_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
    );
    crate::leanh::lean_dec(v_a_1606_);
    crate::leanh::lean_dec_ref(v_a_1605_);
    crate::leanh::lean_dec(v_a_1604_);
    crate::leanh::lean_dec_ref(v_a_1603_);
    crate::leanh::lean_dec(v_a_1602_);
    return v_res_1609_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(
    mut v_fvarId_1612_: *mut crate::leanh::LeanObject,
    mut v_a_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = lean_st_ref_take(v_a_1613_);
    v___x_1616_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0;
    v___x_1617_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1;
    v___x_1618_ = crate::leanh::lean_box(0);
    v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_1616_,
        v___x_1617_,
        v___x_1615_,
        v_fvarId_1612_,
        v___x_1618_,
    );
    v___x_1620_ = lean_st_ref_set(v_a_1613_, v___x_1619_);
    v___x_1621_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1621_, 0, v___x_1618_);
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(
    mut v_fvarId_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(
            v_fvarId_1622_,
            v_a_1623_,
        );
    crate::leanh::lean_dec(v_a_1623_);
    return v_res_1625_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(
    mut v_fvarId_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = lean_st_ref_take(v_a_1627_);
    v___x_1634_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0;
    v___x_1635_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1;
    v___x_1636_ = crate::leanh::lean_box(0);
    v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_1634_,
        v___x_1635_,
        v___x_1633_,
        v_fvarId_1626_,
        v___x_1636_,
    );
    v___x_1638_ = lean_st_ref_set(v_a_1627_, v___x_1637_);
    v___x_1639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1639_, 0, v___x_1636_);
    return v___x_1639_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(
    mut v_fvarId_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_a_1645_: *mut crate::leanh::LeanObject,
    mut v_a_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(
        v_fvarId_1640_,
        v_a_1641_,
        v_a_1642_,
        v_a_1643_,
        v_a_1644_,
        v_a_1645_,
    );
    crate::leanh::lean_dec(v_a_1645_);
    crate::leanh::lean_dec_ref(v_a_1644_);
    crate::leanh::lean_dec(v_a_1643_);
    crate::leanh::lean_dec_ref(v_a_1642_);
    crate::leanh::lean_dec(v_a_1641_);
    return v_res_1647_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(
    mut v_pu_1648_: u8,
    mut v_val_1649_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_pu_1648_ == 0 {
        let mut v___x_1650_: u8 = 0;
        v___x_1650_ = 1;
        return v___x_1650_;
    } else {
        match crate::leanh::lean_obj_tag(v_val_1649_) {
            1 => {
                let mut v___x_1651_: u8 = 0;
                v___x_1651_ = 1;
                return v___x_1651_;
            }
            4 => {
                let mut v___x_1652_: u8 = 0;
                v___x_1652_ = 0;
                return v___x_1652_;
            }
            9 => {
                let mut v_args_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1656_: u8 = 0;
                v_args_1653_ = crate::leanh::lean_ctor_get(v_val_1649_, 1);
                v___x_1654_ = lean_array_get_size(v_args_1653_);
                v___x_1655_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1656_ = lean_nat_dec_eq(v___x_1654_, v___x_1655_);
                return v___x_1656_;
            }
            _ => {
                let mut v___x_1657_: u8 = 0;
                v___x_1657_ = 1;
                return v___x_1657_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(
    mut v_pu_1658_: *mut crate::leanh::LeanObject,
    mut v_val_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_1660_: u8 = 0;
    let mut v_res_1661_: u8 = 0;
    let mut v_r_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1660_ = (crate::leanh::lean_unbox(v_pu_1658_) as u8);
    v_res_1661_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(
        v_pu_boxed_1660_,
        v_val_1659_,
    );
    crate::leanh::lean_dec(v_val_1659_);
    v_r_1662_ = crate::leanh::lean_box((v_res_1661_) as usize);
    return v_r_1662_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(
    mut v_as_1663_: *mut crate::leanh::LeanObject,
    mut v_i_1664_: usize,
    mut v_stop_1665_: usize,
    mut v_b_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_usize_dec_eq(v_i_1664_, v_stop_1665_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = lean_st_ref_take(v___y_1667_);
                    v___x_1671_ = lean_array_uget_borrowed(v_as_1663_, v_i_1664_);
                    crate::leanh::lean_inc(v___x_1671_);
                    v___x_1672_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_1670_, v___x_1671_);
                    v___x_1673_ = lean_st_ref_set(v___y_1667_, v___x_1672_);
                    v___x_1674_ = crate::leanh::lean_box(0);
                    v___x_1675_ = 1usize;
                    v___x_1676_ = lean_usize_add(v_i_1664_, v___x_1675_);
                    v_i_1664_ = v___x_1676_;
                    v_b_1666_ = v___x_1674_;
                    state = 0;
                    continue;
                } else {
                    v___x_1678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1678_, 0, v_b_1666_);
                    return v___x_1678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(
    mut v_as_1679_: *mut crate::leanh::LeanObject,
    mut v_i_1680_: *mut crate::leanh::LeanObject,
    mut v_stop_1681_: *mut crate::leanh::LeanObject,
    mut v_b_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1685_: usize = 0;
    let mut v_stop_boxed_1686_: usize = 0;
    let mut v_res_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1685_ = crate::leanh::lean_unbox_usize(v_i_1680_);
    crate::leanh::lean_dec(v_i_1680_);
    v_stop_boxed_1686_ = crate::leanh::lean_unbox_usize(v_stop_1681_);
    crate::leanh::lean_dec(v_stop_1681_);
    v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_1679_, v_i_boxed_1685_, v_stop_boxed_1686_, v_b_1682_, v___y_1683_);
    crate::leanh::lean_dec(v___y_1683_);
    crate::leanh::lean_dec_ref(v_as_1679_);
    return v_res_1687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(
    mut v_m_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u64 = 0;
    let mut v___x_1693_: u64 = 0;
    let mut v___x_1694_: u64 = 0;
    let mut v_fold_1695_: u64 = 0;
    let mut v___x_1696_: u64 = 0;
    let mut v___x_1697_: u64 = 0;
    let mut v___x_1698_: u64 = 0;
    let mut v___x_1699_: usize = 0;
    let mut v___x_1700_: usize = 0;
    let mut v___x_1701_: usize = 0;
    let mut v___x_1702_: usize = 0;
    let mut v___x_1703_: usize = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    v_buckets_1690_ = crate::leanh::lean_ctor_get(v_m_1688_, 1);
    v___x_1691_ = lean_array_get_size(v_buckets_1690_);
    v___x_1692_ = l_Lean_instHashableFVarId_hash(v_a_1689_);
    v___x_1693_ = 32u64;
    v___x_1694_ = lean_uint64_shift_right(v___x_1692_, v___x_1693_);
    v_fold_1695_ = lean_uint64_xor(v___x_1692_, v___x_1694_);
    v___x_1696_ = 16u64;
    v___x_1697_ = lean_uint64_shift_right(v_fold_1695_, v___x_1696_);
    v___x_1698_ = lean_uint64_xor(v_fold_1695_, v___x_1697_);
    v___x_1699_ = lean_uint64_to_usize(v___x_1698_);
    v___x_1700_ = lean_usize_of_nat(v___x_1691_);
    v___x_1701_ = 1usize;
    v___x_1702_ = lean_usize_sub(v___x_1700_, v___x_1701_);
    v___x_1703_ = lean_usize_land(v___x_1699_, v___x_1702_);
    v___x_1704_ = lean_array_uget_borrowed(v_buckets_1690_, v___x_1703_);
    v___x_1705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1689_, v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(
    mut v_m_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1708_: u8 = 0;
    let mut v_r_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_1706_, v_a_1707_);
    crate::leanh::lean_dec(v_a_1707_);
    crate::leanh::lean_dec_ref(v_m_1706_);
    v_r_1709_ = crate::leanh::lean_box((v_res_1708_) as usize);
    return v_r_1709_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(
    mut v_pu_1710_: u8,
    mut v_i_1711_: *mut crate::leanh::LeanObject,
    mut v_as_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: u8 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v_code_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_array_get_size(v_as_1712_);
                v___x_1720_ = lean_nat_dec_lt(v_i_1711_, v___x_1719_);
                if v___x_1720_ == 0 {
                    crate::leanh::lean_dec(v_i_1711_);
                    v___x_1721_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1721_, 0, v_as_1712_);
                    return v___x_1721_;
                } else {
                    v_a_1722_ = lean_array_fget_borrowed(v_as_1712_, v_i_1711_);
                    match crate::leanh::lean_obj_tag(v_a_1722_) {
                        0 => {
                            v_code_1746_ = crate::leanh::lean_ctor_get(v_a_1722_, 2);
                            crate::leanh::lean_inc_ref(v_code_1746_);
                            v___y_1724_ = v_code_1746_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1747_ = crate::leanh::lean_ctor_get(v_a_1722_, 1);
                            crate::leanh::lean_inc_ref(v_code_1747_);
                            v___y_1724_ = v_code_1747_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1748_ = crate::leanh::lean_ctor_get(v_a_1722_, 0);
                            crate::leanh::lean_inc_ref(v_code_1748_);
                            v___y_1724_ = v_code_1748_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1725_ =
                    l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
                        v_pu_1710_,
                        v___y_1724_,
                        v___y_1713_,
                        v___y_1714_,
                        v___y_1715_,
                        v___y_1716_,
                        v___y_1717_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1725_) == 0 {
                    v_a_1726_ = crate::leanh::lean_ctor_get(v___x_1725_, 0);
                    crate::leanh::lean_inc(v_a_1726_);
                    crate::leanh::lean_dec_ref_known(v___x_1725_, 1);
                    crate::leanh::lean_inc(v_a_1722_);
                    v___x_1727_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1722_, v_a_1726_);
                    v___x_1728_ = lean_ptr_addr(v_a_1722_);
                    v___x_1729_ = lean_ptr_addr(v___x_1727_);
                    v___x_1730_ = lean_usize_dec_eq(v___x_1728_, v___x_1729_);
                    if v___x_1730_ == 0 {
                        v___x_1731_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1732_ = lean_nat_add(v_i_1711_, v___x_1731_);
                        v___x_1733_ = lean_array_fset(v_as_1712_, v_i_1711_, v___x_1727_);
                        crate::leanh::lean_dec(v_i_1711_);
                        v_i_1711_ = v___x_1732_;
                        v_as_1712_ = v___x_1733_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1727_);
                        v___x_1735_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1736_ = lean_nat_add(v_i_1711_, v___x_1735_);
                        crate::leanh::lean_dec(v_i_1711_);
                        v_i_1711_ = v___x_1736_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_as_1712_);
                    crate::leanh::lean_dec(v_i_1711_);
                    v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1725_, 0);
                    v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v___x_1725_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1740_ = v___x_1725_;
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1738_);
                        crate::leanh::lean_dec(v___x_1725_);
                        v___x_1740_ = crate::leanh::lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1741_ == 0 {
                    v___x_1743_ = v___x_1740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
    mut v_pu_1749_: u8,
    mut v_code_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_unused_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut v_decl_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: usize = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_unused_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut v_unused_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: u8 = 0;
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_decl_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___y_1860_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_unused_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: u8 = 0;
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_a_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut v_decl_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1906_: u8 = 0;
    let mut v_unused_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___y_1922_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v_unused_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_fvarId_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: usize = 0;
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: usize = 0;
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: usize = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_fvarId_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_unused_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v_fvarId_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_unused_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_fvarId_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: usize = 0;
    let mut v___x_2125_: u8 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v_fvarId_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_unused_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v_fvarId_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2180_: u8 = 0;
    let mut v_persistent_2181_: u8 = 0;
    let mut v_k_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: usize = 0;
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v_unused_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_fvarId_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_2214_: u8 = 0;
    let mut v_persistent_2215_: u8 = 0;
    let mut v_objs_x3f_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2247_: u8 = 0;
    let mut v_fvarId_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: usize = 0;
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_code_1750_) {
                    0 => {
                        v_decl_1775_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_k_1776_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_inc_ref(v_k_1776_);
                        v___x_1777_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1776_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_1777_) == 0 {
                            v_a_1778_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                            v_isSharedCheck_1828_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1777_)) as u8;
                            if v_isSharedCheck_1828_ == 0 {
                                v___x_1780_ = v___x_1777_;
                                v_isShared_1781_ = v_isSharedCheck_1828_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1778_);
                                crate::leanh::lean_dec(v___x_1777_);
                                v___x_1780_ = crate::leanh::lean_box(0);
                                v_isShared_1781_ = v_isSharedCheck_1828_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1777_;
                        }
                    }
                    1 => {
                        v_decl_1829_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_k_1830_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_inc_ref(v_k_1830_);
                        v___x_1831_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1830_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_1831_) == 0 {
                            v_a_1832_ = crate::leanh::lean_ctor_get(v___x_1831_, 0);
                            crate::leanh::lean_inc(v_a_1832_);
                            crate::leanh::lean_dec_ref_known(v___x_1831_, 1);
                            v___x_1833_ = lean_st_ref_get(v_a_1751_);
                            v_fvarId_1834_ = crate::leanh::lean_ctor_get(v_decl_1829_, 0);
                            v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1833_, v_fvarId_1834_);
                            crate::leanh::lean_dec(v___x_1833_);
                            if v___x_1835_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_1829_);
                                crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                                v___x_1836_ = 1;
                                v___x_1837_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                                    v_pu_1749_,
                                    v_decl_1829_,
                                    v___x_1836_,
                                    v_a_1753_,
                                );
                                crate::leanh::lean_dec_ref(v_decl_1829_);
                                if crate::leanh::lean_obj_tag(v___x_1837_) == 0 {
                                    v_isSharedCheck_1844_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1837_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v_unused_1845_ =
                                            crate::leanh::lean_ctor_get(v___x_1837_, 0);
                                        crate::leanh::lean_dec(v_unused_1845_);
                                        v___x_1839_ = v___x_1837_;
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1837_);
                                        v___x_1839_ = crate::leanh::lean_box(0);
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1832_);
                                    v_a_1846_ = crate::leanh::lean_ctor_get(v___x_1837_, 0);
                                    v_isSharedCheck_1853_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1837_)) as u8;
                                    if v_isSharedCheck_1853_ == 0 {
                                        v___x_1848_ = v___x_1837_;
                                        v_isShared_1849_ = v_isSharedCheck_1853_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1846_);
                                        crate::leanh::lean_dec(v___x_1837_);
                                        v___x_1848_ = crate::leanh::lean_box(0);
                                        v_isShared_1849_ = v_isSharedCheck_1853_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_decl_1829_);
                                v___x_1854_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_1749_, v_decl_1829_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                                if crate::leanh::lean_obj_tag(v___x_1854_) == 0 {
                                    v_a_1855_ = crate::leanh::lean_ctor_get(v___x_1854_, 0);
                                    v_isSharedCheck_1882_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1854_)) as u8;
                                    if v_isSharedCheck_1882_ == 0 {
                                        v___x_1857_ = v___x_1854_;
                                        v_isShared_1858_ = v_isSharedCheck_1882_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1855_);
                                        crate::leanh::lean_dec(v___x_1854_);
                                        v___x_1857_ = crate::leanh::lean_box(0);
                                        v_isShared_1858_ = v_isSharedCheck_1882_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1832_);
                                    crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                                    v_a_1883_ = crate::leanh::lean_ctor_get(v___x_1854_, 0);
                                    v_isSharedCheck_1890_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1854_)) as u8;
                                    if v_isSharedCheck_1890_ == 0 {
                                        v___x_1885_ = v___x_1854_;
                                        v_isShared_1886_ = v_isSharedCheck_1890_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1883_);
                                        crate::leanh::lean_dec(v___x_1854_);
                                        v___x_1885_ = crate::leanh::lean_box(0);
                                        v_isShared_1886_ = v_isSharedCheck_1890_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1831_;
                        }
                    }
                    2 => {
                        v_decl_1891_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_k_1892_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_inc_ref(v_k_1892_);
                        v___x_1893_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1892_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_1893_) == 0 {
                            v_a_1894_ = crate::leanh::lean_ctor_get(v___x_1893_, 0);
                            crate::leanh::lean_inc(v_a_1894_);
                            crate::leanh::lean_dec_ref_known(v___x_1893_, 1);
                            v___x_1895_ = lean_st_ref_get(v_a_1751_);
                            v_fvarId_1896_ = crate::leanh::lean_ctor_get(v_decl_1891_, 0);
                            v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1895_, v_fvarId_1896_);
                            crate::leanh::lean_dec(v___x_1895_);
                            if v___x_1897_ == 0 {
                                crate::leanh::lean_inc_ref(v_decl_1891_);
                                crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                                v___x_1898_ = 1;
                                v___x_1899_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                                    v_pu_1749_,
                                    v_decl_1891_,
                                    v___x_1898_,
                                    v_a_1753_,
                                );
                                crate::leanh::lean_dec_ref(v_decl_1891_);
                                if crate::leanh::lean_obj_tag(v___x_1899_) == 0 {
                                    v_isSharedCheck_1906_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1899_)) as u8;
                                    if v_isSharedCheck_1906_ == 0 {
                                        v_unused_1907_ =
                                            crate::leanh::lean_ctor_get(v___x_1899_, 0);
                                        crate::leanh::lean_dec(v_unused_1907_);
                                        v___x_1901_ = v___x_1899_;
                                        v_isShared_1902_ = v_isSharedCheck_1906_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1899_);
                                        v___x_1901_ = crate::leanh::lean_box(0);
                                        v_isShared_1902_ = v_isSharedCheck_1906_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1894_);
                                    v_a_1908_ = crate::leanh::lean_ctor_get(v___x_1899_, 0);
                                    v_isSharedCheck_1915_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1899_)) as u8;
                                    if v_isSharedCheck_1915_ == 0 {
                                        v___x_1910_ = v___x_1899_;
                                        v_isShared_1911_ = v_isSharedCheck_1915_;
                                        state = 31;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1908_);
                                        crate::leanh::lean_dec(v___x_1899_);
                                        v___x_1910_ = crate::leanh::lean_box(0);
                                        v_isShared_1911_ = v_isSharedCheck_1915_;
                                        state = 31;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc_ref(v_decl_1891_);
                                v___x_1916_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_1749_, v_decl_1891_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                                if crate::leanh::lean_obj_tag(v___x_1916_) == 0 {
                                    v_a_1917_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                                    v_isSharedCheck_1944_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1916_)) as u8;
                                    if v_isSharedCheck_1944_ == 0 {
                                        v___x_1919_ = v___x_1916_;
                                        v_isShared_1920_ = v_isSharedCheck_1944_;
                                        state = 33;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1917_);
                                        crate::leanh::lean_dec(v___x_1916_);
                                        v___x_1919_ = crate::leanh::lean_box(0);
                                        v_isShared_1920_ = v_isSharedCheck_1944_;
                                        state = 33;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1894_);
                                    crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                                    v_a_1945_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                                    v_isSharedCheck_1952_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1916_)) as u8;
                                    if v_isSharedCheck_1952_ == 0 {
                                        v___x_1947_ = v___x_1916_;
                                        v_isShared_1948_ = v_isSharedCheck_1952_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1945_);
                                        crate::leanh::lean_dec(v___x_1916_);
                                        v___x_1947_ = crate::leanh::lean_box(0);
                                        v_isShared_1948_ = v_isSharedCheck_1952_;
                                        state = 39;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1893_;
                        }
                    }
                    3 => {
                        v_fvarId_1953_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_args_1954_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v___x_1955_ = lean_st_ref_take(v_a_1751_);
                        v___x_1956_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_fvarId_1953_);
                        v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_1955_, v_fvarId_1953_, v___x_1956_);
                        v___x_1958_ = lean_st_ref_set(v_a_1751_, v___x_1957_);
                        v___x_1959_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1960_ = lean_array_get_size(v_args_1954_);
                        v___x_1961_ = lean_nat_dec_lt(v___x_1959_, v___x_1960_);
                        if v___x_1961_ == 0 {
                            v___x_1962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1962_, 0, v_code_1750_);
                            return v___x_1962_;
                        } else {
                            v___x_1963_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
                            if v___x_1963_ == 0 {
                                if v___x_1961_ == 0 {
                                    v___x_1964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1964_, 0, v_code_1750_);
                                    return v___x_1964_;
                                } else {
                                    v___x_1965_ = 0usize;
                                    v___x_1966_ = lean_usize_of_nat(v___x_1960_);
                                    v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_1954_, v___x_1965_, v___x_1966_, v___x_1956_, v_a_1751_);
                                    v___y_1758_ = v___x_1967_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_1968_ = 0usize;
                                v___x_1969_ = lean_usize_of_nat(v___x_1960_);
                                v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_1954_, v___x_1968_, v___x_1969_, v___x_1956_, v_a_1751_);
                                v___y_1758_ = v___x_1970_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                    4 => {
                        v_cases_1971_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_inc_ref(v_cases_1971_);
                        v_typeName_1972_ = crate::leanh::lean_ctor_get(v_cases_1971_, 0);
                        v_resultType_1973_ = crate::leanh::lean_ctor_get(v_cases_1971_, 1);
                        v_discr_1974_ = crate::leanh::lean_ctor_get(v_cases_1971_, 2);
                        v_alts_1975_ = crate::leanh::lean_ctor_get(v_cases_1971_, 3);
                        v_isSharedCheck_2018_ =
                            (!crate::leanh::lean_is_exclusive(v_cases_1971_)) as u8;
                        if v_isSharedCheck_2018_ == 0 {
                            v___x_1977_ = v_cases_1971_;
                            v_isShared_1978_ = v_isSharedCheck_2018_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_alts_1975_);
                            crate::leanh::lean_inc(v_discr_1974_);
                            crate::leanh::lean_inc(v_resultType_1973_);
                            crate::leanh::lean_inc(v_typeName_1972_);
                            crate::leanh::lean_dec(v_cases_1971_);
                            v___x_1977_ = crate::leanh::lean_box(0);
                            v_isShared_1978_ = v_isSharedCheck_2018_;
                            state = 41;
                            continue;
                        }
                    }
                    5 => {
                        v_fvarId_2019_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v___x_2020_ = lean_st_ref_take(v_a_1751_);
                        v___x_2021_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_fvarId_2019_);
                        v___x_2022_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2020_, v_fvarId_2019_, v___x_2021_);
                        v___x_2023_ = lean_st_ref_set(v_a_1751_, v___x_2022_);
                        v___x_2024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2024_, 0, v_code_1750_);
                        return v___x_2024_;
                    }
                    6 => {
                        v___x_2025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2025_, 0, v_code_1750_);
                        return v___x_2025_;
                    }
                    7 => {
                        v_fvarId_2026_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_i_2027_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_y_2028_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        v_k_2029_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                        crate::leanh::lean_inc_ref(v_k_2029_);
                        v___x_2030_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2029_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2030_) == 0 {
                            v_a_2031_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                            v_isSharedCheck_2063_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2030_)) as u8;
                            if v_isSharedCheck_2063_ == 0 {
                                v___x_2033_ = v___x_2030_;
                                v_isShared_2034_ = v_isSharedCheck_2063_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2031_);
                                crate::leanh::lean_dec(v___x_2030_);
                                v___x_2033_ = crate::leanh::lean_box(0);
                                v_isShared_2034_ = v_isSharedCheck_2063_;
                                state = 50;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2030_;
                        }
                    }
                    8 => {
                        v_fvarId_2064_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_i_2065_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_y_2066_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        v_k_2067_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                        crate::leanh::lean_inc_ref(v_k_2067_);
                        v___x_2068_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2067_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2068_) == 0 {
                            v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                            v_isSharedCheck_2102_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2068_)) as u8;
                            if v_isSharedCheck_2102_ == 0 {
                                v___x_2071_ = v___x_2068_;
                                v_isShared_2072_ = v_isSharedCheck_2102_;
                                state = 56;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2069_);
                                crate::leanh::lean_dec(v___x_2068_);
                                v___x_2071_ = crate::leanh::lean_box(0);
                                v_isShared_2072_ = v_isSharedCheck_2102_;
                                state = 56;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2068_;
                        }
                    }
                    9 => {
                        v_fvarId_2103_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_i_2104_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_offset_2105_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        v_y_2106_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                        v_ty_2107_ = crate::leanh::lean_ctor_get(v_code_1750_, 4);
                        v_k_2108_ = crate::leanh::lean_ctor_get(v_code_1750_, 5);
                        crate::leanh::lean_inc_ref(v_k_2108_);
                        v___x_2109_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2108_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2109_) == 0 {
                            v_a_2110_ = crate::leanh::lean_ctor_get(v___x_2109_, 0);
                            v_isSharedCheck_2145_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2109_)) as u8;
                            if v_isSharedCheck_2145_ == 0 {
                                v___x_2112_ = v___x_2109_;
                                v_isShared_2113_ = v_isSharedCheck_2145_;
                                state = 62;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2110_);
                                crate::leanh::lean_dec(v___x_2109_);
                                v___x_2112_ = crate::leanh::lean_box(0);
                                v_isShared_2113_ = v_isSharedCheck_2145_;
                                state = 62;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 6);
                            return v___x_2109_;
                        }
                    }
                    10 => {
                        v_fvarId_2146_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_cidx_2147_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_k_2148_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        crate::leanh::lean_inc_ref(v_k_2148_);
                        v___x_2149_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2148_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2149_) == 0 {
                            v_a_2150_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                            v_isSharedCheck_2177_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2149_)) as u8;
                            if v_isSharedCheck_2177_ == 0 {
                                v___x_2152_ = v___x_2149_;
                                v_isShared_2153_ = v_isSharedCheck_2177_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2150_);
                                crate::leanh::lean_dec(v___x_2149_);
                                v___x_2152_ = crate::leanh::lean_box(0);
                                v_isShared_2153_ = v_isSharedCheck_2177_;
                                state = 68;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 3);
                            return v___x_2149_;
                        }
                    }
                    11 => {
                        v_fvarId_2178_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_n_2179_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_check_2180_ = crate::leanh::lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_2181_ = crate::leanh::lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_2182_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        crate::leanh::lean_inc_ref(v_k_2182_);
                        v___x_2183_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2182_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2183_) == 0 {
                            v_a_2184_ = crate::leanh::lean_ctor_get(v___x_2183_, 0);
                            v_isSharedCheck_2211_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2183_)) as u8;
                            if v_isSharedCheck_2211_ == 0 {
                                v___x_2186_ = v___x_2183_;
                                v_isShared_2187_ = v_isSharedCheck_2211_;
                                state = 73;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2184_);
                                crate::leanh::lean_dec(v___x_2183_);
                                v___x_2186_ = crate::leanh::lean_box(0);
                                v_isShared_2187_ = v_isSharedCheck_2211_;
                                state = 73;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 3);
                            return v___x_2183_;
                        }
                    }
                    12 => {
                        v_fvarId_2212_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_n_2213_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        v_check_2214_ = crate::leanh::lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        );
                        v_persistent_2215_ = crate::leanh::lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_2216_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        v_k_2217_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                        crate::leanh::lean_inc_ref(v_k_2217_);
                        v___x_2218_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2217_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2218_) == 0 {
                            v_a_2219_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                            v_isSharedCheck_2247_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                            if v_isSharedCheck_2247_ == 0 {
                                v___x_2221_ = v___x_2218_;
                                v_isShared_2222_ = v_isSharedCheck_2247_;
                                state = 78;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2219_);
                                crate::leanh::lean_dec(v___x_2218_);
                                v___x_2221_ = crate::leanh::lean_box(0);
                                v_isShared_2222_ = v_isSharedCheck_2247_;
                                state = 78;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2218_;
                        }
                    }
                    _ => {
                        v_fvarId_2248_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        v_k_2249_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_inc_ref(v_k_2249_);
                        v___x_2250_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2249_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if crate::leanh::lean_obj_tag(v___x_2250_) == 0 {
                            v_a_2251_ = crate::leanh::lean_ctor_get(v___x_2250_, 0);
                            v_isSharedCheck_2277_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2250_)) as u8;
                            if v_isSharedCheck_2277_ == 0 {
                                v___x_2253_ = v___x_2250_;
                                v_isShared_2254_ = v_isSharedCheck_2277_;
                                state = 83;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2251_);
                                crate::leanh::lean_dec(v___x_2250_);
                                v___x_2253_ = crate::leanh::lean_box(0);
                                v_isShared_2254_ = v_isSharedCheck_2277_;
                                state = 83;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_2250_;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1758_) == 0 {
                    v_isSharedCheck_1765_ = (!crate::leanh::lean_is_exclusive(v___y_1758_)) as u8;
                    if v_isSharedCheck_1765_ == 0 {
                        v_unused_1766_ = crate::leanh::lean_ctor_get(v___y_1758_, 0);
                        crate::leanh::lean_dec(v_unused_1766_);
                        v___x_1760_ = v___y_1758_;
                        v_isShared_1761_ = v_isSharedCheck_1765_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1758_);
                        v___x_1760_ = crate::leanh::lean_box(0);
                        v_isShared_1761_ = v_isSharedCheck_1765_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_1750_);
                    v_a_1767_ = crate::leanh::lean_ctor_get(v___y_1758_, 0);
                    v_isSharedCheck_1774_ = (!crate::leanh::lean_is_exclusive(v___y_1758_)) as u8;
                    if v_isSharedCheck_1774_ == 0 {
                        v___x_1769_ = v___y_1758_;
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1767_);
                        crate::leanh::lean_dec(v___y_1758_);
                        v___x_1769_ = crate::leanh::lean_box(0);
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1760_, 0, v_code_1750_);
                    v___x_1763_ = v___x_1760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_code_1750_);
                    v___x_1763_ = v_reuseFailAlloc_1764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1763_;
            }
            4 => {
                if v_isShared_1770_ == 0 {
                    v___x_1772_ = v___x_1769_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
                    v___x_1772_ = v_reuseFailAlloc_1773_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1772_;
            }
            6 => {
                v___x_1782_ = lean_st_ref_get(v_a_1751_);
                v_fvarId_1783_ = crate::leanh::lean_ctor_get(v_decl_1775_, 0);
                v_value_1784_ = crate::leanh::lean_ctor_get(v_decl_1775_, 3);
                v___x_1826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1782_, v_fvarId_1783_);
                crate::leanh::lean_dec(v___x_1782_);
                if v___x_1826_ == 0 {
                    v___x_1827_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_1749_, v_value_1784_);
                    if v___x_1827_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___y_1808_ = v___x_1826_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___y_1808_ = v___x_1826_;
                    state = 12;
                    continue;
                }
            }
            7 => {
                v___x_1786_ = lean_st_ref_take(v_a_1751_);
                crate::leanh::lean_inc(v_value_1784_);
                v___x_1787_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_1749_, v___x_1786_, v_value_1784_);
                v___x_1788_ = lean_st_ref_set(v_a_1751_, v___x_1787_);
                v___x_1789_ = lean_ptr_addr(v_k_1776_);
                v___x_1790_ = lean_ptr_addr(v_a_1778_);
                v___x_1791_ = lean_usize_dec_eq(v___x_1789_, v___x_1790_);
                if v___x_1791_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_1775_);
                    v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v_unused_1802_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_1802_);
                        v_unused_1803_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_1803_);
                        v___x_1793_ = v_code_1750_;
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_1793_ = crate::leanh::lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1778_);
                    if v_isShared_1781_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1780_, 0, v_code_1750_);
                        v___x_1805_ = v___x_1780_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_code_1750_);
                        v___x_1805_ = v_reuseFailAlloc_1806_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1793_, 1, v_a_1778_);
                    v___x_1796_ = v___x_1793_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_decl_1775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1778_);
                    v___x_1796_ = v_reuseFailAlloc_1800_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1796_);
                    v___x_1798_ = v___x_1780_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
                    v___x_1798_ = v_reuseFailAlloc_1799_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1798_;
            }
            11 => {
                return v___x_1805_;
            }
            12 => {
                if v___y_1808_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_1775_);
                    crate::leanh::lean_del_object(v___x_1780_);
                    crate::leanh::lean_dec_ref_known(v_code_1750_, 2);
                    v___x_1809_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                        v_pu_1749_,
                        v_decl_1775_,
                        v_a_1753_,
                    );
                    crate::leanh::lean_dec_ref(v_decl_1775_);
                    if crate::leanh::lean_obj_tag(v___x_1809_) == 0 {
                        v_isSharedCheck_1816_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1809_)) as u8;
                        if v_isSharedCheck_1816_ == 0 {
                            v_unused_1817_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                            crate::leanh::lean_dec(v_unused_1817_);
                            v___x_1811_ = v___x_1809_;
                            v_isShared_1812_ = v_isSharedCheck_1816_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1809_);
                            v___x_1811_ = crate::leanh::lean_box(0);
                            v_isShared_1812_ = v_isSharedCheck_1816_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1778_);
                        v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                        v_isSharedCheck_1825_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1809_)) as u8;
                        if v_isSharedCheck_1825_ == 0 {
                            v___x_1820_ = v___x_1809_;
                            v_isShared_1821_ = v_isSharedCheck_1825_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1818_);
                            crate::leanh::lean_dec(v___x_1809_);
                            v___x_1820_ = crate::leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_1825_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    state = 7;
                    continue;
                }
            }
            13 => {
                if v_isShared_1812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1811_, 0, v_a_1778_);
                    v___x_1814_ = v___x_1811_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1778_);
                    v___x_1814_ = v_reuseFailAlloc_1815_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1814_;
            }
            15 => {
                if v_isShared_1821_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
                    v___x_1823_ = v_reuseFailAlloc_1824_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1823_;
            }
            17 => {
                if v_isShared_1840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1839_, 0, v_a_1832_);
                    v___x_1842_ = v___x_1839_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1832_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1842_;
            }
            19 => {
                if v_isShared_1849_ == 0 {
                    v___x_1851_ = v___x_1848_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
                    v___x_1851_ = v_reuseFailAlloc_1852_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1851_;
            }
            21 => {
                v___x_1876_ = lean_ptr_addr(v_k_1830_);
                v___x_1877_ = lean_ptr_addr(v_a_1832_);
                v___x_1878_ = lean_usize_dec_eq(v___x_1876_, v___x_1877_);
                if v___x_1878_ == 0 {
                    v___y_1860_ = v___x_1878_;
                    state = 22;
                    continue;
                } else {
                    v___x_1879_ = lean_ptr_addr(v_decl_1829_);
                    v___x_1880_ = lean_ptr_addr(v_a_1855_);
                    v___x_1881_ = lean_usize_dec_eq(v___x_1879_, v___x_1880_);
                    v___y_1860_ = v___x_1881_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v___y_1860_ == 0 {
                    v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1870_ == 0 {
                        v_unused_1871_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_1871_);
                        v_unused_1872_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_1872_);
                        v___x_1862_ = v_code_1750_;
                        v_isShared_1863_ = v_isSharedCheck_1870_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_1862_ = crate::leanh::lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1870_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1855_);
                    crate::leanh::lean_dec(v_a_1832_);
                    if v_isShared_1858_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1857_, 0, v_code_1750_);
                        v___x_1874_ = v___x_1857_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_code_1750_);
                        v___x_1874_ = v_reuseFailAlloc_1875_;
                        state = 26;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1862_, 1, v_a_1832_);
                    crate::leanh::lean_ctor_set(v___x_1862_, 0, v_a_1855_);
                    v___x_1865_ = v___x_1862_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_a_1832_);
                    v___x_1865_ = v_reuseFailAlloc_1869_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_1858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1857_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1867_;
            }
            26 => {
                return v___x_1874_;
            }
            27 => {
                if v_isShared_1886_ == 0 {
                    v___x_1888_ = v___x_1885_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
                    v___x_1888_ = v_reuseFailAlloc_1889_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1888_;
            }
            29 => {
                if v_isShared_1902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v_a_1894_);
                    v___x_1904_ = v___x_1901_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1894_);
                    v___x_1904_ = v_reuseFailAlloc_1905_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1904_;
            }
            31 => {
                if v_isShared_1911_ == 0 {
                    v___x_1913_ = v___x_1910_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1913_;
            }
            33 => {
                v___x_1938_ = lean_ptr_addr(v_k_1892_);
                v___x_1939_ = lean_ptr_addr(v_a_1894_);
                v___x_1940_ = lean_usize_dec_eq(v___x_1938_, v___x_1939_);
                if v___x_1940_ == 0 {
                    v___y_1922_ = v___x_1940_;
                    state = 34;
                    continue;
                } else {
                    v___x_1941_ = lean_ptr_addr(v_decl_1891_);
                    v___x_1942_ = lean_ptr_addr(v_a_1917_);
                    v___x_1943_ = lean_usize_dec_eq(v___x_1941_, v___x_1942_);
                    v___y_1922_ = v___x_1943_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v___y_1922_ == 0 {
                    v_isSharedCheck_1932_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v_unused_1933_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_1933_);
                        v_unused_1934_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_1934_);
                        v___x_1924_ = v_code_1750_;
                        v_isShared_1925_ = v_isSharedCheck_1932_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_1924_ = crate::leanh::lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1932_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1917_);
                    crate::leanh::lean_dec(v_a_1894_);
                    if v_isShared_1920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1919_, 0, v_code_1750_);
                        v___x_1936_ = v___x_1919_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_code_1750_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_1925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1924_, 1, v_a_1894_);
                    crate::leanh::lean_ctor_set(v___x_1924_, 0, v_a_1917_);
                    v___x_1927_ = v___x_1924_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_a_1894_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1919_, 0, v___x_1927_);
                    v___x_1929_ = v___x_1919_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1929_;
            }
            38 => {
                return v___x_1936_;
            }
            39 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_1950_;
            }
            41 => {
                v___x_1979_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_1975_);
                v___x_1980_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_1749_, v___x_1979_, v_alts_1975_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                if crate::leanh::lean_obj_tag(v___x_1980_) == 0 {
                    v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                    v_isSharedCheck_2009_ = (!crate::leanh::lean_is_exclusive(v___x_1980_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_1983_ = v___x_1980_;
                        v_isShared_1984_ = v_isSharedCheck_2009_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1981_);
                        crate::leanh::lean_dec(v___x_1980_);
                        v___x_1983_ = crate::leanh::lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_2009_;
                        state = 42;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1977_);
                    crate::leanh::lean_dec_ref(v_alts_1975_);
                    crate::leanh::lean_dec(v_discr_1974_);
                    crate::leanh::lean_dec_ref(v_resultType_1973_);
                    crate::leanh::lean_dec(v_typeName_1972_);
                    crate::leanh::lean_dec_ref_known(v_code_1750_, 1);
                    v_a_2010_ = crate::leanh::lean_ctor_get(v___x_1980_, 0);
                    v_isSharedCheck_2017_ = (!crate::leanh::lean_is_exclusive(v___x_1980_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_2012_ = v___x_1980_;
                        v_isShared_2013_ = v_isSharedCheck_2017_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2010_);
                        crate::leanh::lean_dec(v___x_1980_);
                        v___x_2012_ = crate::leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2017_;
                        state = 48;
                        continue;
                    }
                }
            }
            42 => {
                v___x_1985_ = lean_st_ref_take(v_a_1751_);
                v___x_1986_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_discr_1974_);
                v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_1985_, v_discr_1974_, v___x_1986_);
                v___x_1988_ = lean_st_ref_set(v_a_1751_, v___x_1987_);
                v___x_1989_ = lean_ptr_addr(v_alts_1975_);
                crate::leanh::lean_dec_ref(v_alts_1975_);
                v___x_1990_ = lean_ptr_addr(v_a_1981_);
                v___x_1991_ = lean_usize_dec_eq(v___x_1989_, v___x_1990_);
                if v___x_1991_ == 0 {
                    v_isSharedCheck_2004_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v_unused_2005_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_2005_);
                        v___x_1993_ = v_code_1750_;
                        v_isShared_1994_ = v_isSharedCheck_2004_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_1993_ = crate::leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2004_;
                        state = 43;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1981_);
                    crate::leanh::lean_del_object(v___x_1977_);
                    crate::leanh::lean_dec(v_discr_1974_);
                    crate::leanh::lean_dec_ref(v_resultType_1973_);
                    crate::leanh::lean_dec(v_typeName_1972_);
                    if v_isShared_1984_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1983_, 0, v_code_1750_);
                        v___x_2007_ = v___x_1983_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_2008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_code_1750_);
                        v___x_2007_ = v_reuseFailAlloc_2008_;
                        state = 47;
                        continue;
                    }
                }
            }
            43 => {
                if v_isShared_1978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1977_, 3, v_a_1981_);
                    v___x_1996_ = v___x_1977_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_typeName_1972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_resultType_1973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_discr_1974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_a_1981_);
                    v___x_1996_ = v_reuseFailAlloc_2003_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1993_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2002_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1983_, 0, v___x_1998_);
                    v___x_2000_ = v___x_1983_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
                    v___x_2000_ = v_reuseFailAlloc_2001_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2000_;
            }
            47 => {
                return v___x_2007_;
            }
            48 => {
                if v_isShared_2013_ == 0 {
                    v___x_2015_ = v___x_2012_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_2015_;
            }
            50 => {
                v___x_2035_ = lean_st_ref_get(v_a_1751_);
                v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_2035_, v_fvarId_2026_);
                crate::leanh::lean_dec(v___x_2035_);
                if v___x_2036_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_code_1750_, 4);
                    if v_isShared_2034_ == 0 {
                        v___x_2038_ = v___x_2033_;
                        state = 51;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2031_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 51;
                        continue;
                    }
                } else {
                    v___x_2040_ = lean_st_ref_take(v_a_1751_);
                    crate::leanh::lean_inc(v_y_2028_);
                    v___x_2041_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_2040_, v_y_2028_);
                    v___x_2042_ = lean_st_ref_set(v_a_1751_, v___x_2041_);
                    v___x_2043_ = lean_ptr_addr(v_k_2029_);
                    v___x_2044_ = lean_ptr_addr(v_a_2031_);
                    v___x_2045_ = lean_usize_dec_eq(v___x_2043_, v___x_2044_);
                    if v___x_2045_ == 0 {
                        crate::leanh::lean_inc(v_y_2028_);
                        crate::leanh::lean_inc(v_i_2027_);
                        crate::leanh::lean_inc(v_fvarId_2026_);
                        v_isSharedCheck_2055_ =
                            (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2055_ == 0 {
                            v_unused_2056_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                            crate::leanh::lean_dec(v_unused_2056_);
                            v_unused_2057_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                            crate::leanh::lean_dec(v_unused_2057_);
                            v_unused_2058_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                            crate::leanh::lean_dec(v_unused_2058_);
                            v_unused_2059_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                            crate::leanh::lean_dec(v_unused_2059_);
                            v___x_2047_ = v_code_1750_;
                            v_isShared_2048_ = v_isSharedCheck_2055_;
                            state = 52;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_1750_);
                            v___x_2047_ = crate::leanh::lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2055_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2031_);
                        if v_isShared_2034_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2033_, 0, v_code_1750_);
                            v___x_2061_ = v___x_2033_;
                            state = 55;
                            continue;
                        } else {
                            v_reuseFailAlloc_2062_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_code_1750_);
                            v___x_2061_ = v_reuseFailAlloc_2062_;
                            state = 55;
                            continue;
                        }
                    }
                }
            }
            51 => {
                return v___x_2038_;
            }
            52 => {
                if v_isShared_2048_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2047_, 3, v_a_2031_);
                    v___x_2050_ = v___x_2047_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_fvarId_2026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_i_2027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_y_2028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_a_2031_);
                    v___x_2050_ = v_reuseFailAlloc_2054_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_2034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2033_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2052_;
            }
            55 => {
                return v___x_2061_;
            }
            56 => {
                v___x_2073_ = lean_st_ref_get(v_a_1751_);
                v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_2073_, v_fvarId_2064_);
                crate::leanh::lean_dec(v___x_2073_);
                if v___x_2074_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_code_1750_, 4);
                    if v_isShared_2072_ == 0 {
                        v___x_2076_ = v___x_2071_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2069_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 57;
                        continue;
                    }
                } else {
                    v___x_2078_ = lean_st_ref_take(v_a_1751_);
                    v___x_2079_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_y_2066_);
                    v___x_2080_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2078_, v_y_2066_, v___x_2079_);
                    v___x_2081_ = lean_st_ref_set(v_a_1751_, v___x_2080_);
                    v___x_2082_ = lean_ptr_addr(v_k_2067_);
                    v___x_2083_ = lean_ptr_addr(v_a_2069_);
                    v___x_2084_ = lean_usize_dec_eq(v___x_2082_, v___x_2083_);
                    if v___x_2084_ == 0 {
                        crate::leanh::lean_inc(v_y_2066_);
                        crate::leanh::lean_inc(v_i_2065_);
                        crate::leanh::lean_inc(v_fvarId_2064_);
                        v_isSharedCheck_2094_ =
                            (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2094_ == 0 {
                            v_unused_2095_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                            crate::leanh::lean_dec(v_unused_2095_);
                            v_unused_2096_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                            crate::leanh::lean_dec(v_unused_2096_);
                            v_unused_2097_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                            crate::leanh::lean_dec(v_unused_2097_);
                            v_unused_2098_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                            crate::leanh::lean_dec(v_unused_2098_);
                            v___x_2086_ = v_code_1750_;
                            v_isShared_2087_ = v_isSharedCheck_2094_;
                            state = 58;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_1750_);
                            v___x_2086_ = crate::leanh::lean_box(0);
                            v_isShared_2087_ = v_isSharedCheck_2094_;
                            state = 58;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2069_);
                        if v_isShared_2072_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2071_, 0, v_code_1750_);
                            v___x_2100_ = v___x_2071_;
                            state = 61;
                            continue;
                        } else {
                            v_reuseFailAlloc_2101_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_code_1750_);
                            v___x_2100_ = v_reuseFailAlloc_2101_;
                            state = 61;
                            continue;
                        }
                    }
                }
            }
            57 => {
                return v___x_2076_;
            }
            58 => {
                if v_isShared_2087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2086_, 3, v_a_2069_);
                    v___x_2089_ = v___x_2086_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_fvarId_2064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_i_2065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_y_2066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_a_2069_);
                    v___x_2089_ = v_reuseFailAlloc_2093_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_2072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2071_, 0, v___x_2089_);
                    v___x_2091_ = v___x_2071_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
                    v___x_2091_ = v_reuseFailAlloc_2092_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2091_;
            }
            61 => {
                return v___x_2100_;
            }
            62 => {
                v___x_2114_ = lean_st_ref_get(v_a_1751_);
                v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_2114_, v_fvarId_2103_);
                crate::leanh::lean_dec(v___x_2114_);
                if v___x_2115_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_code_1750_, 6);
                    if v_isShared_2113_ == 0 {
                        v___x_2117_ = v___x_2112_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_2118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2110_);
                        v___x_2117_ = v_reuseFailAlloc_2118_;
                        state = 63;
                        continue;
                    }
                } else {
                    v___x_2119_ = lean_st_ref_take(v_a_1751_);
                    v___x_2120_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_y_2106_);
                    v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2119_, v_y_2106_, v___x_2120_);
                    v___x_2122_ = lean_st_ref_set(v_a_1751_, v___x_2121_);
                    v___x_2123_ = lean_ptr_addr(v_k_2108_);
                    v___x_2124_ = lean_ptr_addr(v_a_2110_);
                    v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
                    if v___x_2125_ == 0 {
                        crate::leanh::lean_inc_ref(v_ty_2107_);
                        crate::leanh::lean_inc(v_y_2106_);
                        crate::leanh::lean_inc(v_offset_2105_);
                        crate::leanh::lean_inc(v_i_2104_);
                        crate::leanh::lean_inc(v_fvarId_2103_);
                        v_isSharedCheck_2135_ =
                            (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v_unused_2136_ = crate::leanh::lean_ctor_get(v_code_1750_, 5);
                            crate::leanh::lean_dec(v_unused_2136_);
                            v_unused_2137_ = crate::leanh::lean_ctor_get(v_code_1750_, 4);
                            crate::leanh::lean_dec(v_unused_2137_);
                            v_unused_2138_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                            crate::leanh::lean_dec(v_unused_2138_);
                            v_unused_2139_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                            crate::leanh::lean_dec(v_unused_2139_);
                            v_unused_2140_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                            crate::leanh::lean_dec(v_unused_2140_);
                            v_unused_2141_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                            crate::leanh::lean_dec(v_unused_2141_);
                            v___x_2127_ = v_code_1750_;
                            v_isShared_2128_ = v_isSharedCheck_2135_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_1750_);
                            v___x_2127_ = crate::leanh::lean_box(0);
                            v_isShared_2128_ = v_isSharedCheck_2135_;
                            state = 64;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2110_);
                        if v_isShared_2113_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2112_, 0, v_code_1750_);
                            v___x_2143_ = v___x_2112_;
                            state = 67;
                            continue;
                        } else {
                            v_reuseFailAlloc_2144_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_code_1750_);
                            v___x_2143_ = v_reuseFailAlloc_2144_;
                            state = 67;
                            continue;
                        }
                    }
                }
            }
            63 => {
                return v___x_2117_;
            }
            64 => {
                if v_isShared_2128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2127_, 5, v_a_2110_);
                    v___x_2130_ = v___x_2127_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fvarId_2103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_i_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_offset_2105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_y_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_ty_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 5, v_a_2110_);
                    v___x_2130_ = v_reuseFailAlloc_2134_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                if v_isShared_2113_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2112_, 0, v___x_2130_);
                    v___x_2132_ = v___x_2112_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
                    v___x_2132_ = v_reuseFailAlloc_2133_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_2132_;
            }
            67 => {
                return v___x_2143_;
            }
            68 => {
                v___x_2154_ = lean_st_ref_take(v_a_1751_);
                v___x_2155_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fvarId_2146_);
                v___x_2156_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2154_, v_fvarId_2146_, v___x_2155_);
                v___x_2157_ = lean_st_ref_set(v_a_1751_, v___x_2156_);
                v___x_2158_ = lean_ptr_addr(v_k_2148_);
                v___x_2159_ = lean_ptr_addr(v_a_2150_);
                v___x_2160_ = lean_usize_dec_eq(v___x_2158_, v___x_2159_);
                if v___x_2160_ == 0 {
                    crate::leanh::lean_inc(v_cidx_2147_);
                    crate::leanh::lean_inc(v_fvarId_2146_);
                    v_isSharedCheck_2170_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2170_ == 0 {
                        v_unused_2171_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        crate::leanh::lean_dec(v_unused_2171_);
                        v_unused_2172_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_2172_);
                        v_unused_2173_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_2173_);
                        v___x_2162_ = v_code_1750_;
                        v_isShared_2163_ = v_isSharedCheck_2170_;
                        state = 69;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_2162_ = crate::leanh::lean_box(0);
                        v_isShared_2163_ = v_isSharedCheck_2170_;
                        state = 69;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2150_);
                    if v_isShared_2153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2152_, 0, v_code_1750_);
                        v___x_2175_ = v___x_2152_;
                        state = 72;
                        continue;
                    } else {
                        v_reuseFailAlloc_2176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_code_1750_);
                        v___x_2175_ = v_reuseFailAlloc_2176_;
                        state = 72;
                        continue;
                    }
                }
            }
            69 => {
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 2, v_a_2150_);
                    v___x_2165_ = v___x_2162_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_fvarId_2146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_cidx_2147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_a_2150_);
                    v___x_2165_ = v_reuseFailAlloc_2169_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2165_);
                    v___x_2167_ = v___x_2152_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_2167_;
            }
            72 => {
                return v___x_2175_;
            }
            73 => {
                v___x_2188_ = lean_st_ref_take(v_a_1751_);
                v___x_2189_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fvarId_2178_);
                v___x_2190_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2188_, v_fvarId_2178_, v___x_2189_);
                v___x_2191_ = lean_st_ref_set(v_a_1751_, v___x_2190_);
                v___x_2192_ = lean_ptr_addr(v_k_2182_);
                v___x_2193_ = lean_ptr_addr(v_a_2184_);
                v___x_2194_ = lean_usize_dec_eq(v___x_2192_, v___x_2193_);
                if v___x_2194_ == 0 {
                    crate::leanh::lean_inc(v_n_2179_);
                    crate::leanh::lean_inc(v_fvarId_2178_);
                    v_isSharedCheck_2204_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2204_ == 0 {
                        v_unused_2205_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        crate::leanh::lean_dec(v_unused_2205_);
                        v_unused_2206_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_2206_);
                        v_unused_2207_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_2207_);
                        v___x_2196_ = v_code_1750_;
                        v_isShared_2197_ = v_isSharedCheck_2204_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_2196_ = crate::leanh::lean_box(0);
                        v_isShared_2197_ = v_isSharedCheck_2204_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2184_);
                    if v_isShared_2187_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2186_, 0, v_code_1750_);
                        v___x_2209_ = v___x_2186_;
                        state = 77;
                        continue;
                    } else {
                        v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_code_1750_);
                        v___x_2209_ = v_reuseFailAlloc_2210_;
                        state = 77;
                        continue;
                    }
                }
            }
            74 => {
                if v_isShared_2197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2196_, 2, v_a_2184_);
                    v___x_2199_ = v___x_2196_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_fvarId_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_n_2179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_a_2184_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2203_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_2180_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2203_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_2181_,
                    );
                    v___x_2199_ = v_reuseFailAlloc_2203_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_2187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2199_);
                    v___x_2201_ = v___x_2186_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_2201_;
            }
            77 => {
                return v___x_2209_;
            }
            78 => {
                v___x_2223_ = lean_st_ref_take(v_a_1751_);
                v___x_2224_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fvarId_2212_);
                v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2223_, v_fvarId_2212_, v___x_2224_);
                v___x_2226_ = lean_st_ref_set(v_a_1751_, v___x_2225_);
                v___x_2227_ = lean_ptr_addr(v_k_2217_);
                v___x_2228_ = lean_ptr_addr(v_a_2219_);
                v___x_2229_ = lean_usize_dec_eq(v___x_2227_, v___x_2228_);
                if v___x_2229_ == 0 {
                    crate::leanh::lean_inc(v_objs_x3f_2216_);
                    crate::leanh::lean_inc(v_n_2213_);
                    crate::leanh::lean_inc(v_fvarId_2212_);
                    v_isSharedCheck_2239_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v_unused_2240_ = crate::leanh::lean_ctor_get(v_code_1750_, 3);
                        crate::leanh::lean_dec(v_unused_2240_);
                        v_unused_2241_ = crate::leanh::lean_ctor_get(v_code_1750_, 2);
                        crate::leanh::lean_dec(v_unused_2241_);
                        v_unused_2242_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_2242_);
                        v_unused_2243_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_2243_);
                        v___x_2231_ = v_code_1750_;
                        v_isShared_2232_ = v_isSharedCheck_2239_;
                        state = 79;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_2231_ = crate::leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2239_;
                        state = 79;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2219_);
                    if v_isShared_2222_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2221_, 0, v_code_1750_);
                        v___x_2245_ = v___x_2221_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_2246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_code_1750_);
                        v___x_2245_ = v_reuseFailAlloc_2246_;
                        state = 82;
                        continue;
                    }
                }
            }
            79 => {
                if v_isShared_2232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2231_, 3, v_a_2219_);
                    v___x_2234_ = v___x_2231_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_fvarId_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_n_2213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_objs_x3f_2216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_a_2219_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_2214_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_2215_,
                    );
                    v___x_2234_ = v_reuseFailAlloc_2238_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_2222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2234_);
                    v___x_2236_ = v___x_2221_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
                    v___x_2236_ = v_reuseFailAlloc_2237_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_2236_;
            }
            82 => {
                return v___x_2245_;
            }
            83 => {
                v___x_2255_ = lean_st_ref_take(v_a_1751_);
                v___x_2256_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fvarId_2248_);
                v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2255_, v_fvarId_2248_, v___x_2256_);
                v___x_2258_ = lean_st_ref_set(v_a_1751_, v___x_2257_);
                v___x_2259_ = lean_ptr_addr(v_k_2249_);
                v___x_2260_ = lean_ptr_addr(v_a_2251_);
                v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
                if v___x_2261_ == 0 {
                    crate::leanh::lean_inc(v_fvarId_2248_);
                    v_isSharedCheck_2271_ = (!crate::leanh::lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = crate::leanh::lean_ctor_get(v_code_1750_, 1);
                        crate::leanh::lean_dec(v_unused_2272_);
                        v_unused_2273_ = crate::leanh::lean_ctor_get(v_code_1750_, 0);
                        crate::leanh::lean_dec(v_unused_2273_);
                        v___x_2263_ = v_code_1750_;
                        v_isShared_2264_ = v_isSharedCheck_2271_;
                        state = 84;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1750_);
                        v___x_2263_ = crate::leanh::lean_box(0);
                        v_isShared_2264_ = v_isSharedCheck_2271_;
                        state = 84;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2251_);
                    if v_isShared_2254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2253_, 0, v_code_1750_);
                        v___x_2275_ = v___x_2253_;
                        state = 87;
                        continue;
                    } else {
                        v_reuseFailAlloc_2276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_code_1750_);
                        v___x_2275_ = v_reuseFailAlloc_2276_;
                        state = 87;
                        continue;
                    }
                }
            }
            84 => {
                if v_isShared_2264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2263_, 1, v_a_2251_);
                    v___x_2266_ = v___x_2263_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_fvarId_2248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2251_);
                    v___x_2266_ = v_reuseFailAlloc_2270_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_2254_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2253_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2268_;
            }
            87 => {
                return v___x_2275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(
    mut v_pu_2278_: u8,
    mut v_funDecl_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_2286_ = crate::leanh::lean_ctor_get(v_funDecl_2279_, 2);
                crate::leanh::lean_inc_ref(v_params_2286_);
                v_type_2287_ = crate::leanh::lean_ctor_get(v_funDecl_2279_, 3);
                crate::leanh::lean_inc_ref(v_type_2287_);
                v_value_2288_ = crate::leanh::lean_ctor_get(v_funDecl_2279_, 4);
                crate::leanh::lean_inc_ref(v_value_2288_);
                v___x_2289_ =
                    l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
                        v_pu_2278_,
                        v_value_2288_,
                        v_a_2280_,
                        v_a_2281_,
                        v_a_2282_,
                        v_a_2283_,
                        v_a_2284_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2289_) == 0 {
                    v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2289_, 0);
                    crate::leanh::lean_inc(v_a_2290_);
                    crate::leanh::lean_dec_ref_known(v___x_2289_, 1);
                    v___x_2291_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2278_, v_funDecl_2279_, v_type_2287_, v_params_2286_, v_a_2290_, v_a_2282_);
                    return v___x_2291_;
                } else {
                    crate::leanh::lean_dec_ref(v_type_2287_);
                    crate::leanh::lean_dec_ref(v_params_2286_);
                    crate::leanh::lean_dec_ref(v_funDecl_2279_);
                    v_a_2292_ = crate::leanh::lean_ctor_get(v___x_2289_, 0);
                    v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v___x_2289_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v___x_2294_ = v___x_2289_;
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2292_);
                        crate::leanh::lean_dec(v___x_2289_);
                        v___x_2294_ = crate::leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2295_ == 0 {
                    v___x_2297_ = v___x_2294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(
    mut v_pu_2300_: *mut crate::leanh::LeanObject,
    mut v_funDecl_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
    mut v_a_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2308_: u8 = 0;
    let mut v_res_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2308_ = (crate::leanh::lean_unbox(v_pu_2300_) as u8);
    v_res_2309_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(
        v_pu_boxed_2308_,
        v_funDecl_2301_,
        v_a_2302_,
        v_a_2303_,
        v_a_2304_,
        v_a_2305_,
        v_a_2306_,
    );
    crate::leanh::lean_dec(v_a_2306_);
    crate::leanh::lean_dec_ref(v_a_2305_);
    crate::leanh::lean_dec(v_a_2304_);
    crate::leanh::lean_dec_ref(v_a_2303_);
    crate::leanh::lean_dec(v_a_2302_);
    return v_res_2309_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(
    mut v_pu_2310_: *mut crate::leanh::LeanObject,
    mut v_i_2311_: *mut crate::leanh::LeanObject,
    mut v_as_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2319_: u8 = 0;
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2319_ = (crate::leanh::lean_unbox(v_pu_2310_) as u8);
    v_res_2320_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_2319_, v_i_2311_, v_as_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    crate::leanh::lean_dec(v___y_2317_);
    crate::leanh::lean_dec_ref(v___y_2316_);
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec_ref(v___y_2314_);
    crate::leanh::lean_dec(v___y_2313_);
    return v_res_2320_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(
    mut v_pu_2321_: *mut crate::leanh::LeanObject,
    mut v_code_2322_: *mut crate::leanh::LeanObject,
    mut v_a_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_a_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2329_: u8 = 0;
    let mut v_res_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2329_ = (crate::leanh::lean_unbox(v_pu_2321_) as u8);
    v_res_2330_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
        v_pu_boxed_2329_,
        v_code_2322_,
        v_a_2323_,
        v_a_2324_,
        v_a_2325_,
        v_a_2326_,
        v_a_2327_,
    );
    crate::leanh::lean_dec(v_a_2327_);
    crate::leanh::lean_dec_ref(v_a_2326_);
    crate::leanh::lean_dec(v_a_2325_);
    crate::leanh::lean_dec_ref(v_a_2324_);
    crate::leanh::lean_dec(v_a_2323_);
    return v_res_2330_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(
    mut v_00_u03b2_2331_: *mut crate::leanh::LeanObject,
    mut v_m_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2334_: u8 = 0;
    v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_2332_, v_a_2333_);
    return v___x_2334_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(
    mut v_00_u03b2_2335_: *mut crate::leanh::LeanObject,
    mut v_m_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_2335_, v_m_2336_, v_a_2337_);
    crate::leanh::lean_dec(v_a_2337_);
    crate::leanh::lean_dec_ref(v_m_2336_);
    v_r_2339_ = crate::leanh::lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(
    mut v_pu_2340_: u8,
    mut v_as_2341_: *mut crate::leanh::LeanObject,
    mut v_i_2342_: usize,
    mut v_stop_2343_: usize,
    mut v_b_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_2341_, v_i_2342_, v_stop_2343_, v_b_2344_, v___y_2345_);
    return v___x_2351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(
    mut v_pu_2352_: *mut crate::leanh::LeanObject,
    mut v_as_2353_: *mut crate::leanh::LeanObject,
    mut v_i_2354_: *mut crate::leanh::LeanObject,
    mut v_stop_2355_: *mut crate::leanh::LeanObject,
    mut v_b_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2363_: u8 = 0;
    let mut v_i_boxed_2364_: usize = 0;
    let mut v_stop_boxed_2365_: usize = 0;
    let mut v_res_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2363_ = (crate::leanh::lean_unbox(v_pu_2352_) as u8);
    v_i_boxed_2364_ = crate::leanh::lean_unbox_usize(v_i_2354_);
    crate::leanh::lean_dec(v_i_2354_);
    v_stop_boxed_2365_ = crate::leanh::lean_unbox_usize(v_stop_2355_);
    crate::leanh::lean_dec(v_stop_2355_);
    v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_2363_, v_as_2353_, v_i_boxed_2364_, v_stop_boxed_2365_, v_b_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
    crate::leanh::lean_dec(v___y_2361_);
    crate::leanh::lean_dec_ref(v___y_2360_);
    crate::leanh::lean_dec(v___y_2359_);
    crate::leanh::lean_dec_ref(v___y_2358_);
    crate::leanh::lean_dec(v___y_2357_);
    crate::leanh::lean_dec_ref(v_as_2353_);
    return v_res_2366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(
    mut v_f_2367_: *mut crate::leanh::LeanObject,
    mut v_v_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_a_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2397_: u8 = 0;
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2368_) == 0 {
                    v_code_2374_ = crate::leanh::lean_ctor_get(v_v_2368_, 0);
                    v_isSharedCheck_2398_ = (!crate::leanh::lean_is_exclusive(v_v_2368_)) as u8;
                    if v_isSharedCheck_2398_ == 0 {
                        v___x_2376_ = v_v_2368_;
                        v_isShared_2377_ = v_isSharedCheck_2398_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_2374_);
                        crate::leanh::lean_dec(v_v_2368_);
                        v___x_2376_ = crate::leanh::lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2398_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2367_);
                    v___x_2399_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2399_, 0, v_v_2368_);
                    return v___x_2399_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2372_);
                crate::leanh::lean_inc_ref(v___y_2371_);
                crate::leanh::lean_inc(v___y_2370_);
                crate::leanh::lean_inc_ref(v___y_2369_);
                v___x_2378_ = crate::leanh::lean_apply_6(
                    v_f_2367_,
                    v_code_2374_,
                    v___y_2369_,
                    v___y_2370_,
                    v___y_2371_,
                    v___y_2372_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2378_) == 0 {
                    v_a_2379_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                    v_isSharedCheck_2389_ = (!crate::leanh::lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2381_ = v___x_2378_;
                        v_isShared_2382_ = v_isSharedCheck_2389_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2379_);
                        crate::leanh::lean_dec(v___x_2378_);
                        v___x_2381_ = crate::leanh::lean_box(0);
                        v_isShared_2382_ = v_isSharedCheck_2389_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2376_);
                    v_a_2390_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                    v_isSharedCheck_2397_ = (!crate::leanh::lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2397_ == 0 {
                        v___x_2392_ = v___x_2378_;
                        v_isShared_2393_ = v_isSharedCheck_2397_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2390_);
                        crate::leanh::lean_dec(v___x_2378_);
                        v___x_2392_ = crate::leanh::lean_box(0);
                        v_isShared_2393_ = v_isSharedCheck_2397_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2376_, 0, v_a_2379_);
                    v___x_2384_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2381_, 0, v___x_2384_);
                    v___x_2386_ = v___x_2381_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
                    v___x_2386_ = v_reuseFailAlloc_2387_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2386_;
            }
            5 => {
                if v_isShared_2393_ == 0 {
                    v___x_2395_ = v___x_2392_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
                    v___x_2395_ = v_reuseFailAlloc_2396_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(
    mut v_f_2400_: *mut crate::leanh::LeanObject,
    mut v_v_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_2400_, v_v_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    crate::leanh::lean_dec(v___y_2405_);
    crate::leanh::lean_dec_ref(v___y_2404_);
    crate::leanh::lean_dec(v___y_2403_);
    crate::leanh::lean_dec_ref(v___y_2402_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(
    mut v_pu_2408_: u8,
    mut v_f_2409_: *mut crate::leanh::LeanObject,
    mut v_v_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_2409_, v_v_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
    return v___x_2416_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(
    mut v_pu_2417_: *mut crate::leanh::LeanObject,
    mut v_f_2418_: *mut crate::leanh::LeanObject,
    mut v_v_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2425_ = (crate::leanh::lean_unbox(v_pu_2417_) as u8);
    v_res_2426_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_2425_, v_f_2418_, v_v_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
    crate::leanh::lean_dec(v___y_2423_);
    crate::leanh::lean_dec_ref(v___y_2422_);
    crate::leanh::lean_dec(v___y_2421_);
    crate::leanh::lean_dec_ref(v___y_2420_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(
    mut v___x_2427_: *mut crate::leanh::LeanObject,
    mut v_pu_2428_: u8,
    mut v_code_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2435_ = lean_st_mk_ref(v___x_2427_);
                v___x_2436_ =
                    l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
                        v_pu_2428_,
                        v_code_2429_,
                        v___x_2435_,
                        v___y_2430_,
                        v___y_2431_,
                        v___y_2432_,
                        v___y_2433_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2436_) == 0 {
                    v_a_2437_ = crate::leanh::lean_ctor_get(v___x_2436_, 0);
                    v_isSharedCheck_2445_ = (!crate::leanh::lean_is_exclusive(v___x_2436_)) as u8;
                    if v_isSharedCheck_2445_ == 0 {
                        v___x_2439_ = v___x_2436_;
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2437_);
                        crate::leanh::lean_dec(v___x_2436_);
                        v___x_2439_ = crate::leanh::lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2435_);
                    return v___x_2436_;
                }
            }
            1 => {
                v___x_2441_ = lean_st_ref_get(v___x_2435_);
                crate::leanh::lean_dec(v___x_2435_);
                crate::leanh::lean_dec(v___x_2441_);
                if v_isShared_2440_ == 0 {
                    v___x_2443_ = v___x_2439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2437_);
                    v___x_2443_ = v_reuseFailAlloc_2444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(
    mut v___x_2446_: *mut crate::leanh::LeanObject,
    mut v_pu_2447_: *mut crate::leanh::LeanObject,
    mut v_code_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2454_: u8 = 0;
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2454_ = (crate::leanh::lean_unbox(v_pu_2447_) as u8);
    v_res_2455_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(
        v___x_2446_,
        v_pu_boxed_2454_,
        v_code_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
        v___y_2452_,
    );
    crate::leanh::lean_dec(v___y_2452_);
    crate::leanh::lean_dec_ref(v___y_2451_);
    crate::leanh::lean_dec(v___y_2450_);
    crate::leanh::lean_dec_ref(v___y_2449_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars(
    mut v_pu_2456_: u8,
    mut v_decl_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2465_: u8 = 0;
    let mut v_inlineAttr_x3f_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_a_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2463_ = crate::leanh::lean_ctor_get(v_decl_2457_, 0);
                v_value_2464_ = crate::leanh::lean_ctor_get(v_decl_2457_, 1);
                v_recursive_2465_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_2457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2466_ = crate::leanh::lean_ctor_get(v_decl_2457_, 2);
                v_isSharedCheck_2493_ = (!crate::leanh::lean_is_exclusive(v_decl_2457_)) as u8;
                if v_isSharedCheck_2493_ == 0 {
                    v___x_2468_ = v_decl_2457_;
                    v_isShared_2469_ = v_isSharedCheck_2493_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_2466_);
                    crate::leanh::lean_inc(v_value_2464_);
                    crate::leanh::lean_inc(v_toSignature_2463_);
                    crate::leanh::lean_dec(v_decl_2457_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2493_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_2471_ = crate::leanh::lean_box((v_pu_2456_) as usize);
                v___f_2472_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2472_, 0, v___x_2470_);
                crate::leanh::lean_closure_set(v___f_2472_, 1, v___x_2471_);
                v___x_2473_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_2472_, v_value_2464_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                if crate::leanh::lean_obj_tag(v___x_2473_) == 0 {
                    v_a_2474_ = crate::leanh::lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2484_ = (!crate::leanh::lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2484_ == 0 {
                        v___x_2476_ = v___x_2473_;
                        v_isShared_2477_ = v_isSharedCheck_2484_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2474_);
                        crate::leanh::lean_dec(v___x_2473_);
                        v___x_2476_ = crate::leanh::lean_box(0);
                        v_isShared_2477_ = v_isSharedCheck_2484_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2468_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_2466_);
                    crate::leanh::lean_dec_ref(v_toSignature_2463_);
                    v_a_2485_ = crate::leanh::lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2492_ = (!crate::leanh::lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2492_ == 0 {
                        v___x_2487_ = v___x_2473_;
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2485_);
                        crate::leanh::lean_dec(v___x_2473_);
                        v___x_2487_ = crate::leanh::lean_box(0);
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2468_, 1, v_a_2474_);
                    v___x_2479_ = v___x_2468_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_toSignature_2463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_a_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_inlineAttr_x3f_2466_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2483_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_2465_,
                    );
                    v___x_2479_ = v_reuseFailAlloc_2483_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2479_);
                    v___x_2481_ = v___x_2476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
                    v___x_2481_ = v_reuseFailAlloc_2482_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2481_;
            }
            5 => {
                if v_isShared_2488_ == 0 {
                    v___x_2490_ = v___x_2487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
                    v___x_2490_ = v_reuseFailAlloc_2491_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(
    mut v_pu_2494_: *mut crate::leanh::LeanObject,
    mut v_decl_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2501_: u8 = 0;
    let mut v_res_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2501_ = (crate::leanh::lean_unbox(v_pu_2494_) as u8);
    v_res_2502_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(
        v_pu_boxed_2501_,
        v_decl_2495_,
        v_a_2496_,
        v_a_2497_,
        v_a_2498_,
        v_a_2499_,
    );
    crate::leanh::lean_dec(v_a_2499_);
    crate::leanh::lean_dec_ref(v_a_2498_);
    crate::leanh::lean_dec(v_a_2497_);
    crate::leanh::lean_dec_ref(v_a_2496_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Compiler_LCNF_elimDeadVars(
    mut v_phase_2506_: u8,
    mut v_occurrence_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Compiler_LCNF_elimDeadVars___closed__1;
    v___x_2509_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2506_);
    v___x_2510_ = crate::leanh::lean_box((v___x_2509_) as usize);
    v___x_2511_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2511_, 0, v___x_2510_);
    v___x_2512_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_2508_,
        v_phase_2506_,
        v___x_2511_,
        v_occurrence_2507_,
    );
    return v___x_2512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_elimDeadVars___boxed(
    mut v_phase_2513_: *mut crate::leanh::LeanObject,
    mut v_occurrence_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_2515_: u8 = 0;
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_2515_ = (crate::leanh::lean_unbox(v_phase_2513_) as u8);
    v_res_2516_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_2515_, v_occurrence_2514_);
    return v_res_2516_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: u8 = 0;
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_;
    v___x_2588_ = 1;
    v___x_2589_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_;
    v___x_2590_ = l_Lean_registerTraceClass(v___x_2587_, v___x_2588_, v___x_2589_);
    return v___x_2590_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(
    mut v_a_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
    return v_res_2592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ElimDead(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ElimDead(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ElimDead(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ElimDead(builtin);
}
