// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Lean.Compiler.LCNF.PassManager
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_elimDeadVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value)
                as *mut LeanObject,
            3124881684459225322 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_elimDeadVars___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value) as *mut LeanObject,9395430877909087188 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [69, 108, 105, 109, 68, 101, 97, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,14163133238160151269 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,6052363318432827440 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,7554273778717026953 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,5927455751105078039 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,7620594354019787370 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,7193277325485164719 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,17061857964176178842 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,4186764511736025147 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,4541933012811097981 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,9347070451442335048 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,17143492271855544088 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,((( 792928910 as usize) << 1) | 1) as *mut LeanObject,10762227741200191793 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,7626176891831604562 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,4450015759653002622 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,15569236097711012943 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(
    mut v_a_1297_: *mut LeanObject,
    mut v_x_1298_: *mut LeanObject,
) -> u8 {
    let mut v___x_1299_: u8 = 0;
    let mut v_key_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1298_) == 0 {
                    v___x_1299_ = 0;
                    return v___x_1299_;
                } else {
                    v_key_1300_ = lean_ctor_get(v_x_1298_, 0);
                    v_tail_1301_ = lean_ctor_get(v_x_1298_, 2);
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
    mut v_a_1304_: *mut LeanObject,
    mut v_x_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1306_: u8 = 0;
    let mut v_r_1307_: *mut LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1304_, v_x_1305_);
    lean_dec(v_x_1305_);
    lean_dec(v_a_1304_);
    v_r_1307_ = lean_box((v_res_1306_) as usize);
    return v_r_1307_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1308_: *mut LeanObject,
    mut v_x_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1309_) == 0 {
                    return v_x_1308_;
                } else {
                    v_key_1310_ = lean_ctor_get(v_x_1309_, 0);
                    v_value_1311_ = lean_ctor_get(v_x_1309_, 1);
                    v_tail_1312_ = lean_ctor_get(v_x_1309_, 2);
                    v_isSharedCheck_1335_ = (!lean_is_exclusive(v_x_1309_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v___x_1314_ = v_x_1309_;
                        v_isShared_1315_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1312_);
                        lean_inc(v_value_1311_);
                        lean_inc(v_key_1310_);
                        lean_dec(v_x_1309_);
                        v___x_1314_ = lean_box(0);
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
                lean_inc(v___x_1329_);
                if v_isShared_1315_ == 0 {
                    lean_ctor_set(v___x_1314_, 2, v___x_1329_);
                    v___x_1331_ = v___x_1314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_key_1310_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_value_1311_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 2, v___x_1329_);
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
    mut v_i_1336_: *mut LeanObject,
    mut v_source_1337_: *mut LeanObject,
    mut v_target_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v_es_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1339_ = lean_array_get_size(v_source_1337_);
                v___x_1340_ = lean_nat_dec_lt(v_i_1336_, v___x_1339_);
                if v___x_1340_ == 0 {
                    lean_dec_ref(v_source_1337_);
                    lean_dec(v_i_1336_);
                    return v_target_1338_;
                } else {
                    v_es_1341_ = lean_array_fget(v_source_1337_, v_i_1336_);
                    v___x_1342_ = lean_box(0);
                    v_source_1343_ = lean_array_fset(v_source_1337_, v_i_1336_, v___x_1342_);
                    v_target_1344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1338_, v_es_1341_);
                    v___x_1345_ = lean_unsigned_to_nat(1);
                    v___x_1346_ = lean_nat_add(v_i_1336_, v___x_1345_);
                    lean_dec(v_i_1336_);
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
    mut v_data_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = lean_array_get_size(v_data_1348_);
    v___x_1350_ = lean_unsigned_to_nat(2);
    v_nbuckets_1351_ = lean_nat_mul(v___x_1349_, v___x_1350_);
    v___x_1352_ = lean_unsigned_to_nat(0);
    v___x_1353_ = lean_box(0);
    v___x_1354_ = lean_mk_array(v_nbuckets_1351_, v___x_1353_);
    v___x_1355_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v___x_1352_, v_data_1348_, v___x_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(
    mut v_m_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_b_1358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1378_: u8 = 0;
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v_val_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1396_: u8 = 0;
    let mut v_unused_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1359_ = lean_ctor_get(v_m_1356_, 0);
                v_buckets_1360_ = lean_ctor_get(v_m_1356_, 1);
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
                    lean_inc_ref(v_buckets_1360_);
                    lean_inc(v_size_1359_);
                    v_isSharedCheck_1396_ = (!lean_is_exclusive(v_m_1356_)) as u8;
                    if v_isSharedCheck_1396_ == 0 {
                        v_unused_1397_ = lean_ctor_get(v_m_1356_, 1);
                        lean_dec(v_unused_1397_);
                        v_unused_1398_ = lean_ctor_get(v_m_1356_, 0);
                        lean_dec(v_unused_1398_);
                        v___x_1377_ = v_m_1356_;
                        v_isShared_1378_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_1356_);
                        v___x_1377_ = lean_box(0);
                        v_isShared_1378_ = v_isSharedCheck_1396_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1358_);
                    lean_dec(v_a_1357_);
                    return v_m_1356_;
                }
            }
            1 => {
                v___x_1379_ = lean_unsigned_to_nat(1);
                v_size_x27_1380_ = lean_nat_add(v_size_1359_, v___x_1379_);
                lean_dec(v_size_1359_);
                lean_inc(v_bkt_1374_);
                v___x_1381_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1381_, 0, v_a_1357_);
                lean_ctor_set(v___x_1381_, 1, v_b_1358_);
                lean_ctor_set(v___x_1381_, 2, v_bkt_1374_);
                v_buckets_x27_1382_ = lean_array_uset(v_buckets_1360_, v___x_1373_, v___x_1381_);
                v___x_1383_ = lean_unsigned_to_nat(4);
                v___x_1384_ = lean_nat_mul(v_size_x27_1380_, v___x_1383_);
                v___x_1385_ = lean_unsigned_to_nat(3);
                v___x_1386_ = lean_nat_div(v___x_1384_, v___x_1385_);
                lean_dec(v___x_1384_);
                v___x_1387_ = lean_array_get_size(v_buckets_x27_1382_);
                v___x_1388_ = lean_nat_dec_le(v___x_1386_, v___x_1387_);
                lean_dec(v___x_1386_);
                if v___x_1388_ == 0 {
                    v_val_1389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_buckets_x27_1382_);
                    if v_isShared_1378_ == 0 {
                        lean_ctor_set(v___x_1377_, 1, v_val_1389_);
                        lean_ctor_set(v___x_1377_, 0, v_size_x27_1380_);
                        v___x_1391_ = v___x_1377_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_size_x27_1380_);
                        lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_val_1389_);
                        v___x_1391_ = v_reuseFailAlloc_1392_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1378_ == 0 {
                        lean_ctor_set(v___x_1377_, 1, v_buckets_x27_1382_);
                        lean_ctor_set(v___x_1377_, 0, v_size_x27_1380_);
                        v___x_1394_ = v___x_1377_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_size_x27_1380_);
                        lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_buckets_x27_1382_);
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
    mut v_s_1399_: *mut LeanObject,
    mut v_arg_1400_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_1400_) == 1 {
        let mut v_fvarId_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_1401_ = lean_ctor_get(v_arg_1400_, 0);
        lean_inc(v_fvarId_1401_);
        lean_dec_ref_known(v_arg_1400_, 1);
        v___x_1402_ = lean_box(0);
        v___x_1403_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1399_, v_fvarId_1401_, v___x_1402_);
        return v___x_1403_;
    } else {
        lean_dec(v_arg_1400_);
        return v_s_1399_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(
    mut v_pu_1404_: u8,
    mut v_s_1405_: *mut LeanObject,
    mut v_arg_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v_s_1405_,
            v_arg_1406_,
        );
    return v___x_1407_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(
    mut v_pu_1408_: *mut LeanObject,
    mut v_s_1409_: *mut LeanObject,
    mut v_arg_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1411_: u8 = 0;
    let mut v_res_1412_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1411_ = (lean_unbox(v_pu_1408_) as u8);
    v_res_1412_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(
            v_pu_boxed_1411_,
            v_s_1409_,
            v_arg_1410_,
        );
    return v_res_1412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0(
    mut v_00_u03b2_1413_: *mut LeanObject,
    mut v_m_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
    mut v_b_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_m_1414_, v_a_1415_, v_b_1416_);
    return v___x_1417_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(
    mut v_00_u03b2_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_x_1420_: *mut LeanObject,
) -> u8 {
    let mut v___x_1421_: u8 = 0;
    v___x_1421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___redArg(v_a_1419_, v_x_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0___boxed(
    mut v_00_u03b2_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
    mut v_x_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__0(v_00_u03b2_1422_, v_a_1423_, v_x_1424_);
    lean_dec(v_x_1424_);
    lean_dec(v_a_1423_);
    v_r_1426_ = lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1(
    mut v_00_u03b2_1427_: *mut LeanObject,
    mut v_data_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1___redArg(v_data_1428_);
    return v___x_1429_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1430_: *mut LeanObject,
    mut v_i_1431_: *mut LeanObject,
    mut v_source_1432_: *mut LeanObject,
    mut v_target_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2___redArg(v_i_1431_, v_source_1432_, v_target_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1435_: *mut LeanObject,
    mut v_x_1436_: *mut LeanObject,
    mut v_x_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1436_, v_x_1437_);
    return v___x_1438_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(
    mut v_as_1439_: *mut LeanObject,
    mut v_i_1440_: usize,
    mut v_stop_1441_: usize,
    mut v_b_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1443_ = lean_usize_dec_eq(v_i_1440_, v_stop_1441_);
                if v___x_1443_ == 0 {
                    v___x_1444_ = lean_array_uget_borrowed(v_as_1439_, v_i_1440_);
                    lean_inc(v___x_1444_);
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
    mut v_as_1449_: *mut LeanObject,
    mut v_i_1450_: *mut LeanObject,
    mut v_stop_1451_: *mut LeanObject,
    mut v_b_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1453_: usize = 0;
    let mut v_stop_boxed_1454_: usize = 0;
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1453_ = lean_unbox_usize(v_i_1450_);
    lean_dec(v_i_1450_);
    v_stop_boxed_1454_ = lean_unbox_usize(v_stop_1451_);
    lean_dec(v_stop_1451_);
    v_res_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_1449_, v_i_boxed_1453_, v_stop_boxed_1454_, v_b_1452_);
    lean_dec_ref(v_as_1449_);
    return v_res_1455_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(
    mut v_pu_1456_: u8,
    mut v_s_1457_: *mut LeanObject,
    mut v_args_1458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    v___x_1459_ = lean_unsigned_to_nat(0);
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
                let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
                v___x_1463_ = 0usize;
                v___x_1464_ = lean_usize_of_nat(v___x_1460_);
                v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_1458_, v___x_1463_, v___x_1464_, v_s_1457_);
                return v___x_1465_;
            }
        } else {
            let mut v___x_1466_: usize = 0;
            let mut v___x_1467_: usize = 0;
            let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
            v___x_1466_ = 0usize;
            v___x_1467_ = lean_usize_of_nat(v___x_1460_);
            v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_1458_, v___x_1466_, v___x_1467_, v_s_1457_);
            return v___x_1468_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(
    mut v_pu_1469_: *mut LeanObject,
    mut v_s_1470_: *mut LeanObject,
    mut v_args_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1472_: u8 = 0;
    let mut v_res_1473_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1472_ = (lean_unbox(v_pu_1469_) as u8);
    v_res_1473_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(
            v_pu_boxed_1472_,
            v_s_1470_,
            v_args_1471_,
        );
    lean_dec_ref(v_args_1471_);
    return v_res_1473_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(
    mut v_pu_1474_: u8,
    mut v_as_1475_: *mut LeanObject,
    mut v_i_1476_: usize,
    mut v_stop_1477_: usize,
    mut v_b_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_1475_, v_i_1476_, v_stop_1477_, v_b_1478_);
    return v___x_1479_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(
    mut v_pu_1480_: *mut LeanObject,
    mut v_as_1481_: *mut LeanObject,
    mut v_i_1482_: *mut LeanObject,
    mut v_stop_1483_: *mut LeanObject,
    mut v_b_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1485_: u8 = 0;
    let mut v_i_boxed_1486_: usize = 0;
    let mut v_stop_boxed_1487_: usize = 0;
    let mut v_res_1488_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1485_ = (lean_unbox(v_pu_1480_) as u8);
    v_i_boxed_1486_ = lean_unbox_usize(v_i_1482_);
    lean_dec(v_i_1482_);
    v_stop_boxed_1487_ = lean_unbox_usize(v_stop_1483_);
    lean_dec(v_stop_1483_);
    v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_1485_, v_as_1481_, v_i_boxed_1486_, v_stop_boxed_1487_, v_b_1484_);
    lean_dec_ref(v_as_1481_);
    return v_res_1488_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
    mut v_pu_1489_: u8,
    mut v_s_1490_: *mut LeanObject,
    mut v_e_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_1491_) {
                2 => {
                    v_struct_1500_ = lean_ctor_get(v_e_1491_, 2);
                    lean_inc(v_struct_1500_);
                    lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1501_ = lean_box(0);
                    v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_struct_1500_, v___x_1501_);
                    return v___x_1502_;
                }
                3 => {
                    v_args_1503_ = lean_ctor_get(v_e_1491_, 2);
                    lean_inc_ref(v_args_1503_);
                    lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1504_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1503_);
                    lean_dec_ref(v_args_1503_);
                    return v___x_1504_;
                }
                4 => {
                    v_fvarId_1505_ = lean_ctor_get(v_e_1491_, 0);
                    lean_inc(v_fvarId_1505_);
                    v_args_1506_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc_ref(v_args_1506_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1507_ = lean_box(0);
                    v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1505_, v___x_1507_);
                    v___x_1509_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v___x_1508_, v_args_1506_);
                    lean_dec_ref(v_args_1506_);
                    return v___x_1509_;
                }
                5 => {
                    v_args_1510_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc_ref(v_args_1510_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1511_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1510_);
                    lean_dec_ref(v_args_1510_);
                    return v___x_1511_;
                }
                6 => {
                    v_var_1512_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc(v_var_1512_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1512_;
                    state = 2;
                    continue;
                }
                7 => {
                    v_var_1513_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc(v_var_1513_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1513_;
                    state = 2;
                    continue;
                }
                8 => {
                    v_var_1514_ = lean_ctor_get(v_e_1491_, 2);
                    lean_inc(v_var_1514_);
                    lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1515_ = lean_box(0);
                    v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_var_1514_, v___x_1515_);
                    return v___x_1516_;
                }
                9 => {
                    v_args_1517_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc_ref(v_args_1517_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1518_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1517_);
                    lean_dec_ref(v_args_1517_);
                    return v___x_1518_;
                }
                10 => {
                    v_args_1519_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc_ref(v_args_1519_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1520_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v_s_1490_, v_args_1519_);
                    lean_dec_ref(v_args_1519_);
                    return v___x_1520_;
                }
                11 => {
                    v_var_1521_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc(v_var_1521_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v_fvarId_1497_ = v_var_1521_;
                    state = 2;
                    continue;
                }
                12 => {
                    v_var_1522_ = lean_ctor_get(v_e_1491_, 0);
                    lean_inc(v_var_1522_);
                    v_args_1523_ = lean_ctor_get(v_e_1491_, 2);
                    lean_inc_ref(v_args_1523_);
                    lean_dec_ref_known(v_e_1491_, 3);
                    v___x_1524_ = lean_box(0);
                    v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_var_1522_, v___x_1524_);
                    v___x_1526_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_1489_, v___x_1525_, v_args_1523_);
                    lean_dec_ref(v_args_1523_);
                    return v___x_1526_;
                }
                13 => {
                    v_fvarId_1527_ = lean_ctor_get(v_e_1491_, 1);
                    lean_inc(v_fvarId_1527_);
                    lean_dec_ref_known(v_e_1491_, 2);
                    v___x_1528_ = lean_box(0);
                    v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1527_, v___x_1528_);
                    return v___x_1529_;
                }
                14 => {
                    v_fvarId_1530_ = lean_ctor_get(v_e_1491_, 0);
                    lean_inc(v_fvarId_1530_);
                    lean_dec_ref_known(v_e_1491_, 1);
                    v_fvarId_1493_ = v_fvarId_1530_;
                    state = 1;
                    continue;
                }
                15 => {
                    v_fvarId_1531_ = lean_ctor_get(v_e_1491_, 0);
                    lean_inc(v_fvarId_1531_);
                    lean_dec_ref_known(v_e_1491_, 1);
                    v_fvarId_1493_ = v_fvarId_1531_;
                    state = 1;
                    continue;
                }
                _ => {
                    lean_dec(v_e_1491_);
                    return v_s_1490_;
                }
            },
            1 => {
                v___x_1494_ = lean_box(0);
                v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1493_, v___x_1494_);
                return v___x_1495_;
            }
            2 => {
                v___x_1498_ = lean_box(0);
                v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v_s_1490_, v_fvarId_1497_, v___x_1498_);
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(
    mut v_pu_1532_: *mut LeanObject,
    mut v_s_1533_: *mut LeanObject,
    mut v_e_1534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1535_: u8 = 0;
    let mut v_res_1536_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1535_ = (lean_unbox(v_pu_1532_) as u8);
    v_res_1536_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_boxed_1535_,
            v_s_1533_,
            v_e_1534_,
        );
    return v_res_1536_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(
    mut v_arg_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_st_ref_take(v_a_1538_);
    v___x_1541_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v___x_1540_,
            v_arg_1537_,
        );
    v___x_1542_ = lean_st_ref_set(v_a_1538_, v___x_1541_);
    v___x_1543_ = lean_box(0);
    v___x_1544_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1544_, 0, v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(
    mut v_arg_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
    mut v_a_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1548_: *mut LeanObject = core::ptr::null_mut();
    v_res_1548_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(
            v_arg_1545_,
            v_a_1546_,
        );
    lean_dec(v_a_1546_);
    return v_res_1548_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(
    mut v_pu_1549_: u8,
    mut v_arg_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = lean_st_ref_take(v_a_1551_);
    v___x_1558_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(
            v___x_1557_,
            v_arg_1550_,
        );
    v___x_1559_ = lean_st_ref_set(v_a_1551_, v___x_1558_);
    v___x_1560_ = lean_box(0);
    v___x_1561_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(
    mut v_pu_1562_: *mut LeanObject,
    mut v_arg_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_a_1566_: *mut LeanObject,
    mut v_a_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1570_: u8 = 0;
    let mut v_res_1571_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1570_ = (lean_unbox(v_pu_1562_) as u8);
    v_res_1571_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(
        v_pu_boxed_1570_,
        v_arg_1563_,
        v_a_1564_,
        v_a_1565_,
        v_a_1566_,
        v_a_1567_,
        v_a_1568_,
    );
    lean_dec(v_a_1568_);
    lean_dec_ref(v_a_1567_);
    lean_dec(v_a_1566_);
    lean_dec_ref(v_a_1565_);
    lean_dec(v_a_1564_);
    return v_res_1571_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(
    mut v_pu_1572_: u8,
    mut v_e_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_st_ref_take(v_a_1574_);
    v___x_1577_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_1572_,
            v___x_1576_,
            v_e_1573_,
        );
    v___x_1578_ = lean_st_ref_set(v_a_1574_, v___x_1577_);
    v___x_1579_ = lean_box(0);
    v___x_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1580_, 0, v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(
    mut v_pu_1581_: *mut LeanObject,
    mut v_e_1582_: *mut LeanObject,
    mut v_a_1583_: *mut LeanObject,
    mut v_a_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1585_: u8 = 0;
    let mut v_res_1586_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1585_ = (lean_unbox(v_pu_1581_) as u8);
    v_res_1586_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(
            v_pu_boxed_1585_,
            v_e_1582_,
            v_a_1583_,
        );
    lean_dec(v_a_1583_);
    return v_res_1586_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(
    mut v_pu_1587_: u8,
    mut v_e_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
    mut v_a_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1595_ = lean_st_ref_take(v_a_1589_);
    v___x_1596_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(
            v_pu_1587_,
            v___x_1595_,
            v_e_1588_,
        );
    v___x_1597_ = lean_st_ref_set(v_a_1589_, v___x_1596_);
    v___x_1598_ = lean_box(0);
    v___x_1599_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1599_, 0, v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(
    mut v_pu_1600_: *mut LeanObject,
    mut v_e_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1608_: u8 = 0;
    let mut v_res_1609_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1608_ = (lean_unbox(v_pu_1600_) as u8);
    v_res_1609_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(
        v_pu_boxed_1608_,
        v_e_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
    );
    lean_dec(v_a_1606_);
    lean_dec_ref(v_a_1605_);
    lean_dec(v_a_1604_);
    lean_dec_ref(v_a_1603_);
    lean_dec(v_a_1602_);
    return v_res_1609_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(
    mut v_fvarId_1612_: *mut LeanObject,
    mut v_a_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1615_ = lean_st_ref_take(v_a_1613_);
    v___x_1616_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0;
    v___x_1617_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1;
    v___x_1618_ = lean_box(0);
    v___x_1619_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_1616_,
        v___x_1617_,
        v___x_1615_,
        v_fvarId_1612_,
        v___x_1618_,
    );
    v___x_1620_ = lean_st_ref_set(v_a_1613_, v___x_1619_);
    v___x_1621_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1621_, 0, v___x_1618_);
    return v___x_1621_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(
    mut v_fvarId_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1625_: *mut LeanObject = core::ptr::null_mut();
    v_res_1625_ =
        l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(
            v_fvarId_1622_,
            v_a_1623_,
        );
    lean_dec(v_a_1623_);
    return v_res_1625_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(
    mut v_fvarId_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = lean_st_ref_take(v_a_1627_);
    v___x_1634_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__0;
    v___x_1635_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___closed__1;
    v___x_1636_ = lean_box(0);
    v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_1634_,
        v___x_1635_,
        v___x_1633_,
        v_fvarId_1626_,
        v___x_1636_,
    );
    v___x_1638_ = lean_st_ref_set(v_a_1627_, v___x_1637_);
    v___x_1639_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1639_, 0, v___x_1636_);
    return v___x_1639_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(
    mut v_fvarId_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_a_1642_: *mut LeanObject,
    mut v_a_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
    mut v_a_1645_: *mut LeanObject,
    mut v_a_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1647_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(
        v_fvarId_1640_,
        v_a_1641_,
        v_a_1642_,
        v_a_1643_,
        v_a_1644_,
        v_a_1645_,
    );
    lean_dec(v_a_1645_);
    lean_dec_ref(v_a_1644_);
    lean_dec(v_a_1643_);
    lean_dec_ref(v_a_1642_);
    lean_dec(v_a_1641_);
    return v_res_1647_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(
    mut v_pu_1648_: u8,
    mut v_val_1649_: *mut LeanObject,
) -> u8 {
    if v_pu_1648_ == 0 {
        let mut v___x_1650_: u8 = 0;
        v___x_1650_ = 1;
        return v___x_1650_;
    } else {
        match lean_obj_tag(v_val_1649_) {
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
                let mut v_args_1653_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1656_: u8 = 0;
                v_args_1653_ = lean_ctor_get(v_val_1649_, 1);
                v___x_1654_ = lean_array_get_size(v_args_1653_);
                v___x_1655_ = lean_unsigned_to_nat(0);
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
    mut v_pu_1658_: *mut LeanObject,
    mut v_val_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_1660_: u8 = 0;
    let mut v_res_1661_: u8 = 0;
    let mut v_r_1662_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_1660_ = (lean_unbox(v_pu_1658_) as u8);
    v_res_1661_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(
        v_pu_boxed_1660_,
        v_val_1659_,
    );
    lean_dec(v_val_1659_);
    v_r_1662_ = lean_box((v_res_1661_) as usize);
    return v_r_1662_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(
    mut v_as_1663_: *mut LeanObject,
    mut v_i_1664_: usize,
    mut v_stop_1665_: usize,
    mut v_b_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_usize_dec_eq(v_i_1664_, v_stop_1665_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = lean_st_ref_take(v___y_1667_);
                    v___x_1671_ = lean_array_uget_borrowed(v_as_1663_, v_i_1664_);
                    lean_inc(v___x_1671_);
                    v___x_1672_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_1670_, v___x_1671_);
                    v___x_1673_ = lean_st_ref_set(v___y_1667_, v___x_1672_);
                    v___x_1674_ = lean_box(0);
                    v___x_1675_ = 1usize;
                    v___x_1676_ = lean_usize_add(v_i_1664_, v___x_1675_);
                    v_i_1664_ = v___x_1676_;
                    v_b_1666_ = v___x_1674_;
                    state = 0;
                    continue;
                } else {
                    v___x_1678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1678_, 0, v_b_1666_);
                    return v___x_1678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(
    mut v_as_1679_: *mut LeanObject,
    mut v_i_1680_: *mut LeanObject,
    mut v_stop_1681_: *mut LeanObject,
    mut v_b_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1685_: usize = 0;
    let mut v_stop_boxed_1686_: usize = 0;
    let mut v_res_1687_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1685_ = lean_unbox_usize(v_i_1680_);
    lean_dec(v_i_1680_);
    v_stop_boxed_1686_ = lean_unbox_usize(v_stop_1681_);
    lean_dec(v_stop_1681_);
    v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_1679_, v_i_boxed_1685_, v_stop_boxed_1686_, v_b_1682_, v___y_1683_);
    lean_dec(v___y_1683_);
    lean_dec_ref(v_as_1679_);
    return v_res_1687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(
    mut v_m_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    v_buckets_1690_ = lean_ctor_get(v_m_1688_, 1);
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
    mut v_m_1706_: *mut LeanObject,
    mut v_a_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1708_: u8 = 0;
    let mut v_r_1709_: *mut LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_1706_, v_a_1707_);
    lean_dec(v_a_1707_);
    lean_dec_ref(v_m_1706_);
    v_r_1709_ = lean_box((v_res_1708_) as usize);
    return v_r_1709_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(
    mut v_pu_1710_: u8,
    mut v_i_1711_: *mut LeanObject,
    mut v_as_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: u8 = 0;
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v_code_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_array_get_size(v_as_1712_);
                v___x_1720_ = lean_nat_dec_lt(v_i_1711_, v___x_1719_);
                if v___x_1720_ == 0 {
                    lean_dec(v_i_1711_);
                    v___x_1721_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1721_, 0, v_as_1712_);
                    return v___x_1721_;
                } else {
                    v_a_1722_ = lean_array_fget_borrowed(v_as_1712_, v_i_1711_);
                    match lean_obj_tag(v_a_1722_) {
                        0 => {
                            v_code_1746_ = lean_ctor_get(v_a_1722_, 2);
                            lean_inc_ref(v_code_1746_);
                            v___y_1724_ = v_code_1746_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1747_ = lean_ctor_get(v_a_1722_, 1);
                            lean_inc_ref(v_code_1747_);
                            v___y_1724_ = v_code_1747_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1748_ = lean_ctor_get(v_a_1722_, 0);
                            lean_inc_ref(v_code_1748_);
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
                if lean_obj_tag(v___x_1725_) == 0 {
                    v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
                    lean_inc(v_a_1726_);
                    lean_dec_ref_known(v___x_1725_, 1);
                    lean_inc(v_a_1722_);
                    v___x_1727_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1722_, v_a_1726_);
                    v___x_1728_ = lean_ptr_addr(v_a_1722_);
                    v___x_1729_ = lean_ptr_addr(v___x_1727_);
                    v___x_1730_ = lean_usize_dec_eq(v___x_1728_, v___x_1729_);
                    if v___x_1730_ == 0 {
                        v___x_1731_ = lean_unsigned_to_nat(1);
                        v___x_1732_ = lean_nat_add(v_i_1711_, v___x_1731_);
                        v___x_1733_ = lean_array_fset(v_as_1712_, v_i_1711_, v___x_1727_);
                        lean_dec(v_i_1711_);
                        v_i_1711_ = v___x_1732_;
                        v_as_1712_ = v___x_1733_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_1727_);
                        v___x_1735_ = lean_unsigned_to_nat(1);
                        v___x_1736_ = lean_nat_add(v_i_1711_, v___x_1735_);
                        lean_dec(v_i_1711_);
                        v_i_1711_ = v___x_1736_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_as_1712_);
                    lean_dec(v_i_1711_);
                    v_a_1738_ = lean_ctor_get(v___x_1725_, 0);
                    v_isSharedCheck_1745_ = (!lean_is_exclusive(v___x_1725_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1740_ = v___x_1725_;
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1738_);
                        lean_dec(v___x_1725_);
                        v___x_1740_ = lean_box(0);
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
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
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
    mut v_code_1750_: *mut LeanObject,
    mut v_a_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
    mut v_a_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_unused_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut v_decl_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: usize = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_unused_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: u8 = 0;
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut v_unused_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: u8 = 0;
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_decl_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___y_1860_: u8 = 0;
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_unused_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: usize = 0;
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: u8 = 0;
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_a_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut v_decl_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: u8 = 0;
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1906_: u8 = 0;
    let mut v_unused_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___y_1922_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v_unused_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: usize = 0;
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_a_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_fvarId_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: usize = 0;
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: usize = 0;
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: usize = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_fvarId_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut v_unused_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v_fvarId_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_unused_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_fvarId_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: usize = 0;
    let mut v___x_2124_: usize = 0;
    let mut v___x_2125_: u8 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2145_: u8 = 0;
    let mut v_fvarId_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_unused_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v_fvarId_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_2180_: u8 = 0;
    let mut v_persistent_2181_: u8 = 0;
    let mut v_k_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: usize = 0;
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v_unused_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_fvarId_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_2214_: u8 = 0;
    let mut v_persistent_2215_: u8 = 0;
    let mut v_objs_x3f_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v_unused_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2247_: u8 = 0;
    let mut v_fvarId_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: usize = 0;
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_code_1750_) {
                    0 => {
                        v_decl_1775_ = lean_ctor_get(v_code_1750_, 0);
                        v_k_1776_ = lean_ctor_get(v_code_1750_, 1);
                        lean_inc_ref(v_k_1776_);
                        v___x_1777_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1776_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_1777_) == 0 {
                            v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
                            v_isSharedCheck_1828_ = (!lean_is_exclusive(v___x_1777_)) as u8;
                            if v_isSharedCheck_1828_ == 0 {
                                v___x_1780_ = v___x_1777_;
                                v_isShared_1781_ = v_isSharedCheck_1828_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1778_);
                                lean_dec(v___x_1777_);
                                v___x_1780_ = lean_box(0);
                                v_isShared_1781_ = v_isSharedCheck_1828_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1777_;
                        }
                    }
                    1 => {
                        v_decl_1829_ = lean_ctor_get(v_code_1750_, 0);
                        v_k_1830_ = lean_ctor_get(v_code_1750_, 1);
                        lean_inc_ref(v_k_1830_);
                        v___x_1831_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1830_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_1831_) == 0 {
                            v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
                            lean_inc(v_a_1832_);
                            lean_dec_ref_known(v___x_1831_, 1);
                            v___x_1833_ = lean_st_ref_get(v_a_1751_);
                            v_fvarId_1834_ = lean_ctor_get(v_decl_1829_, 0);
                            v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1833_, v_fvarId_1834_);
                            lean_dec(v___x_1833_);
                            if v___x_1835_ == 0 {
                                lean_inc_ref(v_decl_1829_);
                                lean_dec_ref_known(v_code_1750_, 2);
                                v___x_1836_ = 1;
                                v___x_1837_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                                    v_pu_1749_,
                                    v_decl_1829_,
                                    v___x_1836_,
                                    v_a_1753_,
                                );
                                lean_dec_ref(v_decl_1829_);
                                if lean_obj_tag(v___x_1837_) == 0 {
                                    v_isSharedCheck_1844_ = (!lean_is_exclusive(v___x_1837_)) as u8;
                                    if v_isSharedCheck_1844_ == 0 {
                                        v_unused_1845_ = lean_ctor_get(v___x_1837_, 0);
                                        lean_dec(v_unused_1845_);
                                        v___x_1839_ = v___x_1837_;
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 17;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1837_);
                                        v___x_1839_ = lean_box(0);
                                        v_isShared_1840_ = v_isSharedCheck_1844_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1832_);
                                    v_a_1846_ = lean_ctor_get(v___x_1837_, 0);
                                    v_isSharedCheck_1853_ = (!lean_is_exclusive(v___x_1837_)) as u8;
                                    if v_isSharedCheck_1853_ == 0 {
                                        v___x_1848_ = v___x_1837_;
                                        v_isShared_1849_ = v_isSharedCheck_1853_;
                                        state = 19;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1846_);
                                        lean_dec(v___x_1837_);
                                        v___x_1848_ = lean_box(0);
                                        v_isShared_1849_ = v_isSharedCheck_1853_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc_ref(v_decl_1829_);
                                v___x_1854_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_1749_, v_decl_1829_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                                if lean_obj_tag(v___x_1854_) == 0 {
                                    v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
                                    v_isSharedCheck_1882_ = (!lean_is_exclusive(v___x_1854_)) as u8;
                                    if v_isSharedCheck_1882_ == 0 {
                                        v___x_1857_ = v___x_1854_;
                                        v_isShared_1858_ = v_isSharedCheck_1882_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1855_);
                                        lean_dec(v___x_1854_);
                                        v___x_1857_ = lean_box(0);
                                        v_isShared_1858_ = v_isSharedCheck_1882_;
                                        state = 21;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1832_);
                                    lean_dec_ref_known(v_code_1750_, 2);
                                    v_a_1883_ = lean_ctor_get(v___x_1854_, 0);
                                    v_isSharedCheck_1890_ = (!lean_is_exclusive(v___x_1854_)) as u8;
                                    if v_isSharedCheck_1890_ == 0 {
                                        v___x_1885_ = v___x_1854_;
                                        v_isShared_1886_ = v_isSharedCheck_1890_;
                                        state = 27;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1883_);
                                        lean_dec(v___x_1854_);
                                        v___x_1885_ = lean_box(0);
                                        v_isShared_1886_ = v_isSharedCheck_1890_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1831_;
                        }
                    }
                    2 => {
                        v_decl_1891_ = lean_ctor_get(v_code_1750_, 0);
                        v_k_1892_ = lean_ctor_get(v_code_1750_, 1);
                        lean_inc_ref(v_k_1892_);
                        v___x_1893_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_1892_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_1893_) == 0 {
                            v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
                            lean_inc(v_a_1894_);
                            lean_dec_ref_known(v___x_1893_, 1);
                            v___x_1895_ = lean_st_ref_get(v_a_1751_);
                            v_fvarId_1896_ = lean_ctor_get(v_decl_1891_, 0);
                            v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1895_, v_fvarId_1896_);
                            lean_dec(v___x_1895_);
                            if v___x_1897_ == 0 {
                                lean_inc_ref(v_decl_1891_);
                                lean_dec_ref_known(v_code_1750_, 2);
                                v___x_1898_ = 1;
                                v___x_1899_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                                    v_pu_1749_,
                                    v_decl_1891_,
                                    v___x_1898_,
                                    v_a_1753_,
                                );
                                lean_dec_ref(v_decl_1891_);
                                if lean_obj_tag(v___x_1899_) == 0 {
                                    v_isSharedCheck_1906_ = (!lean_is_exclusive(v___x_1899_)) as u8;
                                    if v_isSharedCheck_1906_ == 0 {
                                        v_unused_1907_ = lean_ctor_get(v___x_1899_, 0);
                                        lean_dec(v_unused_1907_);
                                        v___x_1901_ = v___x_1899_;
                                        v_isShared_1902_ = v_isSharedCheck_1906_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1899_);
                                        v___x_1901_ = lean_box(0);
                                        v_isShared_1902_ = v_isSharedCheck_1906_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1894_);
                                    v_a_1908_ = lean_ctor_get(v___x_1899_, 0);
                                    v_isSharedCheck_1915_ = (!lean_is_exclusive(v___x_1899_)) as u8;
                                    if v_isSharedCheck_1915_ == 0 {
                                        v___x_1910_ = v___x_1899_;
                                        v_isShared_1911_ = v_isSharedCheck_1915_;
                                        state = 31;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1908_);
                                        lean_dec(v___x_1899_);
                                        v___x_1910_ = lean_box(0);
                                        v_isShared_1911_ = v_isSharedCheck_1915_;
                                        state = 31;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc_ref(v_decl_1891_);
                                v___x_1916_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_1749_, v_decl_1891_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                                if lean_obj_tag(v___x_1916_) == 0 {
                                    v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
                                    v_isSharedCheck_1944_ = (!lean_is_exclusive(v___x_1916_)) as u8;
                                    if v_isSharedCheck_1944_ == 0 {
                                        v___x_1919_ = v___x_1916_;
                                        v_isShared_1920_ = v_isSharedCheck_1944_;
                                        state = 33;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1917_);
                                        lean_dec(v___x_1916_);
                                        v___x_1919_ = lean_box(0);
                                        v_isShared_1920_ = v_isSharedCheck_1944_;
                                        state = 33;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1894_);
                                    lean_dec_ref_known(v_code_1750_, 2);
                                    v_a_1945_ = lean_ctor_get(v___x_1916_, 0);
                                    v_isSharedCheck_1952_ = (!lean_is_exclusive(v___x_1916_)) as u8;
                                    if v_isSharedCheck_1952_ == 0 {
                                        v___x_1947_ = v___x_1916_;
                                        v_isShared_1948_ = v_isSharedCheck_1952_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1945_);
                                        lean_dec(v___x_1916_);
                                        v___x_1947_ = lean_box(0);
                                        v_isShared_1948_ = v_isSharedCheck_1952_;
                                        state = 39;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_1893_;
                        }
                    }
                    3 => {
                        v_fvarId_1953_ = lean_ctor_get(v_code_1750_, 0);
                        v_args_1954_ = lean_ctor_get(v_code_1750_, 1);
                        v___x_1955_ = lean_st_ref_take(v_a_1751_);
                        v___x_1956_ = lean_box(0);
                        lean_inc(v_fvarId_1953_);
                        v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_1955_, v_fvarId_1953_, v___x_1956_);
                        v___x_1958_ = lean_st_ref_set(v_a_1751_, v___x_1957_);
                        v___x_1959_ = lean_unsigned_to_nat(0);
                        v___x_1960_ = lean_array_get_size(v_args_1954_);
                        v___x_1961_ = lean_nat_dec_lt(v___x_1959_, v___x_1960_);
                        if v___x_1961_ == 0 {
                            v___x_1962_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1962_, 0, v_code_1750_);
                            return v___x_1962_;
                        } else {
                            v___x_1963_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
                            if v___x_1963_ == 0 {
                                if v___x_1961_ == 0 {
                                    v___x_1964_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1964_, 0, v_code_1750_);
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
                        v_cases_1971_ = lean_ctor_get(v_code_1750_, 0);
                        lean_inc_ref(v_cases_1971_);
                        v_typeName_1972_ = lean_ctor_get(v_cases_1971_, 0);
                        v_resultType_1973_ = lean_ctor_get(v_cases_1971_, 1);
                        v_discr_1974_ = lean_ctor_get(v_cases_1971_, 2);
                        v_alts_1975_ = lean_ctor_get(v_cases_1971_, 3);
                        v_isSharedCheck_2018_ = (!lean_is_exclusive(v_cases_1971_)) as u8;
                        if v_isSharedCheck_2018_ == 0 {
                            v___x_1977_ = v_cases_1971_;
                            v_isShared_1978_ = v_isSharedCheck_2018_;
                            state = 41;
                            continue;
                        } else {
                            lean_inc(v_alts_1975_);
                            lean_inc(v_discr_1974_);
                            lean_inc(v_resultType_1973_);
                            lean_inc(v_typeName_1972_);
                            lean_dec(v_cases_1971_);
                            v___x_1977_ = lean_box(0);
                            v_isShared_1978_ = v_isSharedCheck_2018_;
                            state = 41;
                            continue;
                        }
                    }
                    5 => {
                        v_fvarId_2019_ = lean_ctor_get(v_code_1750_, 0);
                        v___x_2020_ = lean_st_ref_take(v_a_1751_);
                        v___x_2021_ = lean_box(0);
                        lean_inc(v_fvarId_2019_);
                        v___x_2022_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2020_, v_fvarId_2019_, v___x_2021_);
                        v___x_2023_ = lean_st_ref_set(v_a_1751_, v___x_2022_);
                        v___x_2024_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2024_, 0, v_code_1750_);
                        return v___x_2024_;
                    }
                    6 => {
                        v___x_2025_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2025_, 0, v_code_1750_);
                        return v___x_2025_;
                    }
                    7 => {
                        v_fvarId_2026_ = lean_ctor_get(v_code_1750_, 0);
                        v_i_2027_ = lean_ctor_get(v_code_1750_, 1);
                        v_y_2028_ = lean_ctor_get(v_code_1750_, 2);
                        v_k_2029_ = lean_ctor_get(v_code_1750_, 3);
                        lean_inc_ref(v_k_2029_);
                        v___x_2030_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2029_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2030_) == 0 {
                            v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
                            v_isSharedCheck_2063_ = (!lean_is_exclusive(v___x_2030_)) as u8;
                            if v_isSharedCheck_2063_ == 0 {
                                v___x_2033_ = v___x_2030_;
                                v_isShared_2034_ = v_isSharedCheck_2063_;
                                state = 50;
                                continue;
                            } else {
                                lean_inc(v_a_2031_);
                                lean_dec(v___x_2030_);
                                v___x_2033_ = lean_box(0);
                                v_isShared_2034_ = v_isSharedCheck_2063_;
                                state = 50;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2030_;
                        }
                    }
                    8 => {
                        v_fvarId_2064_ = lean_ctor_get(v_code_1750_, 0);
                        v_i_2065_ = lean_ctor_get(v_code_1750_, 1);
                        v_y_2066_ = lean_ctor_get(v_code_1750_, 2);
                        v_k_2067_ = lean_ctor_get(v_code_1750_, 3);
                        lean_inc_ref(v_k_2067_);
                        v___x_2068_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2067_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2068_) == 0 {
                            v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
                            v_isSharedCheck_2102_ = (!lean_is_exclusive(v___x_2068_)) as u8;
                            if v_isSharedCheck_2102_ == 0 {
                                v___x_2071_ = v___x_2068_;
                                v_isShared_2072_ = v_isSharedCheck_2102_;
                                state = 56;
                                continue;
                            } else {
                                lean_inc(v_a_2069_);
                                lean_dec(v___x_2068_);
                                v___x_2071_ = lean_box(0);
                                v_isShared_2072_ = v_isSharedCheck_2102_;
                                state = 56;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2068_;
                        }
                    }
                    9 => {
                        v_fvarId_2103_ = lean_ctor_get(v_code_1750_, 0);
                        v_i_2104_ = lean_ctor_get(v_code_1750_, 1);
                        v_offset_2105_ = lean_ctor_get(v_code_1750_, 2);
                        v_y_2106_ = lean_ctor_get(v_code_1750_, 3);
                        v_ty_2107_ = lean_ctor_get(v_code_1750_, 4);
                        v_k_2108_ = lean_ctor_get(v_code_1750_, 5);
                        lean_inc_ref(v_k_2108_);
                        v___x_2109_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2108_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2109_) == 0 {
                            v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
                            v_isSharedCheck_2145_ = (!lean_is_exclusive(v___x_2109_)) as u8;
                            if v_isSharedCheck_2145_ == 0 {
                                v___x_2112_ = v___x_2109_;
                                v_isShared_2113_ = v_isSharedCheck_2145_;
                                state = 62;
                                continue;
                            } else {
                                lean_inc(v_a_2110_);
                                lean_dec(v___x_2109_);
                                v___x_2112_ = lean_box(0);
                                v_isShared_2113_ = v_isSharedCheck_2145_;
                                state = 62;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 6);
                            return v___x_2109_;
                        }
                    }
                    10 => {
                        v_fvarId_2146_ = lean_ctor_get(v_code_1750_, 0);
                        v_cidx_2147_ = lean_ctor_get(v_code_1750_, 1);
                        v_k_2148_ = lean_ctor_get(v_code_1750_, 2);
                        lean_inc_ref(v_k_2148_);
                        v___x_2149_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2148_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2149_) == 0 {
                            v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
                            v_isSharedCheck_2177_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                            if v_isSharedCheck_2177_ == 0 {
                                v___x_2152_ = v___x_2149_;
                                v_isShared_2153_ = v_isSharedCheck_2177_;
                                state = 68;
                                continue;
                            } else {
                                lean_inc(v_a_2150_);
                                lean_dec(v___x_2149_);
                                v___x_2152_ = lean_box(0);
                                v_isShared_2153_ = v_isSharedCheck_2177_;
                                state = 68;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 3);
                            return v___x_2149_;
                        }
                    }
                    11 => {
                        v_fvarId_2178_ = lean_ctor_get(v_code_1750_, 0);
                        v_n_2179_ = lean_ctor_get(v_code_1750_, 1);
                        v_check_2180_ = lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_2181_ = lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_k_2182_ = lean_ctor_get(v_code_1750_, 2);
                        lean_inc_ref(v_k_2182_);
                        v___x_2183_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2182_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2183_) == 0 {
                            v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
                            v_isSharedCheck_2211_ = (!lean_is_exclusive(v___x_2183_)) as u8;
                            if v_isSharedCheck_2211_ == 0 {
                                v___x_2186_ = v___x_2183_;
                                v_isShared_2187_ = v_isSharedCheck_2211_;
                                state = 73;
                                continue;
                            } else {
                                lean_inc(v_a_2184_);
                                lean_dec(v___x_2183_);
                                v___x_2186_ = lean_box(0);
                                v_isShared_2187_ = v_isSharedCheck_2211_;
                                state = 73;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 3);
                            return v___x_2183_;
                        }
                    }
                    12 => {
                        v_fvarId_2212_ = lean_ctor_get(v_code_1750_, 0);
                        v_n_2213_ = lean_ctor_get(v_code_1750_, 1);
                        v_check_2214_ = lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        );
                        v_persistent_2215_ = lean_ctor_get_uint8(
                            v_code_1750_,
                            (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        );
                        v_objs_x3f_2216_ = lean_ctor_get(v_code_1750_, 2);
                        v_k_2217_ = lean_ctor_get(v_code_1750_, 3);
                        lean_inc_ref(v_k_2217_);
                        v___x_2218_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2217_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2218_) == 0 {
                            v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
                            v_isSharedCheck_2247_ = (!lean_is_exclusive(v___x_2218_)) as u8;
                            if v_isSharedCheck_2247_ == 0 {
                                v___x_2221_ = v___x_2218_;
                                v_isShared_2222_ = v_isSharedCheck_2247_;
                                state = 78;
                                continue;
                            } else {
                                lean_inc(v_a_2219_);
                                lean_dec(v___x_2218_);
                                v___x_2221_ = lean_box(0);
                                v_isShared_2222_ = v_isSharedCheck_2247_;
                                state = 78;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 4);
                            return v___x_2218_;
                        }
                    }
                    _ => {
                        v_fvarId_2248_ = lean_ctor_get(v_code_1750_, 0);
                        v_k_2249_ = lean_ctor_get(v_code_1750_, 1);
                        lean_inc_ref(v_k_2249_);
                        v___x_2250_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_1749_, v_k_2249_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                        if lean_obj_tag(v___x_2250_) == 0 {
                            v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
                            v_isSharedCheck_2277_ = (!lean_is_exclusive(v___x_2250_)) as u8;
                            if v_isSharedCheck_2277_ == 0 {
                                v___x_2253_ = v___x_2250_;
                                v_isShared_2254_ = v_isSharedCheck_2277_;
                                state = 83;
                                continue;
                            } else {
                                lean_inc(v_a_2251_);
                                lean_dec(v___x_2250_);
                                v___x_2253_ = lean_box(0);
                                v_isShared_2254_ = v_isSharedCheck_2277_;
                                state = 83;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_1750_, 2);
                            return v___x_2250_;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_1758_) == 0 {
                    v_isSharedCheck_1765_ = (!lean_is_exclusive(v___y_1758_)) as u8;
                    if v_isSharedCheck_1765_ == 0 {
                        v_unused_1766_ = lean_ctor_get(v___y_1758_, 0);
                        lean_dec(v_unused_1766_);
                        v___x_1760_ = v___y_1758_;
                        v_isShared_1761_ = v_isSharedCheck_1765_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_1758_);
                        v___x_1760_ = lean_box(0);
                        v_isShared_1761_ = v_isSharedCheck_1765_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_code_1750_);
                    v_a_1767_ = lean_ctor_get(v___y_1758_, 0);
                    v_isSharedCheck_1774_ = (!lean_is_exclusive(v___y_1758_)) as u8;
                    if v_isSharedCheck_1774_ == 0 {
                        v___x_1769_ = v___y_1758_;
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1767_);
                        lean_dec(v___y_1758_);
                        v___x_1769_ = lean_box(0);
                        v_isShared_1770_ = v_isSharedCheck_1774_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1761_ == 0 {
                    lean_ctor_set(v___x_1760_, 0, v_code_1750_);
                    v___x_1763_ = v___x_1760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_code_1750_);
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
                    v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
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
                v_fvarId_1783_ = lean_ctor_get(v_decl_1775_, 0);
                v_value_1784_ = lean_ctor_get(v_decl_1775_, 3);
                v___x_1826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v___x_1782_, v_fvarId_1783_);
                lean_dec(v___x_1782_);
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
                lean_inc(v_value_1784_);
                v___x_1787_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_1749_, v___x_1786_, v_value_1784_);
                v___x_1788_ = lean_st_ref_set(v_a_1751_, v___x_1787_);
                v___x_1789_ = lean_ptr_addr(v_k_1776_);
                v___x_1790_ = lean_ptr_addr(v_a_1778_);
                v___x_1791_ = lean_usize_dec_eq(v___x_1789_, v___x_1790_);
                if v___x_1791_ == 0 {
                    lean_inc_ref(v_decl_1775_);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v_unused_1802_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_1802_);
                        v_unused_1803_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_1803_);
                        v___x_1793_ = v_code_1750_;
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_1793_ = lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1778_);
                    if v_isShared_1781_ == 0 {
                        lean_ctor_set(v___x_1780_, 0, v_code_1750_);
                        v___x_1805_ = v___x_1780_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_code_1750_);
                        v___x_1805_ = v_reuseFailAlloc_1806_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1794_ == 0 {
                    lean_ctor_set(v___x_1793_, 1, v_a_1778_);
                    v___x_1796_ = v___x_1793_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_decl_1775_);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1778_);
                    v___x_1796_ = v_reuseFailAlloc_1800_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1781_ == 0 {
                    lean_ctor_set(v___x_1780_, 0, v___x_1796_);
                    v___x_1798_ = v___x_1780_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
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
                    lean_inc_ref(v_decl_1775_);
                    lean_del_object(v___x_1780_);
                    lean_dec_ref_known(v_code_1750_, 2);
                    v___x_1809_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
                        v_pu_1749_,
                        v_decl_1775_,
                        v_a_1753_,
                    );
                    lean_dec_ref(v_decl_1775_);
                    if lean_obj_tag(v___x_1809_) == 0 {
                        v_isSharedCheck_1816_ = (!lean_is_exclusive(v___x_1809_)) as u8;
                        if v_isSharedCheck_1816_ == 0 {
                            v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
                            lean_dec(v_unused_1817_);
                            v___x_1811_ = v___x_1809_;
                            v_isShared_1812_ = v_isSharedCheck_1816_;
                            state = 13;
                            continue;
                        } else {
                            lean_dec(v___x_1809_);
                            v___x_1811_ = lean_box(0);
                            v_isShared_1812_ = v_isSharedCheck_1816_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1778_);
                        v_a_1818_ = lean_ctor_get(v___x_1809_, 0);
                        v_isSharedCheck_1825_ = (!lean_is_exclusive(v___x_1809_)) as u8;
                        if v_isSharedCheck_1825_ == 0 {
                            v___x_1820_ = v___x_1809_;
                            v_isShared_1821_ = v_isSharedCheck_1825_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1818_);
                            lean_dec(v___x_1809_);
                            v___x_1820_ = lean_box(0);
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
                    lean_ctor_set(v___x_1811_, 0, v_a_1778_);
                    v___x_1814_ = v___x_1811_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1778_);
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
                    v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
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
                    lean_ctor_set(v___x_1839_, 0, v_a_1832_);
                    v___x_1842_ = v___x_1839_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1832_);
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
                    v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
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
                    v_isSharedCheck_1870_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1870_ == 0 {
                        v_unused_1871_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_1871_);
                        v_unused_1872_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_1872_);
                        v___x_1862_ = v_code_1750_;
                        v_isShared_1863_ = v_isSharedCheck_1870_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_1862_ = lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1870_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1855_);
                    lean_dec(v_a_1832_);
                    if v_isShared_1858_ == 0 {
                        lean_ctor_set(v___x_1857_, 0, v_code_1750_);
                        v___x_1874_ = v___x_1857_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_code_1750_);
                        v___x_1874_ = v_reuseFailAlloc_1875_;
                        state = 26;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_1863_ == 0 {
                    lean_ctor_set(v___x_1862_, 1, v_a_1832_);
                    lean_ctor_set(v___x_1862_, 0, v_a_1855_);
                    v___x_1865_ = v___x_1862_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1855_);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_a_1832_);
                    v___x_1865_ = v_reuseFailAlloc_1869_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_1858_ == 0 {
                    lean_ctor_set(v___x_1857_, 0, v___x_1865_);
                    v___x_1867_ = v___x_1857_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
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
                    v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
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
                    lean_ctor_set(v___x_1901_, 0, v_a_1894_);
                    v___x_1904_ = v___x_1901_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1894_);
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
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
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
                    v_isSharedCheck_1932_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v_unused_1933_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_1933_);
                        v_unused_1934_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_1934_);
                        v___x_1924_ = v_code_1750_;
                        v_isShared_1925_ = v_isSharedCheck_1932_;
                        state = 35;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_1924_ = lean_box(0);
                        v_isShared_1925_ = v_isSharedCheck_1932_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1917_);
                    lean_dec(v_a_1894_);
                    if v_isShared_1920_ == 0 {
                        lean_ctor_set(v___x_1919_, 0, v_code_1750_);
                        v___x_1936_ = v___x_1919_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_code_1750_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_1925_ == 0 {
                    lean_ctor_set(v___x_1924_, 1, v_a_1894_);
                    lean_ctor_set(v___x_1924_, 0, v_a_1917_);
                    v___x_1927_ = v___x_1924_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1931_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1917_);
                    lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_a_1894_);
                    v___x_1927_ = v_reuseFailAlloc_1931_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1920_ == 0 {
                    lean_ctor_set(v___x_1919_, 0, v___x_1927_);
                    v___x_1929_ = v___x_1919_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
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
                    v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_1950_;
            }
            41 => {
                v___x_1979_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_1975_);
                v___x_1980_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_1749_, v___x_1979_, v_alts_1975_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
                if lean_obj_tag(v___x_1980_) == 0 {
                    v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
                    v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1980_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_1983_ = v___x_1980_;
                        v_isShared_1984_ = v_isSharedCheck_2009_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_1981_);
                        lean_dec(v___x_1980_);
                        v___x_1983_ = lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_2009_;
                        state = 42;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1977_);
                    lean_dec_ref(v_alts_1975_);
                    lean_dec(v_discr_1974_);
                    lean_dec_ref(v_resultType_1973_);
                    lean_dec(v_typeName_1972_);
                    lean_dec_ref_known(v_code_1750_, 1);
                    v_a_2010_ = lean_ctor_get(v___x_1980_, 0);
                    v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_1980_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_2012_ = v___x_1980_;
                        v_isShared_2013_ = v_isSharedCheck_2017_;
                        state = 48;
                        continue;
                    } else {
                        lean_inc(v_a_2010_);
                        lean_dec(v___x_1980_);
                        v___x_2012_ = lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2017_;
                        state = 48;
                        continue;
                    }
                }
            }
            42 => {
                v___x_1985_ = lean_st_ref_take(v_a_1751_);
                v___x_1986_ = lean_box(0);
                lean_inc(v_discr_1974_);
                v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_1985_, v_discr_1974_, v___x_1986_);
                v___x_1988_ = lean_st_ref_set(v_a_1751_, v___x_1987_);
                v___x_1989_ = lean_ptr_addr(v_alts_1975_);
                lean_dec_ref(v_alts_1975_);
                v___x_1990_ = lean_ptr_addr(v_a_1981_);
                v___x_1991_ = lean_usize_dec_eq(v___x_1989_, v___x_1990_);
                if v___x_1991_ == 0 {
                    v_isSharedCheck_2004_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v_unused_2005_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_2005_);
                        v___x_1993_ = v_code_1750_;
                        v_isShared_1994_ = v_isSharedCheck_2004_;
                        state = 43;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_1993_ = lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2004_;
                        state = 43;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1981_);
                    lean_del_object(v___x_1977_);
                    lean_dec(v_discr_1974_);
                    lean_dec_ref(v_resultType_1973_);
                    lean_dec(v_typeName_1972_);
                    if v_isShared_1984_ == 0 {
                        lean_ctor_set(v___x_1983_, 0, v_code_1750_);
                        v___x_2007_ = v___x_1983_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_code_1750_);
                        v___x_2007_ = v_reuseFailAlloc_2008_;
                        state = 47;
                        continue;
                    }
                }
            }
            43 => {
                if v_isShared_1978_ == 0 {
                    lean_ctor_set(v___x_1977_, 3, v_a_1981_);
                    v___x_1996_ = v___x_1977_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_typeName_1972_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_resultType_1973_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_discr_1974_);
                    lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_a_1981_);
                    v___x_1996_ = v_reuseFailAlloc_2003_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_1994_ == 0 {
                    lean_ctor_set(v___x_1993_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1993_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_2002_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1984_ == 0 {
                    lean_ctor_set(v___x_1983_, 0, v___x_1998_);
                    v___x_2000_ = v___x_1983_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
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
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
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
                lean_dec(v___x_2035_);
                if v___x_2036_ == 0 {
                    lean_dec_ref_known(v_code_1750_, 4);
                    if v_isShared_2034_ == 0 {
                        v___x_2038_ = v___x_2033_;
                        state = 51;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2031_);
                        v___x_2038_ = v_reuseFailAlloc_2039_;
                        state = 51;
                        continue;
                    }
                } else {
                    v___x_2040_ = lean_st_ref_take(v_a_1751_);
                    lean_inc(v_y_2028_);
                    v___x_2041_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_2040_, v_y_2028_);
                    v___x_2042_ = lean_st_ref_set(v_a_1751_, v___x_2041_);
                    v___x_2043_ = lean_ptr_addr(v_k_2029_);
                    v___x_2044_ = lean_ptr_addr(v_a_2031_);
                    v___x_2045_ = lean_usize_dec_eq(v___x_2043_, v___x_2044_);
                    if v___x_2045_ == 0 {
                        lean_inc(v_y_2028_);
                        lean_inc(v_i_2027_);
                        lean_inc(v_fvarId_2026_);
                        v_isSharedCheck_2055_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2055_ == 0 {
                            v_unused_2056_ = lean_ctor_get(v_code_1750_, 3);
                            lean_dec(v_unused_2056_);
                            v_unused_2057_ = lean_ctor_get(v_code_1750_, 2);
                            lean_dec(v_unused_2057_);
                            v_unused_2058_ = lean_ctor_get(v_code_1750_, 1);
                            lean_dec(v_unused_2058_);
                            v_unused_2059_ = lean_ctor_get(v_code_1750_, 0);
                            lean_dec(v_unused_2059_);
                            v___x_2047_ = v_code_1750_;
                            v_isShared_2048_ = v_isSharedCheck_2055_;
                            state = 52;
                            continue;
                        } else {
                            lean_dec(v_code_1750_);
                            v___x_2047_ = lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2055_;
                            state = 52;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2031_);
                        if v_isShared_2034_ == 0 {
                            lean_ctor_set(v___x_2033_, 0, v_code_1750_);
                            v___x_2061_ = v___x_2033_;
                            state = 55;
                            continue;
                        } else {
                            v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_code_1750_);
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
                    lean_ctor_set(v___x_2047_, 3, v_a_2031_);
                    v___x_2050_ = v___x_2047_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_fvarId_2026_);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_i_2027_);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_y_2028_);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_a_2031_);
                    v___x_2050_ = v_reuseFailAlloc_2054_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_2034_ == 0 {
                    lean_ctor_set(v___x_2033_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2033_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
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
                lean_dec(v___x_2073_);
                if v___x_2074_ == 0 {
                    lean_dec_ref_known(v_code_1750_, 4);
                    if v_isShared_2072_ == 0 {
                        v___x_2076_ = v___x_2071_;
                        state = 57;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2069_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 57;
                        continue;
                    }
                } else {
                    v___x_2078_ = lean_st_ref_take(v_a_1751_);
                    v___x_2079_ = lean_box(0);
                    lean_inc(v_y_2066_);
                    v___x_2080_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2078_, v_y_2066_, v___x_2079_);
                    v___x_2081_ = lean_st_ref_set(v_a_1751_, v___x_2080_);
                    v___x_2082_ = lean_ptr_addr(v_k_2067_);
                    v___x_2083_ = lean_ptr_addr(v_a_2069_);
                    v___x_2084_ = lean_usize_dec_eq(v___x_2082_, v___x_2083_);
                    if v___x_2084_ == 0 {
                        lean_inc(v_y_2066_);
                        lean_inc(v_i_2065_);
                        lean_inc(v_fvarId_2064_);
                        v_isSharedCheck_2094_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2094_ == 0 {
                            v_unused_2095_ = lean_ctor_get(v_code_1750_, 3);
                            lean_dec(v_unused_2095_);
                            v_unused_2096_ = lean_ctor_get(v_code_1750_, 2);
                            lean_dec(v_unused_2096_);
                            v_unused_2097_ = lean_ctor_get(v_code_1750_, 1);
                            lean_dec(v_unused_2097_);
                            v_unused_2098_ = lean_ctor_get(v_code_1750_, 0);
                            lean_dec(v_unused_2098_);
                            v___x_2086_ = v_code_1750_;
                            v_isShared_2087_ = v_isSharedCheck_2094_;
                            state = 58;
                            continue;
                        } else {
                            lean_dec(v_code_1750_);
                            v___x_2086_ = lean_box(0);
                            v_isShared_2087_ = v_isSharedCheck_2094_;
                            state = 58;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2069_);
                        if v_isShared_2072_ == 0 {
                            lean_ctor_set(v___x_2071_, 0, v_code_1750_);
                            v___x_2100_ = v___x_2071_;
                            state = 61;
                            continue;
                        } else {
                            v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_code_1750_);
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
                    lean_ctor_set(v___x_2086_, 3, v_a_2069_);
                    v___x_2089_ = v___x_2086_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_fvarId_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_i_2065_);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_y_2066_);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_a_2069_);
                    v___x_2089_ = v_reuseFailAlloc_2093_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_2072_ == 0 {
                    lean_ctor_set(v___x_2071_, 0, v___x_2089_);
                    v___x_2091_ = v___x_2071_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
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
                lean_dec(v___x_2114_);
                if v___x_2115_ == 0 {
                    lean_dec_ref_known(v_code_1750_, 6);
                    if v_isShared_2113_ == 0 {
                        v___x_2117_ = v___x_2112_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2110_);
                        v___x_2117_ = v_reuseFailAlloc_2118_;
                        state = 63;
                        continue;
                    }
                } else {
                    v___x_2119_ = lean_st_ref_take(v_a_1751_);
                    v___x_2120_ = lean_box(0);
                    lean_inc(v_y_2106_);
                    v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2119_, v_y_2106_, v___x_2120_);
                    v___x_2122_ = lean_st_ref_set(v_a_1751_, v___x_2121_);
                    v___x_2123_ = lean_ptr_addr(v_k_2108_);
                    v___x_2124_ = lean_ptr_addr(v_a_2110_);
                    v___x_2125_ = lean_usize_dec_eq(v___x_2123_, v___x_2124_);
                    if v___x_2125_ == 0 {
                        lean_inc_ref(v_ty_2107_);
                        lean_inc(v_y_2106_);
                        lean_inc(v_offset_2105_);
                        lean_inc(v_i_2104_);
                        lean_inc(v_fvarId_2103_);
                        v_isSharedCheck_2135_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v_unused_2136_ = lean_ctor_get(v_code_1750_, 5);
                            lean_dec(v_unused_2136_);
                            v_unused_2137_ = lean_ctor_get(v_code_1750_, 4);
                            lean_dec(v_unused_2137_);
                            v_unused_2138_ = lean_ctor_get(v_code_1750_, 3);
                            lean_dec(v_unused_2138_);
                            v_unused_2139_ = lean_ctor_get(v_code_1750_, 2);
                            lean_dec(v_unused_2139_);
                            v_unused_2140_ = lean_ctor_get(v_code_1750_, 1);
                            lean_dec(v_unused_2140_);
                            v_unused_2141_ = lean_ctor_get(v_code_1750_, 0);
                            lean_dec(v_unused_2141_);
                            v___x_2127_ = v_code_1750_;
                            v_isShared_2128_ = v_isSharedCheck_2135_;
                            state = 64;
                            continue;
                        } else {
                            lean_dec(v_code_1750_);
                            v___x_2127_ = lean_box(0);
                            v_isShared_2128_ = v_isSharedCheck_2135_;
                            state = 64;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2110_);
                        if v_isShared_2113_ == 0 {
                            lean_ctor_set(v___x_2112_, 0, v_code_1750_);
                            v___x_2143_ = v___x_2112_;
                            state = 67;
                            continue;
                        } else {
                            v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_code_1750_);
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
                    lean_ctor_set(v___x_2127_, 5, v_a_2110_);
                    v___x_2130_ = v___x_2127_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fvarId_2103_);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_i_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_offset_2105_);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_y_2106_);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_ty_2107_);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 5, v_a_2110_);
                    v___x_2130_ = v_reuseFailAlloc_2134_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                if v_isShared_2113_ == 0 {
                    lean_ctor_set(v___x_2112_, 0, v___x_2130_);
                    v___x_2132_ = v___x_2112_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
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
                v___x_2155_ = lean_box(0);
                lean_inc(v_fvarId_2146_);
                v___x_2156_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2154_, v_fvarId_2146_, v___x_2155_);
                v___x_2157_ = lean_st_ref_set(v_a_1751_, v___x_2156_);
                v___x_2158_ = lean_ptr_addr(v_k_2148_);
                v___x_2159_ = lean_ptr_addr(v_a_2150_);
                v___x_2160_ = lean_usize_dec_eq(v___x_2158_, v___x_2159_);
                if v___x_2160_ == 0 {
                    lean_inc(v_cidx_2147_);
                    lean_inc(v_fvarId_2146_);
                    v_isSharedCheck_2170_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2170_ == 0 {
                        v_unused_2171_ = lean_ctor_get(v_code_1750_, 2);
                        lean_dec(v_unused_2171_);
                        v_unused_2172_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_2172_);
                        v_unused_2173_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_2173_);
                        v___x_2162_ = v_code_1750_;
                        v_isShared_2163_ = v_isSharedCheck_2170_;
                        state = 69;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_2162_ = lean_box(0);
                        v_isShared_2163_ = v_isSharedCheck_2170_;
                        state = 69;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2150_);
                    if v_isShared_2153_ == 0 {
                        lean_ctor_set(v___x_2152_, 0, v_code_1750_);
                        v___x_2175_ = v___x_2152_;
                        state = 72;
                        continue;
                    } else {
                        v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_code_1750_);
                        v___x_2175_ = v_reuseFailAlloc_2176_;
                        state = 72;
                        continue;
                    }
                }
            }
            69 => {
                if v_isShared_2163_ == 0 {
                    lean_ctor_set(v___x_2162_, 2, v_a_2150_);
                    v___x_2165_ = v___x_2162_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_fvarId_2146_);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_cidx_2147_);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_a_2150_);
                    v___x_2165_ = v_reuseFailAlloc_2169_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2153_ == 0 {
                    lean_ctor_set(v___x_2152_, 0, v___x_2165_);
                    v___x_2167_ = v___x_2152_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
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
                v___x_2189_ = lean_box(0);
                lean_inc(v_fvarId_2178_);
                v___x_2190_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2188_, v_fvarId_2178_, v___x_2189_);
                v___x_2191_ = lean_st_ref_set(v_a_1751_, v___x_2190_);
                v___x_2192_ = lean_ptr_addr(v_k_2182_);
                v___x_2193_ = lean_ptr_addr(v_a_2184_);
                v___x_2194_ = lean_usize_dec_eq(v___x_2192_, v___x_2193_);
                if v___x_2194_ == 0 {
                    lean_inc(v_n_2179_);
                    lean_inc(v_fvarId_2178_);
                    v_isSharedCheck_2204_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2204_ == 0 {
                        v_unused_2205_ = lean_ctor_get(v_code_1750_, 2);
                        lean_dec(v_unused_2205_);
                        v_unused_2206_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_2206_);
                        v_unused_2207_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_2207_);
                        v___x_2196_ = v_code_1750_;
                        v_isShared_2197_ = v_isSharedCheck_2204_;
                        state = 74;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_2196_ = lean_box(0);
                        v_isShared_2197_ = v_isSharedCheck_2204_;
                        state = 74;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2184_);
                    if v_isShared_2187_ == 0 {
                        lean_ctor_set(v___x_2186_, 0, v_code_1750_);
                        v___x_2209_ = v___x_2186_;
                        state = 77;
                        continue;
                    } else {
                        v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_code_1750_);
                        v___x_2209_ = v_reuseFailAlloc_2210_;
                        state = 77;
                        continue;
                    }
                }
            }
            74 => {
                if v_isShared_2197_ == 0 {
                    lean_ctor_set(v___x_2196_, 2, v_a_2184_);
                    v___x_2199_ = v___x_2196_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_fvarId_2178_);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_n_2179_);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_a_2184_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2203_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_2180_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2203_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_2181_,
                    );
                    v___x_2199_ = v_reuseFailAlloc_2203_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_2187_ == 0 {
                    lean_ctor_set(v___x_2186_, 0, v___x_2199_);
                    v___x_2201_ = v___x_2186_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
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
                v___x_2224_ = lean_box(0);
                lean_inc(v_fvarId_2212_);
                v___x_2225_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2223_, v_fvarId_2212_, v___x_2224_);
                v___x_2226_ = lean_st_ref_set(v_a_1751_, v___x_2225_);
                v___x_2227_ = lean_ptr_addr(v_k_2217_);
                v___x_2228_ = lean_ptr_addr(v_a_2219_);
                v___x_2229_ = lean_usize_dec_eq(v___x_2227_, v___x_2228_);
                if v___x_2229_ == 0 {
                    lean_inc(v_objs_x3f_2216_);
                    lean_inc(v_n_2213_);
                    lean_inc(v_fvarId_2212_);
                    v_isSharedCheck_2239_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v_unused_2240_ = lean_ctor_get(v_code_1750_, 3);
                        lean_dec(v_unused_2240_);
                        v_unused_2241_ = lean_ctor_get(v_code_1750_, 2);
                        lean_dec(v_unused_2241_);
                        v_unused_2242_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_2242_);
                        v_unused_2243_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_2243_);
                        v___x_2231_ = v_code_1750_;
                        v_isShared_2232_ = v_isSharedCheck_2239_;
                        state = 79;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_2231_ = lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2239_;
                        state = 79;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2219_);
                    if v_isShared_2222_ == 0 {
                        lean_ctor_set(v___x_2221_, 0, v_code_1750_);
                        v___x_2245_ = v___x_2221_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_code_1750_);
                        v___x_2245_ = v_reuseFailAlloc_2246_;
                        state = 82;
                        continue;
                    }
                }
            }
            79 => {
                if v_isShared_2232_ == 0 {
                    lean_ctor_set(v___x_2231_, 3, v_a_2219_);
                    v___x_2234_ = v___x_2231_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_2238_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_fvarId_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_n_2213_);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_objs_x3f_2216_);
                    lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_a_2219_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_2214_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2238_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_2215_,
                    );
                    v___x_2234_ = v_reuseFailAlloc_2238_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_2222_ == 0 {
                    lean_ctor_set(v___x_2221_, 0, v___x_2234_);
                    v___x_2236_ = v___x_2221_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
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
                v___x_2256_ = lean_box(0);
                lean_inc(v_fvarId_2248_);
                v___x_2257_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg_spec__0___redArg(v___x_2255_, v_fvarId_2248_, v___x_2256_);
                v___x_2258_ = lean_st_ref_set(v_a_1751_, v___x_2257_);
                v___x_2259_ = lean_ptr_addr(v_k_2249_);
                v___x_2260_ = lean_ptr_addr(v_a_2251_);
                v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
                if v___x_2261_ == 0 {
                    lean_inc(v_fvarId_2248_);
                    v_isSharedCheck_2271_ = (!lean_is_exclusive(v_code_1750_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = lean_ctor_get(v_code_1750_, 1);
                        lean_dec(v_unused_2272_);
                        v_unused_2273_ = lean_ctor_get(v_code_1750_, 0);
                        lean_dec(v_unused_2273_);
                        v___x_2263_ = v_code_1750_;
                        v_isShared_2264_ = v_isSharedCheck_2271_;
                        state = 84;
                        continue;
                    } else {
                        lean_dec(v_code_1750_);
                        v___x_2263_ = lean_box(0);
                        v_isShared_2264_ = v_isSharedCheck_2271_;
                        state = 84;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2251_);
                    if v_isShared_2254_ == 0 {
                        lean_ctor_set(v___x_2253_, 0, v_code_1750_);
                        v___x_2275_ = v___x_2253_;
                        state = 87;
                        continue;
                    } else {
                        v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_code_1750_);
                        v___x_2275_ = v_reuseFailAlloc_2276_;
                        state = 87;
                        continue;
                    }
                }
            }
            84 => {
                if v_isShared_2264_ == 0 {
                    lean_ctor_set(v___x_2263_, 1, v_a_2251_);
                    v___x_2266_ = v___x_2263_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_fvarId_2248_);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2251_);
                    v___x_2266_ = v_reuseFailAlloc_2270_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_2254_ == 0 {
                    lean_ctor_set(v___x_2253_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2253_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
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
    mut v_funDecl_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_2286_ = lean_ctor_get(v_funDecl_2279_, 2);
                lean_inc_ref(v_params_2286_);
                v_type_2287_ = lean_ctor_get(v_funDecl_2279_, 3);
                lean_inc_ref(v_type_2287_);
                v_value_2288_ = lean_ctor_get(v_funDecl_2279_, 4);
                lean_inc_ref(v_value_2288_);
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
                if lean_obj_tag(v___x_2289_) == 0 {
                    v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
                    lean_inc(v_a_2290_);
                    lean_dec_ref_known(v___x_2289_, 1);
                    v___x_2291_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_2278_, v_funDecl_2279_, v_type_2287_, v_params_2286_, v_a_2290_, v_a_2282_);
                    return v___x_2291_;
                } else {
                    lean_dec_ref(v_type_2287_);
                    lean_dec_ref(v_params_2286_);
                    lean_dec_ref(v_funDecl_2279_);
                    v_a_2292_ = lean_ctor_get(v___x_2289_, 0);
                    v_isSharedCheck_2299_ = (!lean_is_exclusive(v___x_2289_)) as u8;
                    if v_isSharedCheck_2299_ == 0 {
                        v___x_2294_ = v___x_2289_;
                        v_isShared_2295_ = v_isSharedCheck_2299_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2292_);
                        lean_dec(v___x_2289_);
                        v___x_2294_ = lean_box(0);
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
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
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
    mut v_pu_2300_: *mut LeanObject,
    mut v_funDecl_2301_: *mut LeanObject,
    mut v_a_2302_: *mut LeanObject,
    mut v_a_2303_: *mut LeanObject,
    mut v_a_2304_: *mut LeanObject,
    mut v_a_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_a_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2308_: u8 = 0;
    let mut v_res_2309_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2308_ = (lean_unbox(v_pu_2300_) as u8);
    v_res_2309_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(
        v_pu_boxed_2308_,
        v_funDecl_2301_,
        v_a_2302_,
        v_a_2303_,
        v_a_2304_,
        v_a_2305_,
        v_a_2306_,
    );
    lean_dec(v_a_2306_);
    lean_dec_ref(v_a_2305_);
    lean_dec(v_a_2304_);
    lean_dec_ref(v_a_2303_);
    lean_dec(v_a_2302_);
    return v_res_2309_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(
    mut v_pu_2310_: *mut LeanObject,
    mut v_i_2311_: *mut LeanObject,
    mut v_as_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2319_: u8 = 0;
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2319_ = (lean_unbox(v_pu_2310_) as u8);
    v_res_2320_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_2319_, v_i_2311_, v_as_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    lean_dec(v___y_2317_);
    lean_dec_ref(v___y_2316_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    lean_dec(v___y_2313_);
    return v_res_2320_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(
    mut v_pu_2321_: *mut LeanObject,
    mut v_code_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
    mut v_a_2325_: *mut LeanObject,
    mut v_a_2326_: *mut LeanObject,
    mut v_a_2327_: *mut LeanObject,
    mut v_a_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2329_: u8 = 0;
    let mut v_res_2330_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2329_ = (lean_unbox(v_pu_2321_) as u8);
    v_res_2330_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(
        v_pu_boxed_2329_,
        v_code_2322_,
        v_a_2323_,
        v_a_2324_,
        v_a_2325_,
        v_a_2326_,
        v_a_2327_,
    );
    lean_dec(v_a_2327_);
    lean_dec_ref(v_a_2326_);
    lean_dec(v_a_2325_);
    lean_dec_ref(v_a_2324_);
    lean_dec(v_a_2323_);
    return v_res_2330_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(
    mut v_00_u03b2_2331_: *mut LeanObject,
    mut v_m_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
) -> u8 {
    let mut v___x_2334_: u8 = 0;
    v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_m_2332_, v_a_2333_);
    return v___x_2334_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(
    mut v_00_u03b2_2335_: *mut LeanObject,
    mut v_m_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_2335_, v_m_2336_, v_a_2337_);
    lean_dec(v_a_2337_);
    lean_dec_ref(v_m_2336_);
    v_r_2339_ = lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(
    mut v_pu_2340_: u8,
    mut v_as_2341_: *mut LeanObject,
    mut v_i_2342_: usize,
    mut v_stop_2343_: usize,
    mut v_b_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_2341_, v_i_2342_, v_stop_2343_, v_b_2344_, v___y_2345_);
    return v___x_2351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(
    mut v_pu_2352_: *mut LeanObject,
    mut v_as_2353_: *mut LeanObject,
    mut v_i_2354_: *mut LeanObject,
    mut v_stop_2355_: *mut LeanObject,
    mut v_b_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2363_: u8 = 0;
    let mut v_i_boxed_2364_: usize = 0;
    let mut v_stop_boxed_2365_: usize = 0;
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2363_ = (lean_unbox(v_pu_2352_) as u8);
    v_i_boxed_2364_ = lean_unbox_usize(v_i_2354_);
    lean_dec(v_i_2354_);
    v_stop_boxed_2365_ = lean_unbox_usize(v_stop_2355_);
    lean_dec(v_stop_2355_);
    v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_2363_, v_as_2353_, v_i_boxed_2364_, v_stop_boxed_2365_, v_b_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
    lean_dec(v___y_2361_);
    lean_dec_ref(v___y_2360_);
    lean_dec(v___y_2359_);
    lean_dec_ref(v___y_2358_);
    lean_dec(v___y_2357_);
    lean_dec_ref(v_as_2353_);
    return v_res_2366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(
    mut v_f_2367_: *mut LeanObject,
    mut v_v_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_a_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2397_: u8 = 0;
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2368_) == 0 {
                    v_code_2374_ = lean_ctor_get(v_v_2368_, 0);
                    v_isSharedCheck_2398_ = (!lean_is_exclusive(v_v_2368_)) as u8;
                    if v_isSharedCheck_2398_ == 0 {
                        v___x_2376_ = v_v_2368_;
                        v_isShared_2377_ = v_isSharedCheck_2398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_2374_);
                        lean_dec(v_v_2368_);
                        v___x_2376_ = lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2398_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_2367_);
                    v___x_2399_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2399_, 0, v_v_2368_);
                    return v___x_2399_;
                }
            }
            1 => {
                lean_inc(v___y_2372_);
                lean_inc_ref(v___y_2371_);
                lean_inc(v___y_2370_);
                lean_inc_ref(v___y_2369_);
                v___x_2378_ = lean_apply_6(
                    v_f_2367_,
                    v_code_2374_,
                    v___y_2369_,
                    v___y_2370_,
                    v___y_2371_,
                    v___y_2372_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2378_) == 0 {
                    v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
                    v_isSharedCheck_2389_ = (!lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2389_ == 0 {
                        v___x_2381_ = v___x_2378_;
                        v_isShared_2382_ = v_isSharedCheck_2389_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2379_);
                        lean_dec(v___x_2378_);
                        v___x_2381_ = lean_box(0);
                        v_isShared_2382_ = v_isSharedCheck_2389_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2376_);
                    v_a_2390_ = lean_ctor_get(v___x_2378_, 0);
                    v_isSharedCheck_2397_ = (!lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2397_ == 0 {
                        v___x_2392_ = v___x_2378_;
                        v_isShared_2393_ = v_isSharedCheck_2397_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2390_);
                        lean_dec(v___x_2378_);
                        v___x_2392_ = lean_box(0);
                        v_isShared_2393_ = v_isSharedCheck_2397_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2377_ == 0 {
                    lean_ctor_set(v___x_2376_, 0, v_a_2379_);
                    v___x_2384_ = v___x_2376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2382_ == 0 {
                    lean_ctor_set(v___x_2381_, 0, v___x_2384_);
                    v___x_2386_ = v___x_2381_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
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
                    v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
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
    mut v_f_2400_: *mut LeanObject,
    mut v_v_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2407_: *mut LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_2400_, v_v_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    lean_dec(v___y_2405_);
    lean_dec_ref(v___y_2404_);
    lean_dec(v___y_2403_);
    lean_dec_ref(v___y_2402_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(
    mut v_pu_2408_: u8,
    mut v_f_2409_: *mut LeanObject,
    mut v_v_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_2409_, v_v_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
    return v___x_2416_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(
    mut v_pu_2417_: *mut LeanObject,
    mut v_f_2418_: *mut LeanObject,
    mut v_v_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2425_: u8 = 0;
    let mut v_res_2426_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2425_ = (lean_unbox(v_pu_2417_) as u8);
    v_res_2426_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_2425_, v_f_2418_, v_v_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
    lean_dec(v___y_2423_);
    lean_dec_ref(v___y_2422_);
    lean_dec(v___y_2421_);
    lean_dec_ref(v___y_2420_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(
    mut v___x_2427_: *mut LeanObject,
    mut v_pu_2428_: u8,
    mut v_code_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2436_) == 0 {
                    v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
                    v_isSharedCheck_2445_ = (!lean_is_exclusive(v___x_2436_)) as u8;
                    if v_isSharedCheck_2445_ == 0 {
                        v___x_2439_ = v___x_2436_;
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2437_);
                        lean_dec(v___x_2436_);
                        v___x_2439_ = lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2445_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2435_);
                    return v___x_2436_;
                }
            }
            1 => {
                v___x_2441_ = lean_st_ref_get(v___x_2435_);
                lean_dec(v___x_2435_);
                lean_dec(v___x_2441_);
                if v_isShared_2440_ == 0 {
                    v___x_2443_ = v___x_2439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2437_);
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
    mut v___x_2446_: *mut LeanObject,
    mut v_pu_2447_: *mut LeanObject,
    mut v_code_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
    mut v___y_2451_: *mut LeanObject,
    mut v___y_2452_: *mut LeanObject,
    mut v___y_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2454_: u8 = 0;
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2454_ = (lean_unbox(v_pu_2447_) as u8);
    v_res_2455_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(
        v___x_2446_,
        v_pu_boxed_2454_,
        v_code_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
        v___y_2452_,
    );
    lean_dec(v___y_2452_);
    lean_dec_ref(v___y_2451_);
    lean_dec(v___y_2450_);
    lean_dec_ref(v___y_2449_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_elimDeadVars(
    mut v_pu_2456_: u8,
    mut v_decl_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_2465_: u8 = 0;
    let mut v_inlineAttr_x3f_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_a_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2463_ = lean_ctor_get(v_decl_2457_, 0);
                v_value_2464_ = lean_ctor_get(v_decl_2457_, 1);
                v_recursive_2465_ = lean_ctor_get_uint8(
                    v_decl_2457_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_2466_ = lean_ctor_get(v_decl_2457_, 2);
                v_isSharedCheck_2493_ = (!lean_is_exclusive(v_decl_2457_)) as u8;
                if v_isSharedCheck_2493_ == 0 {
                    v___x_2468_ = v_decl_2457_;
                    v_isShared_2469_ = v_isSharedCheck_2493_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_2466_);
                    lean_inc(v_value_2464_);
                    lean_inc(v_toSignature_2463_);
                    lean_dec(v_decl_2457_);
                    v___x_2468_ = lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2493_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_2471_ = lean_box((v_pu_2456_) as usize);
                v___f_2472_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    2,
                );
                lean_closure_set(v___f_2472_, 0, v___x_2470_);
                lean_closure_set(v___f_2472_, 1, v___x_2471_);
                v___x_2473_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_2472_, v_value_2464_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                if lean_obj_tag(v___x_2473_) == 0 {
                    v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2484_ == 0 {
                        v___x_2476_ = v___x_2473_;
                        v_isShared_2477_ = v_isSharedCheck_2484_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2474_);
                        lean_dec(v___x_2473_);
                        v___x_2476_ = lean_box(0);
                        v_isShared_2477_ = v_isSharedCheck_2484_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2468_);
                    lean_dec(v_inlineAttr_x3f_2466_);
                    lean_dec_ref(v_toSignature_2463_);
                    v_a_2485_ = lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2492_ = (!lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2492_ == 0 {
                        v___x_2487_ = v___x_2473_;
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2485_);
                        lean_dec(v___x_2473_);
                        v___x_2487_ = lean_box(0);
                        v_isShared_2488_ = v_isSharedCheck_2492_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2469_ == 0 {
                    lean_ctor_set(v___x_2468_, 1, v_a_2474_);
                    v___x_2479_ = v___x_2468_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_toSignature_2463_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_a_2474_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_inlineAttr_x3f_2466_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2483_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_2465_,
                    );
                    v___x_2479_ = v_reuseFailAlloc_2483_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2477_ == 0 {
                    lean_ctor_set(v___x_2476_, 0, v___x_2479_);
                    v___x_2481_ = v___x_2476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
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
                    v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
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
    mut v_pu_2494_: *mut LeanObject,
    mut v_decl_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2501_: u8 = 0;
    let mut v_res_2502_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2501_ = (lean_unbox(v_pu_2494_) as u8);
    v_res_2502_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(
        v_pu_boxed_2501_,
        v_decl_2495_,
        v_a_2496_,
        v_a_2497_,
        v_a_2498_,
        v_a_2499_,
    );
    lean_dec(v_a_2499_);
    lean_dec_ref(v_a_2498_);
    lean_dec(v_a_2497_);
    lean_dec_ref(v_a_2496_);
    return v_res_2502_;
}
pub unsafe fn l_Lean_Compiler_LCNF_elimDeadVars(
    mut v_phase_2506_: u8,
    mut v_occurrence_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Compiler_LCNF_elimDeadVars___closed__1;
    v___x_2509_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_2506_);
    v___x_2510_ = lean_box((v___x_2509_) as usize);
    v___x_2511_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_2511_, 0, v___x_2510_);
    v___x_2512_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_2508_,
        v_phase_2506_,
        v___x_2511_,
        v_occurrence_2507_,
    );
    return v___x_2512_;
}
pub unsafe fn l_Lean_Compiler_LCNF_elimDeadVars___boxed(
    mut v_phase_2513_: *mut LeanObject,
    mut v_occurrence_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_2515_: u8 = 0;
    let mut v_res_2516_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_2515_ = (lean_unbox(v_phase_2513_) as u8);
    v_res_2516_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_2515_, v_occurrence_2514_);
    return v_res_2516_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: u8 = 0;
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_;
    v___x_2588_ = 1;
    v___x_2589_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_;
    v___x_2590_ = l_Lean_registerTraceClass(v___x_2587_, v___x_2588_, v___x_2589_);
    return v___x_2590_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(
    mut v_a_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2592_: *mut LeanObject = core::ptr::null_mut();
    v_res_2592_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
    return v_res_2592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ElimDead(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ElimDead(builtin);
}
