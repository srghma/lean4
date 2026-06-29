// Lean compiler output
// Module: Lean.Compiler.LCNF.FVarUtil
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_ptr_addr, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::Option::{
    l_OptionT_bind, l_OptionT_instMonad___redArg___lam__1, l_OptionT_instMonad___redArg___lam__3,
    l_OptionT_instMonad___redArg___lam__6, l_OptionT_instMonad___redArg___lam__9,
    l_OptionT_instMonad___redArg___lam__11, l_OptionT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::BasicAux::l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go;
use crate::r#gen::Init::Prelude::{l_instInhabitedOfMonad___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp,
    l_Lean_Compiler_LCNF_Alt_forCodeM___redArg, l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_hasFVar, l_Lean_Expr_lam___override, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
};
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69,
        120, 112, 114, 46, 109, 97, 112, 70, 86, 97, 114, 77, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70,
        86, 97, 114, 85, 116, 105, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69,
        120, 112, 114, 46, 102, 111, 114, 70, 86, 97, 114, 77, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instTraverseFVarExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(
    mut v_toApplicative_3379_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3380_: *mut crate::leanh::LeanObject,
    mut v_e_3381_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    v_toPure_3383_ = crate::leanh::lean_ctor_get(v_toApplicative_3379_, 1);
    crate::leanh::lean_inc(v_toPure_3383_);
    crate::leanh::lean_dec_ref(v_toApplicative_3379_);
    v___x_3384_ = l_Lean_instBEqFVarId_beq(v_fvarId_3380_, v_____do__lift_3382_);
    if v___x_3384_ == 0 {
        let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_3381_);
        v___x_3385_ = l_Lean_Expr_fvar___override(v_____do__lift_3382_);
        v___x_3386_ =
            crate::leanh::lean_apply_2(v_toPure_3383_, crate::leanh::lean_box(0), v___x_3385_);
        return v___x_3386_;
    } else {
        let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____do__lift_3382_);
        v___x_3387_ =
            crate::leanh::lean_apply_2(v_toPure_3383_, crate::leanh::lean_box(0), v_e_3381_);
        return v___x_3387_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed(
    mut v_toApplicative_3388_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3389_: *mut crate::leanh::LeanObject,
    mut v_e_3390_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3392_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0(
        v_toApplicative_3388_,
        v_fvarId_3389_,
        v_e_3390_,
        v_____do__lift_3391_,
    );
    crate::leanh::lean_dec(v_fvarId_3389_);
    return v_res_3392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(
    mut v_toApplicative_3393_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3394_: *mut crate::leanh::LeanObject,
    mut v_e_3395_: *mut crate::leanh::LeanObject,
    mut v_fn_3396_: *mut crate::leanh::LeanObject,
    mut v_arg_3397_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3401_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: usize = 0;
    let mut v___x_3409_: usize = 0;
    let mut v___x_3410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3399_ = crate::leanh::lean_ctor_get(v_toApplicative_3393_, 1);
                crate::leanh::lean_inc(v_toPure_3399_);
                crate::leanh::lean_dec_ref(v_toApplicative_3393_);
                v___x_3405_ = lean_ptr_addr(v_fn_3396_);
                v___x_3406_ = lean_ptr_addr(v_____do__lift_3394_);
                v___x_3407_ = lean_usize_dec_eq(v___x_3405_, v___x_3406_);
                if v___x_3407_ == 0 {
                    v___y_3401_ = v___x_3407_;
                    state = 1;
                    continue;
                } else {
                    v___x_3408_ = lean_ptr_addr(v_arg_3397_);
                    v___x_3409_ = lean_ptr_addr(v_____do__lift_3398_);
                    v___x_3410_ = lean_usize_dec_eq(v___x_3408_, v___x_3409_);
                    v___y_3401_ = v___x_3410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3401_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3395_);
                    v___x_3402_ =
                        l_Lean_Expr_app___override(v_____do__lift_3394_, v_____do__lift_3398_);
                    v___x_3403_ = crate::leanh::lean_apply_2(
                        v_toPure_3399_,
                        crate::leanh::lean_box(0),
                        v___x_3402_,
                    );
                    return v___x_3403_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_3398_);
                    crate::leanh::lean_dec_ref(v_____do__lift_3394_);
                    v___x_3404_ = crate::leanh::lean_apply_2(
                        v_toPure_3399_,
                        crate::leanh::lean_box(0),
                        v_e_3395_,
                    );
                    return v___x_3404_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed(
    mut v_toApplicative_3411_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3412_: *mut crate::leanh::LeanObject,
    mut v_e_3413_: *mut crate::leanh::LeanObject,
    mut v_fn_3414_: *mut crate::leanh::LeanObject,
    mut v_arg_3415_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3417_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1(
        v_toApplicative_3411_,
        v_____do__lift_3412_,
        v_e_3413_,
        v_fn_3414_,
        v_arg_3415_,
        v_____do__lift_3416_,
    );
    crate::leanh::lean_dec_ref(v_arg_3415_);
    crate::leanh::lean_dec_ref(v_fn_3414_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(
    mut v_toApplicative_3418_: *mut crate::leanh::LeanObject,
    mut v_binderName_3419_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3420_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3421_: u8,
    mut v_e_3422_: *mut crate::leanh::LeanObject,
    mut v_binderType_3423_: *mut crate::leanh::LeanObject,
    mut v_body_3424_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: usize = 0;
    let mut v___x_3440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3426_ = crate::leanh::lean_ctor_get(v_toApplicative_3418_, 1);
                crate::leanh::lean_inc(v_toPure_3426_);
                crate::leanh::lean_dec_ref(v_toApplicative_3418_);
                v___x_3435_ = lean_ptr_addr(v_binderType_3423_);
                v___x_3436_ = lean_ptr_addr(v_____do__lift_3420_);
                v___x_3437_ = lean_usize_dec_eq(v___x_3435_, v___x_3436_);
                if v___x_3437_ == 0 {
                    v___y_3428_ = v___x_3437_;
                    state = 1;
                    continue;
                } else {
                    v___x_3438_ = lean_ptr_addr(v_body_3424_);
                    v___x_3439_ = lean_ptr_addr(v_____do__lift_3425_);
                    v___x_3440_ = lean_usize_dec_eq(v___x_3438_, v___x_3439_);
                    v___y_3428_ = v___x_3440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3428_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3422_);
                    v___x_3429_ = l_Lean_Expr_lam___override(
                        v_binderName_3419_,
                        v_____do__lift_3420_,
                        v_____do__lift_3425_,
                        v_binderInfo_3421_,
                    );
                    v___x_3430_ = crate::leanh::lean_apply_2(
                        v_toPure_3426_,
                        crate::leanh::lean_box(0),
                        v___x_3429_,
                    );
                    return v___x_3430_;
                } else {
                    v___x_3431_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3421_, v_binderInfo_3421_);
                    if v___x_3431_ == 0 {
                        crate::leanh::lean_dec_ref(v_e_3422_);
                        v___x_3432_ = l_Lean_Expr_lam___override(
                            v_binderName_3419_,
                            v_____do__lift_3420_,
                            v_____do__lift_3425_,
                            v_binderInfo_3421_,
                        );
                        v___x_3433_ = crate::leanh::lean_apply_2(
                            v_toPure_3426_,
                            crate::leanh::lean_box(0),
                            v___x_3432_,
                        );
                        return v___x_3433_;
                    } else {
                        crate::leanh::lean_dec_ref(v_____do__lift_3425_);
                        crate::leanh::lean_dec_ref(v_____do__lift_3420_);
                        crate::leanh::lean_dec(v_binderName_3419_);
                        v___x_3434_ = crate::leanh::lean_apply_2(
                            v_toPure_3426_,
                            crate::leanh::lean_box(0),
                            v_e_3422_,
                        );
                        return v___x_3434_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed(
    mut v_toApplicative_3441_: *mut crate::leanh::LeanObject,
    mut v_binderName_3442_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3443_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3444_: *mut crate::leanh::LeanObject,
    mut v_e_3445_: *mut crate::leanh::LeanObject,
    mut v_binderType_3446_: *mut crate::leanh::LeanObject,
    mut v_body_3447_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_1027__boxed_3449_: u8 = 0;
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1027__boxed_3449_ = (crate::leanh::lean_unbox(v_binderInfo_3444_) as u8);
    v_res_3450_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3(
        v_toApplicative_3441_,
        v_binderName_3442_,
        v_____do__lift_3443_,
        v_binderInfo_1027__boxed_3449_,
        v_e_3445_,
        v_binderType_3446_,
        v_body_3447_,
        v_____do__lift_3448_,
    );
    crate::leanh::lean_dec_ref(v_body_3447_);
    crate::leanh::lean_dec_ref(v_binderType_3446_);
    return v_res_3450_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(
    mut v_toApplicative_3451_: *mut crate::leanh::LeanObject,
    mut v_binderName_3452_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3453_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3454_: u8,
    mut v_e_3455_: *mut crate::leanh::LeanObject,
    mut v_binderType_3456_: *mut crate::leanh::LeanObject,
    mut v_body_3457_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: usize = 0;
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: usize = 0;
    let mut v___x_3472_: usize = 0;
    let mut v___x_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toPure_3459_ = crate::leanh::lean_ctor_get(v_toApplicative_3451_, 1);
                crate::leanh::lean_inc(v_toPure_3459_);
                crate::leanh::lean_dec_ref(v_toApplicative_3451_);
                v___x_3468_ = lean_ptr_addr(v_binderType_3456_);
                v___x_3469_ = lean_ptr_addr(v_____do__lift_3453_);
                v___x_3470_ = lean_usize_dec_eq(v___x_3468_, v___x_3469_);
                if v___x_3470_ == 0 {
                    v___y_3461_ = v___x_3470_;
                    state = 1;
                    continue;
                } else {
                    v___x_3471_ = lean_ptr_addr(v_body_3457_);
                    v___x_3472_ = lean_ptr_addr(v_____do__lift_3458_);
                    v___x_3473_ = lean_usize_dec_eq(v___x_3471_, v___x_3472_);
                    v___y_3461_ = v___x_3473_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3461_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3455_);
                    v___x_3462_ = l_Lean_Expr_forallE___override(
                        v_binderName_3452_,
                        v_____do__lift_3453_,
                        v_____do__lift_3458_,
                        v_binderInfo_3454_,
                    );
                    v___x_3463_ = crate::leanh::lean_apply_2(
                        v_toPure_3459_,
                        crate::leanh::lean_box(0),
                        v___x_3462_,
                    );
                    return v___x_3463_;
                } else {
                    v___x_3464_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3454_, v_binderInfo_3454_);
                    if v___x_3464_ == 0 {
                        crate::leanh::lean_dec_ref(v_e_3455_);
                        v___x_3465_ = l_Lean_Expr_forallE___override(
                            v_binderName_3452_,
                            v_____do__lift_3453_,
                            v_____do__lift_3458_,
                            v_binderInfo_3454_,
                        );
                        v___x_3466_ = crate::leanh::lean_apply_2(
                            v_toPure_3459_,
                            crate::leanh::lean_box(0),
                            v___x_3465_,
                        );
                        return v___x_3466_;
                    } else {
                        crate::leanh::lean_dec_ref(v_____do__lift_3458_);
                        crate::leanh::lean_dec_ref(v_____do__lift_3453_);
                        crate::leanh::lean_dec(v_binderName_3452_);
                        v___x_3467_ = crate::leanh::lean_apply_2(
                            v_toPure_3459_,
                            crate::leanh::lean_box(0),
                            v_e_3455_,
                        );
                        return v___x_3467_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed(
    mut v_toApplicative_3474_: *mut crate::leanh::LeanObject,
    mut v_binderName_3475_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3476_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3477_: *mut crate::leanh::LeanObject,
    mut v_e_3478_: *mut crate::leanh::LeanObject,
    mut v_binderType_3479_: *mut crate::leanh::LeanObject,
    mut v_body_3480_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_1073__boxed_3482_: u8 = 0;
    let mut v_res_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1073__boxed_3482_ = (crate::leanh::lean_unbox(v_binderInfo_3477_) as u8);
    v_res_3483_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5(
        v_toApplicative_3474_,
        v_binderName_3475_,
        v_____do__lift_3476_,
        v_binderInfo_1073__boxed_3482_,
        v_e_3478_,
        v_binderType_3479_,
        v_body_3480_,
        v_____do__lift_3481_,
    );
    crate::leanh::lean_dec_ref(v_body_3480_);
    crate::leanh::lean_dec_ref(v_binderType_3479_);
    return v_res_3483_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2;
    v___x_3488_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_3489_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_3490_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__1;
    v___x_3491_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0;
    v___x_3492_ = l_mkPanicMessageWithDecl(
        v___x_3491_,
        v___x_3490_,
        v___x_3489_,
        v___x_3488_,
        v___x_3487_,
    );
    return v___x_3492_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(
    mut v_toApplicative_3493_: *mut crate::leanh::LeanObject,
    mut v_binderName_3494_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3495_: u8,
    mut v_e_3496_: *mut crate::leanh::LeanObject,
    mut v_binderType_3497_: *mut crate::leanh::LeanObject,
    mut v_body_3498_: *mut crate::leanh::LeanObject,
    mut v_inst_3499_: *mut crate::leanh::LeanObject,
    mut v_f_3500_: *mut crate::leanh::LeanObject,
    mut v_toBind_3501_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3503_ = crate::leanh::lean_box((v_binderInfo_3495_) as usize);
    crate::leanh::lean_inc_ref(v_body_3498_);
    v___f_3504_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3504_, 0, v_toApplicative_3493_);
    crate::leanh::lean_closure_set(v___f_3504_, 1, v_binderName_3494_);
    crate::leanh::lean_closure_set(v___f_3504_, 2, v_____do__lift_3502_);
    crate::leanh::lean_closure_set(v___f_3504_, 3, v___x_3503_);
    crate::leanh::lean_closure_set(v___f_3504_, 4, v_e_3496_);
    crate::leanh::lean_closure_set(v___f_3504_, 5, v_binderType_3497_);
    crate::leanh::lean_closure_set(v___f_3504_, 6, v_body_3498_);
    v___x_3505_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3499_, v_f_3500_, v_body_3498_);
    v___x_3506_ = crate::leanh::lean_apply_4(
        v_toBind_3501_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3505_,
        v___f_3504_,
    );
    return v___x_3506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed(
    mut v_toApplicative_3507_: *mut crate::leanh::LeanObject,
    mut v_binderName_3508_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3509_: *mut crate::leanh::LeanObject,
    mut v_e_3510_: *mut crate::leanh::LeanObject,
    mut v_binderType_3511_: *mut crate::leanh::LeanObject,
    mut v_body_3512_: *mut crate::leanh::LeanObject,
    mut v_inst_3513_: *mut crate::leanh::LeanObject,
    mut v_f_3514_: *mut crate::leanh::LeanObject,
    mut v_toBind_3515_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_1152__boxed_3517_: u8 = 0;
    let mut v_res_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1152__boxed_3517_ = (crate::leanh::lean_unbox(v_binderInfo_3509_) as u8);
    v_res_3518_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4(
        v_toApplicative_3507_,
        v_binderName_3508_,
        v_binderInfo_1152__boxed_3517_,
        v_e_3510_,
        v_binderType_3511_,
        v_body_3512_,
        v_inst_3513_,
        v_f_3514_,
        v_toBind_3515_,
        v_____do__lift_3516_,
    );
    return v_res_3518_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(
    mut v_toApplicative_3519_: *mut crate::leanh::LeanObject,
    mut v_binderName_3520_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3521_: u8,
    mut v_e_3522_: *mut crate::leanh::LeanObject,
    mut v_binderType_3523_: *mut crate::leanh::LeanObject,
    mut v_body_3524_: *mut crate::leanh::LeanObject,
    mut v_inst_3525_: *mut crate::leanh::LeanObject,
    mut v_f_3526_: *mut crate::leanh::LeanObject,
    mut v_toBind_3527_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = crate::leanh::lean_box((v_binderInfo_3521_) as usize);
    crate::leanh::lean_inc_ref(v_body_3524_);
    v___f_3530_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3530_, 0, v_toApplicative_3519_);
    crate::leanh::lean_closure_set(v___f_3530_, 1, v_binderName_3520_);
    crate::leanh::lean_closure_set(v___f_3530_, 2, v_____do__lift_3528_);
    crate::leanh::lean_closure_set(v___f_3530_, 3, v___x_3529_);
    crate::leanh::lean_closure_set(v___f_3530_, 4, v_e_3522_);
    crate::leanh::lean_closure_set(v___f_3530_, 5, v_binderType_3523_);
    crate::leanh::lean_closure_set(v___f_3530_, 6, v_body_3524_);
    v___x_3531_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3525_, v_f_3526_, v_body_3524_);
    v___x_3532_ = crate::leanh::lean_apply_4(
        v_toBind_3527_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3531_,
        v___f_3530_,
    );
    return v___x_3532_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed(
    mut v_toApplicative_3533_: *mut crate::leanh::LeanObject,
    mut v_binderName_3534_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3535_: *mut crate::leanh::LeanObject,
    mut v_e_3536_: *mut crate::leanh::LeanObject,
    mut v_binderType_3537_: *mut crate::leanh::LeanObject,
    mut v_body_3538_: *mut crate::leanh::LeanObject,
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_f_3540_: *mut crate::leanh::LeanObject,
    mut v_toBind_3541_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_1161__boxed_3543_: u8 = 0;
    let mut v_res_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_1161__boxed_3543_ = (crate::leanh::lean_unbox(v_binderInfo_3535_) as u8);
    v_res_3544_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6(
        v_toApplicative_3533_,
        v_binderName_3534_,
        v_binderInfo_1161__boxed_3543_,
        v_e_3536_,
        v_binderType_3537_,
        v_body_3538_,
        v_inst_3539_,
        v_f_3540_,
        v_toBind_3541_,
        v_____do__lift_3542_,
    );
    return v_res_3544_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
    mut v_inst_3545_: *mut crate::leanh::LeanObject,
    mut v_f_3546_: *mut crate::leanh::LeanObject,
    mut v_e_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3548_: u8 = 0;
    v___x_3548_ = l_Lean_Expr_hasFVar(v_e_3547_);
    if v___x_3548_ == 0 {
        let mut v_toApplicative_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_3546_);
        v_toApplicative_3549_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3549_);
        crate::leanh::lean_dec_ref(v_inst_3545_);
        v_toPure_3550_ = crate::leanh::lean_ctor_get(v_toApplicative_3549_, 1);
        crate::leanh::lean_inc(v_toPure_3550_);
        crate::leanh::lean_dec_ref(v_toApplicative_3549_);
        v___x_3551_ =
            crate::leanh::lean_apply_2(v_toPure_3550_, crate::leanh::lean_box(0), v_e_3547_);
        return v___x_3551_;
    } else {
        match crate::leanh::lean_obj_tag(v_e_3547_) {
            1 => {
                let mut v_fvarId_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toApplicative_3553_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_fvarId_3552_ = crate::leanh::lean_ctor_get(v_e_3547_, 0);
                crate::leanh::lean_inc_n(v_fvarId_3552_, 2);
                v_toApplicative_3553_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3553_);
                v_toBind_3554_ = crate::leanh::lean_ctor_get(v_inst_3545_, 1);
                crate::leanh::lean_inc(v_toBind_3554_);
                crate::leanh::lean_dec_ref(v_inst_3545_);
                v___f_3555_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3555_, 0, v_toApplicative_3553_);
                crate::leanh::lean_closure_set(v___f_3555_, 1, v_fvarId_3552_);
                crate::leanh::lean_closure_set(v___f_3555_, 2, v_e_3547_);
                v___x_3556_ = crate::leanh::lean_apply_1(v_f_3546_, v_fvarId_3552_);
                v___x_3557_ = crate::leanh::lean_apply_4(
                    v_toBind_3554_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3556_,
                    v___f_3555_,
                );
                return v___x_3557_;
            }
            2 => {
                let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_e_3547_, 1);
                crate::leanh::lean_dec(v_f_3546_);
                v___x_3558_ = l_Lean_instInhabitedExpr;
                v___x_3559_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3558_);
                v___x_3560_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3561_ = l_panic___redArg(v___x_3559_, v___x_3560_);
                crate::leanh::lean_dec(v___x_3559_);
                return v___x_3561_;
            }
            5 => {
                let mut v_fn_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_arg_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toApplicative_3564_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_fn_3562_ = crate::leanh::lean_ctor_get(v_e_3547_, 0);
                crate::leanh::lean_inc_ref_n(v_fn_3562_, 2);
                v_arg_3563_ = crate::leanh::lean_ctor_get(v_e_3547_, 1);
                crate::leanh::lean_inc_ref(v_arg_3563_);
                v_toApplicative_3564_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3565_ = crate::leanh::lean_ctor_get(v_inst_3545_, 1);
                crate::leanh::lean_inc_n(v_toBind_3565_, 2);
                crate::leanh::lean_inc(v_f_3546_);
                crate::leanh::lean_inc_ref(v_inst_3545_);
                crate::leanh::lean_inc_ref(v_toApplicative_3564_);
                v___f_3566_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2 as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_3566_, 0, v_toApplicative_3564_);
                crate::leanh::lean_closure_set(v___f_3566_, 1, v_e_3547_);
                crate::leanh::lean_closure_set(v___f_3566_, 2, v_fn_3562_);
                crate::leanh::lean_closure_set(v___f_3566_, 3, v_arg_3563_);
                crate::leanh::lean_closure_set(v___f_3566_, 4, v_inst_3545_);
                crate::leanh::lean_closure_set(v___f_3566_, 5, v_f_3546_);
                crate::leanh::lean_closure_set(v___f_3566_, 6, v_toBind_3565_);
                v___x_3567_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_fn_3562_,
                );
                v___x_3568_ = crate::leanh::lean_apply_4(
                    v_toBind_3565_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3567_,
                    v___f_3566_,
                );
                return v___x_3568_;
            }
            6 => {
                let mut v_binderName_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_binderType_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_body_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_binderInfo_3572_: u8 = 0;
                let mut v_toApplicative_3573_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_binderName_3569_ = crate::leanh::lean_ctor_get(v_e_3547_, 0);
                crate::leanh::lean_inc(v_binderName_3569_);
                v_binderType_3570_ = crate::leanh::lean_ctor_get(v_e_3547_, 1);
                crate::leanh::lean_inc_ref_n(v_binderType_3570_, 2);
                v_body_3571_ = crate::leanh::lean_ctor_get(v_e_3547_, 2);
                crate::leanh::lean_inc_ref(v_body_3571_);
                v_binderInfo_3572_ = crate::leanh::lean_ctor_get_uint8(
                    v_e_3547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                );
                v_toApplicative_3573_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3574_ = crate::leanh::lean_ctor_get(v_inst_3545_, 1);
                crate::leanh::lean_inc_n(v_toBind_3574_, 2);
                v___x_3575_ = crate::leanh::lean_box((v_binderInfo_3572_) as usize);
                crate::leanh::lean_inc(v_f_3546_);
                crate::leanh::lean_inc_ref(v_inst_3545_);
                crate::leanh::lean_inc_ref(v_toApplicative_3573_);
                v___f_3576_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_3576_, 0, v_toApplicative_3573_);
                crate::leanh::lean_closure_set(v___f_3576_, 1, v_binderName_3569_);
                crate::leanh::lean_closure_set(v___f_3576_, 2, v___x_3575_);
                crate::leanh::lean_closure_set(v___f_3576_, 3, v_e_3547_);
                crate::leanh::lean_closure_set(v___f_3576_, 4, v_binderType_3570_);
                crate::leanh::lean_closure_set(v___f_3576_, 5, v_body_3571_);
                crate::leanh::lean_closure_set(v___f_3576_, 6, v_inst_3545_);
                crate::leanh::lean_closure_set(v___f_3576_, 7, v_f_3546_);
                crate::leanh::lean_closure_set(v___f_3576_, 8, v_toBind_3574_);
                v___x_3577_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_binderType_3570_,
                );
                v___x_3578_ = crate::leanh::lean_apply_4(
                    v_toBind_3574_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3577_,
                    v___f_3576_,
                );
                return v___x_3578_;
            }
            7 => {
                let mut v_binderName_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_binderType_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_body_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_binderInfo_3582_: u8 = 0;
                let mut v_toApplicative_3583_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_binderName_3579_ = crate::leanh::lean_ctor_get(v_e_3547_, 0);
                crate::leanh::lean_inc(v_binderName_3579_);
                v_binderType_3580_ = crate::leanh::lean_ctor_get(v_e_3547_, 1);
                crate::leanh::lean_inc_ref_n(v_binderType_3580_, 2);
                v_body_3581_ = crate::leanh::lean_ctor_get(v_e_3547_, 2);
                crate::leanh::lean_inc_ref(v_body_3581_);
                v_binderInfo_3582_ = crate::leanh::lean_ctor_get_uint8(
                    v_e_3547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                );
                v_toApplicative_3583_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
                v_toBind_3584_ = crate::leanh::lean_ctor_get(v_inst_3545_, 1);
                crate::leanh::lean_inc_n(v_toBind_3584_, 2);
                v___x_3585_ = crate::leanh::lean_box((v_binderInfo_3582_) as usize);
                crate::leanh::lean_inc(v_f_3546_);
                crate::leanh::lean_inc_ref(v_inst_3545_);
                crate::leanh::lean_inc_ref(v_toApplicative_3583_);
                v___f_3586_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_3586_, 0, v_toApplicative_3583_);
                crate::leanh::lean_closure_set(v___f_3586_, 1, v_binderName_3579_);
                crate::leanh::lean_closure_set(v___f_3586_, 2, v___x_3585_);
                crate::leanh::lean_closure_set(v___f_3586_, 3, v_e_3547_);
                crate::leanh::lean_closure_set(v___f_3586_, 4, v_binderType_3580_);
                crate::leanh::lean_closure_set(v___f_3586_, 5, v_body_3581_);
                crate::leanh::lean_closure_set(v___f_3586_, 6, v_inst_3545_);
                crate::leanh::lean_closure_set(v___f_3586_, 7, v_f_3546_);
                crate::leanh::lean_closure_set(v___f_3586_, 8, v_toBind_3584_);
                v___x_3587_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                    v_inst_3545_,
                    v_f_3546_,
                    v_binderType_3580_,
                );
                v___x_3588_ = crate::leanh::lean_apply_4(
                    v_toBind_3584_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3587_,
                    v___f_3586_,
                );
                return v___x_3588_;
            }
            8 => {
                let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_e_3547_, 4);
                crate::leanh::lean_dec(v_f_3546_);
                v___x_3589_ = l_Lean_instInhabitedExpr;
                v___x_3590_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3589_);
                v___x_3591_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3592_ = l_panic___redArg(v___x_3590_, v___x_3591_);
                crate::leanh::lean_dec(v___x_3590_);
                return v___x_3592_;
            }
            11 => {
                let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_e_3547_, 3);
                crate::leanh::lean_dec(v_f_3546_);
                v___x_3593_ = l_Lean_instInhabitedExpr;
                v___x_3594_ = l_instInhabitedOfMonad___redArg(v_inst_3545_, v___x_3593_);
                v___x_3595_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__3,
                );
                v___x_3596_ = l_panic___redArg(v___x_3594_, v___x_3595_);
                crate::leanh::lean_dec(v___x_3594_);
                return v___x_3596_;
            }
            _ => {
                let mut v_toApplicative_3597_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_f_3546_);
                v_toApplicative_3597_ = crate::leanh::lean_ctor_get(v_inst_3545_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_3597_);
                crate::leanh::lean_dec_ref(v_inst_3545_);
                v_toPure_3598_ = crate::leanh::lean_ctor_get(v_toApplicative_3597_, 1);
                crate::leanh::lean_inc(v_toPure_3598_);
                crate::leanh::lean_dec_ref(v_toApplicative_3597_);
                v___x_3599_ = crate::leanh::lean_apply_2(
                    v_toPure_3598_,
                    crate::leanh::lean_box(0),
                    v_e_3547_,
                );
                return v___x_3599_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__2(
    mut v_toApplicative_3600_: *mut crate::leanh::LeanObject,
    mut v_e_3601_: *mut crate::leanh::LeanObject,
    mut v_fn_3602_: *mut crate::leanh::LeanObject,
    mut v_arg_3603_: *mut crate::leanh::LeanObject,
    mut v_inst_3604_: *mut crate::leanh::LeanObject,
    mut v_f_3605_: *mut crate::leanh::LeanObject,
    mut v_toBind_3606_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_arg_3603_);
    v___f_3608_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3608_, 0, v_toApplicative_3600_);
    crate::leanh::lean_closure_set(v___f_3608_, 1, v_____do__lift_3607_);
    crate::leanh::lean_closure_set(v___f_3608_, 2, v_e_3601_);
    crate::leanh::lean_closure_set(v___f_3608_, 3, v_fn_3602_);
    crate::leanh::lean_closure_set(v___f_3608_, 4, v_arg_3603_);
    v___x_3609_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3604_, v_f_3605_, v_arg_3603_);
    v___x_3610_ = crate::leanh::lean_apply_4(
        v_toBind_3606_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3609_,
        v___f_3608_,
    );
    return v___x_3610_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM(
    mut v_m_3611_: *mut crate::leanh::LeanObject,
    mut v_inst_3612_: *mut crate::leanh::LeanObject,
    mut v_inst_3613_: *mut crate::leanh::LeanObject,
    mut v_f_3614_: *mut crate::leanh::LeanObject,
    mut v_e_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3613_, v_f_3614_, v_e_3615_);
    return v___x_3616_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_mapFVarM___boxed(
    mut v_m_3617_: *mut crate::leanh::LeanObject,
    mut v_inst_3618_: *mut crate::leanh::LeanObject,
    mut v_inst_3619_: *mut crate::leanh::LeanObject,
    mut v_f_3620_: *mut crate::leanh::LeanObject,
    mut v_e_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3622_ = l_Lean_Compiler_LCNF_Expr_mapFVarM(
        v_m_3617_,
        v_inst_3618_,
        v_inst_3619_,
        v_f_3620_,
        v_e_3621_,
    );
    crate::leanh::lean_dec(v_inst_3618_);
    return v_res_3622_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3624_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__2;
    v___x_3625_ = crate::leanh::lean_unsigned_to_nat(40);
    v___x_3626_ = crate::leanh::lean_unsigned_to_nat(49);
    v___x_3627_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__0;
    v___x_3628_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg___closed__0;
    v___x_3629_ = l_mkPanicMessageWithDecl(
        v___x_3628_,
        v___x_3627_,
        v___x_3626_,
        v___x_3625_,
        v___x_3624_,
    );
    return v___x_3629_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1(
    mut v_inst_3630_: *mut crate::leanh::LeanObject,
    mut v_f_3631_: *mut crate::leanh::LeanObject,
    mut v_arg_3632_: *mut crate::leanh::LeanObject,
    mut v_____r_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3630_, v_f_3631_, v_arg_3632_);
    return v___x_3634_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
    mut v_inst_3635_: *mut crate::leanh::LeanObject,
    mut v_f_3636_: *mut crate::leanh::LeanObject,
    mut v_e_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: u8 = 0;
    let mut v_toApplicative_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3645_ = l_Lean_Expr_hasFVar(v_e_3637_);
                if v___x_3645_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3637_);
                    crate::leanh::lean_dec(v_f_3636_);
                    v_toApplicative_3646_ = crate::leanh::lean_ctor_get(v_inst_3635_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_3646_);
                    crate::leanh::lean_dec_ref(v_inst_3635_);
                    v_toPure_3647_ = crate::leanh::lean_ctor_get(v_toApplicative_3646_, 1);
                    crate::leanh::lean_inc(v_toPure_3647_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3646_);
                    v___x_3648_ = crate::leanh::lean_box(0);
                    v___x_3649_ = crate::leanh::lean_apply_2(
                        v_toPure_3647_,
                        crate::leanh::lean_box(0),
                        v___x_3648_,
                    );
                    return v___x_3649_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_3637_) {
                        1 => {
                            crate::leanh::lean_dec_ref(v_inst_3635_);
                            v_fvarId_3650_ = crate::leanh::lean_ctor_get(v_e_3637_, 0);
                            crate::leanh::lean_inc(v_fvarId_3650_);
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 1);
                            v___x_3651_ = crate::leanh::lean_apply_1(v_f_3636_, v_fvarId_3650_);
                            return v___x_3651_;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 1);
                            crate::leanh::lean_dec(v_f_3636_);
                            v___x_3652_ = crate::leanh::lean_box(0);
                            v___x_3653_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3652_);
                            v___x_3654_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3655_ = l_panic___redArg(v___x_3653_, v___x_3654_);
                            crate::leanh::lean_dec(v___x_3653_);
                            return v___x_3655_;
                        }
                        5 => {
                            v_fn_3656_ = crate::leanh::lean_ctor_get(v_e_3637_, 0);
                            crate::leanh::lean_inc_ref(v_fn_3656_);
                            v_arg_3657_ = crate::leanh::lean_ctor_get(v_e_3637_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3657_);
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 2);
                            v_toBind_3658_ = crate::leanh::lean_ctor_get(v_inst_3635_, 1);
                            crate::leanh::lean_inc(v_toBind_3658_);
                            crate::leanh::lean_inc(v_f_3636_);
                            crate::leanh::lean_inc_ref(v_inst_3635_);
                            v___f_3659_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__1
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_3659_, 0, v_inst_3635_);
                            crate::leanh::lean_closure_set(v___f_3659_, 1, v_f_3636_);
                            crate::leanh::lean_closure_set(v___f_3659_, 2, v_arg_3657_);
                            v___x_3660_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                                v_inst_3635_,
                                v_f_3636_,
                                v_fn_3656_,
                            );
                            v___x_3661_ = crate::leanh::lean_apply_4(
                                v_toBind_3658_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3660_,
                                v___f_3659_,
                            );
                            return v___x_3661_;
                        }
                        6 => {
                            v_binderType_3662_ = crate::leanh::lean_ctor_get(v_e_3637_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_3662_);
                            v_body_3663_ = crate::leanh::lean_ctor_get(v_e_3637_, 2);
                            crate::leanh::lean_inc_ref(v_body_3663_);
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 3);
                            v_ty_3639_ = v_binderType_3662_;
                            v_body_3640_ = v_body_3663_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_3664_ = crate::leanh::lean_ctor_get(v_e_3637_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_3664_);
                            v_body_3665_ = crate::leanh::lean_ctor_get(v_e_3637_, 2);
                            crate::leanh::lean_inc_ref(v_body_3665_);
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 3);
                            v_ty_3639_ = v_binderType_3664_;
                            v_body_3640_ = v_body_3665_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 4);
                            crate::leanh::lean_dec(v_f_3636_);
                            v___x_3666_ = crate::leanh::lean_box(0);
                            v___x_3667_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3666_);
                            v___x_3668_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3669_ = l_panic___redArg(v___x_3667_, v___x_3668_);
                            crate::leanh::lean_dec(v___x_3667_);
                            return v___x_3669_;
                        }
                        11 => {
                            crate::leanh::lean_dec_ref_known(v_e_3637_, 3);
                            crate::leanh::lean_dec(v_f_3636_);
                            v___x_3670_ = crate::leanh::lean_box(0);
                            v___x_3671_ =
                                l_instInhabitedOfMonad___redArg(v_inst_3635_, v___x_3670_);
                            v___x_3672_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___closed__1,
                            );
                            v___x_3673_ = l_panic___redArg(v___x_3671_, v___x_3672_);
                            crate::leanh::lean_dec(v___x_3671_);
                            return v___x_3673_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_3637_);
                            crate::leanh::lean_dec(v_f_3636_);
                            v_toApplicative_3674_ = crate::leanh::lean_ctor_get(v_inst_3635_, 0);
                            crate::leanh::lean_inc_ref(v_toApplicative_3674_);
                            crate::leanh::lean_dec_ref(v_inst_3635_);
                            v_toPure_3675_ = crate::leanh::lean_ctor_get(v_toApplicative_3674_, 1);
                            crate::leanh::lean_inc(v_toPure_3675_);
                            crate::leanh::lean_dec_ref(v_toApplicative_3674_);
                            v___x_3676_ = crate::leanh::lean_box(0);
                            v___x_3677_ = crate::leanh::lean_apply_2(
                                v_toPure_3675_,
                                crate::leanh::lean_box(0),
                                v___x_3676_,
                            );
                            return v___x_3677_;
                        }
                    }
                }
            }
            1 => {
                v_toBind_3641_ = crate::leanh::lean_ctor_get(v_inst_3635_, 1);
                crate::leanh::lean_inc(v_toBind_3641_);
                crate::leanh::lean_inc(v_f_3636_);
                crate::leanh::lean_inc_ref(v_inst_3635_);
                v___f_3642_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3642_, 0, v_inst_3635_);
                crate::leanh::lean_closure_set(v___f_3642_, 1, v_f_3636_);
                crate::leanh::lean_closure_set(v___f_3642_, 2, v_body_3640_);
                v___x_3643_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                    v_inst_3635_,
                    v_f_3636_,
                    v_ty_3639_,
                );
                v___x_3644_ = crate::leanh::lean_apply_4(
                    v_toBind_3641_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3643_,
                    v___f_3642_,
                );
                return v___x_3644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___redArg___lam__0(
    mut v_inst_3678_: *mut crate::leanh::LeanObject,
    mut v_f_3679_: *mut crate::leanh::LeanObject,
    mut v_body_3680_: *mut crate::leanh::LeanObject,
    mut v_____r_3681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3682_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3678_, v_f_3679_, v_body_3680_);
    return v___x_3682_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM(
    mut v_m_3683_: *mut crate::leanh::LeanObject,
    mut v_inst_3684_: *mut crate::leanh::LeanObject,
    mut v_f_3685_: *mut crate::leanh::LeanObject,
    mut v_e_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3684_, v_f_3685_, v_e_3686_);
    return v___x_3687_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(
    mut v_m_3688_: *mut crate::leanh::LeanObject,
    mut v_inst_3689_: *mut crate::leanh::LeanObject,
    mut v_inst_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3693_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3690_, v___y_3691_, v___y_3692_);
    return v___x_3693_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0___boxed(
    mut v_m_3694_: *mut crate::leanh::LeanObject,
    mut v_inst_3695_: *mut crate::leanh::LeanObject,
    mut v_inst_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__0(
        v_m_3694_,
        v_inst_3695_,
        v_inst_3696_,
        v___y_3697_,
        v___y_3698_,
    );
    crate::leanh::lean_dec(v_inst_3695_);
    return v_res_3699_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarExpr___lam__1(
    mut v_m_3700_: *mut crate::leanh::LeanObject,
    mut v_inst_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3704_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3701_, v___y_3702_, v___y_3703_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0(
    mut v_arg_3711_: *mut crate::leanh::LeanObject,
    mut v_toPure_3712_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(
            v_arg_3711_,
            v_____do__lift_3713_,
        );
    v___x_3715_ =
        crate::leanh::lean_apply_2(v_toPure_3712_, crate::leanh::lean_box(0), v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(
    mut v_pu_3716_: u8,
    mut v_arg_3717_: *mut crate::leanh::LeanObject,
    mut v_toPure_3718_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(
        v_pu_3716_,
        v_arg_3717_,
        v_____do__lift_3719_,
    );
    v___x_3721_ =
        crate::leanh::lean_apply_2(v_toPure_3718_, crate::leanh::lean_box(0), v___x_3720_);
    return v___x_3721_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_3722_: *mut crate::leanh::LeanObject,
    mut v_arg_3723_: *mut crate::leanh::LeanObject,
    mut v_toPure_3724_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3726_: u8 = 0;
    let mut v_res_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3726_ = (crate::leanh::lean_unbox(v_pu_3722_) as u8);
    v_res_3727_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1(
        v_pu_boxed_3726_,
        v_arg_3723_,
        v_toPure_3724_,
        v_____do__lift_3725_,
    );
    return v_res_3727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
    mut v_pu_3728_: u8,
    mut v_inst_3729_: *mut crate::leanh::LeanObject,
    mut v_f_3730_: *mut crate::leanh::LeanObject,
    mut v_arg_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_arg_3731_) {
        0 => {
            let mut v_toApplicative_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3732_ = crate::leanh::lean_ctor_get(v_inst_3729_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_3732_);
            crate::leanh::lean_dec(v_f_3730_);
            crate::leanh::lean_dec_ref(v_inst_3729_);
            v_toPure_3733_ = crate::leanh::lean_ctor_get(v_toApplicative_3732_, 1);
            crate::leanh::lean_inc(v_toPure_3733_);
            crate::leanh::lean_dec_ref(v_toApplicative_3732_);
            v___x_3734_ = crate::leanh::lean_box(0);
            v___x_3735_ =
                crate::leanh::lean_apply_2(v_toPure_3733_, crate::leanh::lean_box(0), v___x_3734_);
            return v___x_3735_;
        }
        1 => {
            let mut v_toApplicative_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3736_ = crate::leanh::lean_ctor_get(v_inst_3729_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_3736_);
            v_toBind_3737_ = crate::leanh::lean_ctor_get(v_inst_3729_, 1);
            crate::leanh::lean_inc(v_toBind_3737_);
            crate::leanh::lean_dec_ref(v_inst_3729_);
            v_toPure_3738_ = crate::leanh::lean_ctor_get(v_toApplicative_3736_, 1);
            crate::leanh::lean_inc(v_toPure_3738_);
            crate::leanh::lean_dec_ref(v_toApplicative_3736_);
            v_fvarId_3739_ = crate::leanh::lean_ctor_get(v_arg_3731_, 0);
            crate::leanh::lean_inc(v_fvarId_3739_);
            v___f_3740_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_3740_, 0, v_arg_3731_);
            crate::leanh::lean_closure_set(v___f_3740_, 1, v_toPure_3738_);
            v___x_3741_ = crate::leanh::lean_apply_1(v_f_3730_, v_fvarId_3739_);
            v___x_3742_ = crate::leanh::lean_apply_4(
                v_toBind_3737_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_3741_,
                v___f_3740_,
            );
            return v___x_3742_;
        }
        _ => {
            let mut v_toApplicative_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3743_ = crate::leanh::lean_ctor_get(v_inst_3729_, 0);
            v_toBind_3744_ = crate::leanh::lean_ctor_get(v_inst_3729_, 1);
            crate::leanh::lean_inc(v_toBind_3744_);
            v_toPure_3745_ = crate::leanh::lean_ctor_get(v_toApplicative_3743_, 1);
            v_expr_3746_ = crate::leanh::lean_ctor_get(v_arg_3731_, 0);
            crate::leanh::lean_inc_ref(v_expr_3746_);
            v___x_3747_ = crate::leanh::lean_box((v_pu_3728_) as usize);
            crate::leanh::lean_inc(v_toPure_3745_);
            v___f_3748_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_3748_, 0, v___x_3747_);
            crate::leanh::lean_closure_set(v___f_3748_, 1, v_arg_3731_);
            crate::leanh::lean_closure_set(v___f_3748_, 2, v_toPure_3745_);
            v___x_3749_ =
                l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_3729_, v_f_3730_, v_expr_3746_);
            v___x_3750_ = crate::leanh::lean_apply_4(
                v_toBind_3744_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_3749_,
                v___f_3748_,
            );
            return v___x_3750_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg___boxed(
    mut v_pu_3751_: *mut crate::leanh::LeanObject,
    mut v_inst_3752_: *mut crate::leanh::LeanObject,
    mut v_f_3753_: *mut crate::leanh::LeanObject,
    mut v_arg_3754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3755_: u8 = 0;
    let mut v_res_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3755_ = (crate::leanh::lean_unbox(v_pu_3751_) as u8);
    v_res_3756_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_boxed_3755_,
        v_inst_3752_,
        v_f_3753_,
        v_arg_3754_,
    );
    return v_res_3756_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM(
    mut v_m_3757_: *mut crate::leanh::LeanObject,
    mut v_pu_3758_: u8,
    mut v_inst_3759_: *mut crate::leanh::LeanObject,
    mut v_inst_3760_: *mut crate::leanh::LeanObject,
    mut v_f_3761_: *mut crate::leanh::LeanObject,
    mut v_arg_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3758_,
        v_inst_3760_,
        v_f_3761_,
        v_arg_3762_,
    );
    return v___x_3763_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed(
    mut v_m_3764_: *mut crate::leanh::LeanObject,
    mut v_pu_3765_: *mut crate::leanh::LeanObject,
    mut v_inst_3766_: *mut crate::leanh::LeanObject,
    mut v_inst_3767_: *mut crate::leanh::LeanObject,
    mut v_f_3768_: *mut crate::leanh::LeanObject,
    mut v_arg_3769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3770_: u8 = 0;
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3770_ = (crate::leanh::lean_unbox(v_pu_3765_) as u8);
    v_res_3771_ = l_Lean_Compiler_LCNF_Arg_mapFVarM(
        v_m_3764_,
        v_pu_boxed_3770_,
        v_inst_3766_,
        v_inst_3767_,
        v_f_3768_,
        v_arg_3769_,
    );
    crate::leanh::lean_dec(v_inst_3766_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(
    mut v_inst_3772_: *mut crate::leanh::LeanObject,
    mut v_f_3773_: *mut crate::leanh::LeanObject,
    mut v_arg_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_arg_3774_) {
        0 => {
            let mut v_toApplicative_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3775_ = crate::leanh::lean_ctor_get(v_inst_3772_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_3775_);
            crate::leanh::lean_dec(v_f_3773_);
            crate::leanh::lean_dec_ref(v_inst_3772_);
            v_toPure_3776_ = crate::leanh::lean_ctor_get(v_toApplicative_3775_, 1);
            crate::leanh::lean_inc(v_toPure_3776_);
            crate::leanh::lean_dec_ref(v_toApplicative_3775_);
            v___x_3777_ = crate::leanh::lean_box(0);
            v___x_3778_ =
                crate::leanh::lean_apply_2(v_toPure_3776_, crate::leanh::lean_box(0), v___x_3777_);
            return v___x_3778_;
        }
        1 => {
            let mut v_fvarId_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_3772_);
            v_fvarId_3779_ = crate::leanh::lean_ctor_get(v_arg_3774_, 0);
            crate::leanh::lean_inc(v_fvarId_3779_);
            crate::leanh::lean_dec_ref_known(v_arg_3774_, 1);
            v___x_3780_ = crate::leanh::lean_apply_1(v_f_3773_, v_fvarId_3779_);
            return v___x_3780_;
        }
        _ => {
            let mut v_expr_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_expr_3781_ = crate::leanh::lean_ctor_get(v_arg_3774_, 0);
            crate::leanh::lean_inc_ref(v_expr_3781_);
            crate::leanh::lean_dec_ref_known(v_arg_3774_, 1);
            v___x_3782_ =
                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_3772_, v_f_3773_, v_expr_3781_);
            return v___x_3782_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM(
    mut v_m_3783_: *mut crate::leanh::LeanObject,
    mut v_pu_3784_: u8,
    mut v_inst_3785_: *mut crate::leanh::LeanObject,
    mut v_f_3786_: *mut crate::leanh::LeanObject,
    mut v_arg_3787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3788_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_3785_, v_f_3786_, v_arg_3787_);
    return v___x_3788_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___boxed(
    mut v_m_3789_: *mut crate::leanh::LeanObject,
    mut v_pu_3790_: *mut crate::leanh::LeanObject,
    mut v_inst_3791_: *mut crate::leanh::LeanObject,
    mut v_f_3792_: *mut crate::leanh::LeanObject,
    mut v_arg_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3794_: u8 = 0;
    let mut v_res_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3794_ = (crate::leanh::lean_unbox(v_pu_3790_) as u8);
    v_res_3795_ = l_Lean_Compiler_LCNF_Arg_forFVarM(
        v_m_3789_,
        v_pu_boxed_3794_,
        v_inst_3791_,
        v_f_3792_,
        v_arg_3793_,
    );
    return v_res_3795_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(
    mut v_pu_3796_: u8,
    mut v_m_3797_: *mut crate::leanh::LeanObject,
    mut v_inst_3798_: *mut crate::leanh::LeanObject,
    mut v_inst_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3796_,
        v_inst_3799_,
        v___y_3800_,
        v___y_3801_,
    );
    return v___x_3802_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed(
    mut v_pu_3803_: *mut crate::leanh::LeanObject,
    mut v_m_3804_: *mut crate::leanh::LeanObject,
    mut v_inst_3805_: *mut crate::leanh::LeanObject,
    mut v_inst_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3809_: u8 = 0;
    let mut v_res_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3809_ = (crate::leanh::lean_unbox(v_pu_3803_) as u8);
    v_res_3810_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0(
        v_pu_boxed_3809_,
        v_m_3804_,
        v_inst_3805_,
        v_inst_3806_,
        v___y_3807_,
        v___y_3808_,
    );
    crate::leanh::lean_dec(v_inst_3805_);
    return v_res_3810_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__1(
    mut v_m_3811_: *mut crate::leanh::LeanObject,
    mut v_inst_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ =
        l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_3812_, v___y_3813_, v___y_3814_);
    return v___x_3815_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg(
    mut v_pu_3817_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3818_ = crate::leanh::lean_box((v_pu_3817_) as usize);
    v___f_3819_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3819_, 0, v___x_3818_);
    v___f_3820_ = l_Lean_Compiler_LCNF_instTraverseFVarArg___closed__0;
    v___x_3821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3821_, 0, v___f_3819_);
    crate::leanh::lean_ctor_set(v___x_3821_, 1, v___f_3820_);
    return v___x_3821_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarArg___boxed(
    mut v_pu_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3823_: u8 = 0;
    let mut v_res_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3823_ = (crate::leanh::lean_unbox(v_pu_3822_) as u8);
    v_res_3824_ = l_Lean_Compiler_LCNF_instTraverseFVarArg(v_pu_boxed_3823_);
    return v_res_3824_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(
    mut v_pu_3825_: u8,
    mut v_inst_3826_: *mut crate::leanh::LeanObject,
    mut v_f_3827_: *mut crate::leanh::LeanObject,
    mut v___y_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3829_ = l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(
        v_pu_3825_,
        v_inst_3826_,
        v_f_3827_,
        v___y_3828_,
    );
    return v___x_3829_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_3830_: *mut crate::leanh::LeanObject,
    mut v_inst_3831_: *mut crate::leanh::LeanObject,
    mut v_f_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3834_: u8 = 0;
    let mut v_res_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3834_ = (crate::leanh::lean_unbox(v_pu_3830_) as u8);
    v_res_3835_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0(
        v_pu_boxed_3834_,
        v_inst_3831_,
        v_f_3832_,
        v___y_3833_,
    );
    return v_res_3835_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(
    mut v_pu_3836_: u8,
    mut v_e_3837_: *mut crate::leanh::LeanObject,
    mut v_toPure_3838_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3840_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(
        v_pu_3836_,
        v_e_3837_,
        v_____do__lift_3839_,
    );
    v___x_3841_ =
        crate::leanh::lean_apply_2(v_toPure_3838_, crate::leanh::lean_box(0), v___x_3840_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_3842_: *mut crate::leanh::LeanObject,
    mut v_e_3843_: *mut crate::leanh::LeanObject,
    mut v_toPure_3844_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3846_: u8 = 0;
    let mut v_res_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3846_ = (crate::leanh::lean_unbox(v_pu_3842_) as u8);
    v_res_3847_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1(
        v_pu_boxed_3846_,
        v_e_3843_,
        v_toPure_3844_,
        v_____do__lift_3845_,
    );
    return v_res_3847_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(
    mut v_pu_3848_: u8,
    mut v_e_3849_: *mut crate::leanh::LeanObject,
    mut v_toPure_3850_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(
        v_pu_3848_,
        v_e_3849_,
        v_____do__lift_3851_,
    );
    v___x_3853_ =
        crate::leanh::lean_apply_2(v_toPure_3850_, crate::leanh::lean_box(0), v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed(
    mut v_pu_3854_: *mut crate::leanh::LeanObject,
    mut v_e_3855_: *mut crate::leanh::LeanObject,
    mut v_toPure_3856_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3858_: u8 = 0;
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3858_ = (crate::leanh::lean_unbox(v_pu_3854_) as u8);
    v_res_3859_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2(
        v_pu_boxed_3858_,
        v_e_3855_,
        v_toPure_3856_,
        v_____do__lift_3857_,
    );
    return v_res_3859_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(
    mut v_pu_3860_: u8,
    mut v_e_3861_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3862_: *mut crate::leanh::LeanObject,
    mut v_toPure_3863_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3865_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(
        v_pu_3860_,
        v_e_3861_,
        v_____do__lift_3862_,
        v_____do__lift_3864_,
    );
    v___x_3866_ =
        crate::leanh::lean_apply_2(v_toPure_3863_, crate::leanh::lean_box(0), v___x_3865_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed(
    mut v_pu_3867_: *mut crate::leanh::LeanObject,
    mut v_e_3868_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3869_: *mut crate::leanh::LeanObject,
    mut v_toPure_3870_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3872_: u8 = 0;
    let mut v_res_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3872_ = (crate::leanh::lean_unbox(v_pu_3867_) as u8);
    v_res_3873_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7(
        v_pu_boxed_3872_,
        v_e_3868_,
        v_____do__lift_3869_,
        v_toPure_3870_,
        v_____do__lift_3871_,
    );
    crate::leanh::lean_dec(v_e_3868_);
    return v_res_3873_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(
    mut v_pu_3874_: u8,
    mut v_e_3875_: *mut crate::leanh::LeanObject,
    mut v_toPure_3876_: *mut crate::leanh::LeanObject,
    mut v_args_3877_: *mut crate::leanh::LeanObject,
    mut v_inst_3878_: *mut crate::leanh::LeanObject,
    mut v___f_3879_: *mut crate::leanh::LeanObject,
    mut v_toBind_3880_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3884_: usize = 0;
    let mut v___x_3885_: usize = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = crate::leanh::lean_box((v_pu_3874_) as usize);
    v___f_3883_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3883_, 0, v___x_3882_);
    crate::leanh::lean_closure_set(v___f_3883_, 1, v_e_3875_);
    crate::leanh::lean_closure_set(v___f_3883_, 2, v_____do__lift_3881_);
    crate::leanh::lean_closure_set(v___f_3883_, 3, v_toPure_3876_);
    v_sz_3884_ = lean_array_size(v_args_3877_);
    v___x_3885_ = 0usize;
    v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_3878_,
        v___f_3879_,
        v_sz_3884_,
        v___x_3885_,
        v_args_3877_,
    );
    v___x_3887_ = crate::leanh::lean_apply_4(
        v_toBind_3880_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3886_,
        v___f_3883_,
    );
    return v___x_3887_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed(
    mut v_pu_3888_: *mut crate::leanh::LeanObject,
    mut v_e_3889_: *mut crate::leanh::LeanObject,
    mut v_toPure_3890_: *mut crate::leanh::LeanObject,
    mut v_args_3891_: *mut crate::leanh::LeanObject,
    mut v_inst_3892_: *mut crate::leanh::LeanObject,
    mut v___f_3893_: *mut crate::leanh::LeanObject,
    mut v_toBind_3894_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3896_: u8 = 0;
    let mut v_res_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3896_ = (crate::leanh::lean_unbox(v_pu_3888_) as u8);
    v_res_3897_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3(
        v_pu_boxed_3896_,
        v_e_3889_,
        v_toPure_3890_,
        v_args_3891_,
        v_inst_3892_,
        v___f_3893_,
        v_toBind_3894_,
        v_____do__lift_3895_,
    );
    return v_res_3897_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(
    mut v_pu_3898_: u8,
    mut v_e_3899_: *mut crate::leanh::LeanObject,
    mut v_n_3900_: *mut crate::leanh::LeanObject,
    mut v_toPure_3901_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3903_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(
            v_pu_3898_,
            v_e_3899_,
            v_n_3900_,
            v_____do__lift_3902_,
        );
    v___x_3904_ =
        crate::leanh::lean_apply_2(v_toPure_3901_, crate::leanh::lean_box(0), v___x_3903_);
    return v___x_3904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed(
    mut v_pu_3905_: *mut crate::leanh::LeanObject,
    mut v_e_3906_: *mut crate::leanh::LeanObject,
    mut v_n_3907_: *mut crate::leanh::LeanObject,
    mut v_toPure_3908_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3910_: u8 = 0;
    let mut v_res_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3910_ = (crate::leanh::lean_unbox(v_pu_3905_) as u8);
    v_res_3911_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8(
        v_pu_boxed_3910_,
        v_e_3906_,
        v_n_3907_,
        v_toPure_3908_,
        v_____do__lift_3909_,
    );
    crate::leanh::lean_dec(v_e_3906_);
    return v_res_3911_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(
    mut v_pu_3912_: u8,
    mut v_e_3913_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3914_: *mut crate::leanh::LeanObject,
    mut v_i_3915_: *mut crate::leanh::LeanObject,
    mut v_updateHeader_3916_: u8,
    mut v_toPure_3917_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(
            v_pu_3912_,
            v_e_3913_,
            v_____do__lift_3914_,
            v_i_3915_,
            v_updateHeader_3916_,
            v_____do__lift_3918_,
        );
    v___x_3920_ =
        crate::leanh::lean_apply_2(v_toPure_3917_, crate::leanh::lean_box(0), v___x_3919_);
    return v___x_3920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed(
    mut v_pu_3921_: *mut crate::leanh::LeanObject,
    mut v_e_3922_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3923_: *mut crate::leanh::LeanObject,
    mut v_i_3924_: *mut crate::leanh::LeanObject,
    mut v_updateHeader_3925_: *mut crate::leanh::LeanObject,
    mut v_toPure_3926_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3928_: u8 = 0;
    let mut v_updateHeader_627__boxed_3929_: u8 = 0;
    let mut v_res_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3928_ = (crate::leanh::lean_unbox(v_pu_3921_) as u8);
    v_updateHeader_627__boxed_3929_ = (crate::leanh::lean_unbox(v_updateHeader_3925_) as u8);
    v_res_3930_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5(
        v_pu_boxed_3928_,
        v_e_3922_,
        v_____do__lift_3923_,
        v_i_3924_,
        v_updateHeader_627__boxed_3929_,
        v_toPure_3926_,
        v_____do__lift_3927_,
    );
    return v_res_3930_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(
    mut v_pu_3931_: u8,
    mut v_e_3932_: *mut crate::leanh::LeanObject,
    mut v_i_3933_: *mut crate::leanh::LeanObject,
    mut v_updateHeader_3934_: u8,
    mut v_toPure_3935_: *mut crate::leanh::LeanObject,
    mut v_args_3936_: *mut crate::leanh::LeanObject,
    mut v_inst_3937_: *mut crate::leanh::LeanObject,
    mut v___f_3938_: *mut crate::leanh::LeanObject,
    mut v_toBind_3939_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3944_: usize = 0;
    let mut v___x_3945_: usize = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = crate::leanh::lean_box((v_pu_3931_) as usize);
    v___x_3942_ = crate::leanh::lean_box((v_updateHeader_3934_) as usize);
    v___f_3943_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_3943_, 0, v___x_3941_);
    crate::leanh::lean_closure_set(v___f_3943_, 1, v_e_3932_);
    crate::leanh::lean_closure_set(v___f_3943_, 2, v_____do__lift_3940_);
    crate::leanh::lean_closure_set(v___f_3943_, 3, v_i_3933_);
    crate::leanh::lean_closure_set(v___f_3943_, 4, v___x_3942_);
    crate::leanh::lean_closure_set(v___f_3943_, 5, v_toPure_3935_);
    v_sz_3944_ = lean_array_size(v_args_3936_);
    v___x_3945_ = 0usize;
    v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_3937_,
        v___f_3938_,
        v_sz_3944_,
        v___x_3945_,
        v_args_3936_,
    );
    v___x_3947_ = crate::leanh::lean_apply_4(
        v_toBind_3939_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3946_,
        v___f_3943_,
    );
    return v___x_3947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed(
    mut v_pu_3948_: *mut crate::leanh::LeanObject,
    mut v_e_3949_: *mut crate::leanh::LeanObject,
    mut v_i_3950_: *mut crate::leanh::LeanObject,
    mut v_updateHeader_3951_: *mut crate::leanh::LeanObject,
    mut v_toPure_3952_: *mut crate::leanh::LeanObject,
    mut v_args_3953_: *mut crate::leanh::LeanObject,
    mut v_inst_3954_: *mut crate::leanh::LeanObject,
    mut v___f_3955_: *mut crate::leanh::LeanObject,
    mut v_toBind_3956_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3958_: u8 = 0;
    let mut v_updateHeader_642__boxed_3959_: u8 = 0;
    let mut v_res_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3958_ = (crate::leanh::lean_unbox(v_pu_3948_) as u8);
    v_updateHeader_642__boxed_3959_ = (crate::leanh::lean_unbox(v_updateHeader_3951_) as u8);
    v_res_3960_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4(
        v_pu_boxed_3958_,
        v_e_3949_,
        v_i_3950_,
        v_updateHeader_642__boxed_3959_,
        v_toPure_3952_,
        v_args_3953_,
        v_inst_3954_,
        v___f_3955_,
        v_toBind_3956_,
        v_____do__lift_3957_,
    );
    return v_res_3960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(
    mut v_pu_3961_: u8,
    mut v_e_3962_: *mut crate::leanh::LeanObject,
    mut v_ty_3963_: *mut crate::leanh::LeanObject,
    mut v_toPure_3964_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(
        v_pu_3961_,
        v_e_3962_,
        v_ty_3963_,
        v_____do__lift_3965_,
    );
    v___x_3967_ =
        crate::leanh::lean_apply_2(v_toPure_3964_, crate::leanh::lean_box(0), v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed(
    mut v_pu_3968_: *mut crate::leanh::LeanObject,
    mut v_e_3969_: *mut crate::leanh::LeanObject,
    mut v_ty_3970_: *mut crate::leanh::LeanObject,
    mut v_toPure_3971_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3973_ = (crate::leanh::lean_unbox(v_pu_3968_) as u8);
    v_res_3974_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6(
        v_pu_boxed_3973_,
        v_e_3969_,
        v_ty_3970_,
        v_toPure_3971_,
        v_____do__lift_3972_,
    );
    crate::leanh::lean_dec(v_e_3969_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(
    mut v_pu_3975_: u8,
    mut v_e_3976_: *mut crate::leanh::LeanObject,
    mut v_toPure_3977_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3979_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(
            v_pu_3975_,
            v_e_3976_,
            v_____do__lift_3978_,
        );
    v___x_3980_ =
        crate::leanh::lean_apply_2(v_toPure_3977_, crate::leanh::lean_box(0), v___x_3979_);
    return v___x_3980_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed(
    mut v_pu_3981_: *mut crate::leanh::LeanObject,
    mut v_e_3982_: *mut crate::leanh::LeanObject,
    mut v_toPure_3983_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3985_: u8 = 0;
    let mut v_res_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3985_ = (crate::leanh::lean_unbox(v_pu_3981_) as u8);
    v_res_3986_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9(
        v_pu_boxed_3985_,
        v_e_3982_,
        v_toPure_3983_,
        v_____do__lift_3984_,
    );
    return v_res_3986_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(
    mut v_pu_3987_: u8,
    mut v_e_3988_: *mut crate::leanh::LeanObject,
    mut v_toPure_3989_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3991_ =
        l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(
            v_pu_3987_,
            v_e_3988_,
            v_____do__lift_3990_,
        );
    v___x_3992_ =
        crate::leanh::lean_apply_2(v_toPure_3989_, crate::leanh::lean_box(0), v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed(
    mut v_pu_3993_: *mut crate::leanh::LeanObject,
    mut v_e_3994_: *mut crate::leanh::LeanObject,
    mut v_toPure_3995_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3997_: u8 = 0;
    let mut v_res_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3997_ = (crate::leanh::lean_unbox(v_pu_3993_) as u8);
    v_res_3998_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10(
        v_pu_boxed_3997_,
        v_e_3994_,
        v_toPure_3995_,
        v_____do__lift_3996_,
    );
    return v_res_3998_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
    mut v_pu_3999_: u8,
    mut v_inst_4000_: *mut crate::leanh::LeanObject,
    mut v_f_4001_: *mut crate::leanh::LeanObject,
    mut v_e_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4012_: usize = 0;
    let mut v___x_4013_: usize = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4026_: usize = 0;
    let mut v___x_4027_: usize = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4037_: usize = 0;
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_4056_: u8 = 0;
    let mut v_args_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4003_ = crate::leanh::lean_ctor_get(v_inst_4000_, 0);
                v_toBind_4004_ = crate::leanh::lean_ctor_get(v_inst_4000_, 1);
                crate::leanh::lean_inc(v_toBind_4004_);
                v_toPure_4005_ = crate::leanh::lean_ctor_get(v_toApplicative_4003_, 1);
                v___x_4006_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                crate::leanh::lean_inc(v_f_4001_);
                crate::leanh::lean_inc_ref(v_inst_4000_);
                v___f_4007_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4007_, 0, v___x_4006_);
                crate::leanh::lean_closure_set(v___f_4007_, 1, v_inst_4000_);
                crate::leanh::lean_closure_set(v___f_4007_, 2, v_f_4001_);
                v___x_4008_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                crate::leanh::lean_inc_n(v_toPure_4005_, 2);
                crate::leanh::lean_inc_n(v_e_4002_, 2);
                v___f_4009_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4009_, 0, v___x_4008_);
                crate::leanh::lean_closure_set(v___f_4009_, 1, v_e_4002_);
                crate::leanh::lean_closure_set(v___f_4009_, 2, v_toPure_4005_);
                v___x_4016_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                v___f_4017_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4017_, 0, v___x_4016_);
                crate::leanh::lean_closure_set(v___f_4017_, 1, v_e_4002_);
                crate::leanh::lean_closure_set(v___f_4017_, 2, v_toPure_4005_);
                match crate::leanh::lean_obj_tag(v_e_4002_) {
                    2 => {
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_struct_4022_ = crate::leanh::lean_ctor_get(v_e_4002_, 2);
                        crate::leanh::lean_inc(v_struct_4022_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 3);
                        v___x_4023_ = crate::leanh::lean_apply_1(v_f_4001_, v_struct_4022_);
                        v___x_4024_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4023_,
                            v___f_4017_,
                        );
                        return v___x_4024_;
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec(v_f_4001_);
                        v_args_4025_ = crate::leanh::lean_ctor_get(v_e_4002_, 2);
                        crate::leanh::lean_inc_ref(v_args_4025_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 3);
                        v_sz_4026_ = lean_array_size(v_args_4025_);
                        v___x_4027_ = 0usize;
                        v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_4000_,
                            v___f_4007_,
                            v_sz_4026_,
                            v___x_4027_,
                            v_args_4025_,
                        );
                        v___x_4029_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4028_,
                            v___f_4009_,
                        );
                        return v___x_4029_;
                    }
                    4 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        v_fvarId_4030_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc(v_fvarId_4030_);
                        v_args_4031_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc_ref(v_args_4031_);
                        v___x_4032_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        crate::leanh::lean_inc(v_toBind_4004_);
                        v___f_4033_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            8,
                            7,
                        );
                        crate::leanh::lean_closure_set(v___f_4033_, 0, v___x_4032_);
                        crate::leanh::lean_closure_set(v___f_4033_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4033_, 2, v_toPure_4005_);
                        crate::leanh::lean_closure_set(v___f_4033_, 3, v_args_4031_);
                        crate::leanh::lean_closure_set(v___f_4033_, 4, v_inst_4000_);
                        crate::leanh::lean_closure_set(v___f_4033_, 5, v___f_4007_);
                        crate::leanh::lean_closure_set(v___f_4033_, 6, v_toBind_4004_);
                        v___x_4034_ = crate::leanh::lean_apply_1(v_f_4001_, v_fvarId_4030_);
                        v___x_4035_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4034_,
                            v___f_4033_,
                        );
                        return v___x_4035_;
                    }
                    5 => {
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec(v_f_4001_);
                        v_args_4036_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc_ref(v_args_4036_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 2);
                        v_sz_4037_ = lean_array_size(v_args_4036_);
                        v___x_4038_ = 0usize;
                        v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_4000_,
                            v___f_4007_,
                            v_sz_4037_,
                            v___x_4038_,
                            v_args_4036_,
                        );
                        v___x_4040_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4039_,
                            v___f_4009_,
                        );
                        return v___x_4040_;
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_var_4041_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc(v_var_4041_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 2);
                        v_fvarId_4019_ = v_var_4041_;
                        state = 2;
                        continue;
                    }
                    7 => {
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_var_4042_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc(v_var_4042_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 2);
                        v_fvarId_4019_ = v_var_4042_;
                        state = 2;
                        continue;
                    }
                    8 => {
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_var_4043_ = crate::leanh::lean_ctor_get(v_e_4002_, 2);
                        crate::leanh::lean_inc(v_var_4043_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 3);
                        v___x_4044_ = crate::leanh::lean_apply_1(v_f_4001_, v_var_4043_);
                        v___x_4045_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4044_,
                            v___f_4017_,
                        );
                        return v___x_4045_;
                    }
                    9 => {
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec(v_f_4001_);
                        v_args_4046_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc_ref(v_args_4046_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 2);
                        v_args_4011_ = v_args_4046_;
                        state = 1;
                        continue;
                    }
                    10 => {
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec(v_f_4001_);
                        v_args_4047_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc_ref(v_args_4047_);
                        crate::leanh::lean_dec_ref_known(v_e_4002_, 2);
                        v_args_4011_ = v_args_4047_;
                        state = 1;
                        continue;
                    }
                    11 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_n_4048_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc(v_n_4048_);
                        v_var_4049_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc(v_var_4049_);
                        v___x_4050_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        v___f_4051_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__8___boxed
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_4051_, 0, v___x_4050_);
                        crate::leanh::lean_closure_set(v___f_4051_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4051_, 2, v_n_4048_);
                        crate::leanh::lean_closure_set(v___f_4051_, 3, v_toPure_4005_);
                        v___x_4052_ = crate::leanh::lean_apply_1(v_f_4001_, v_var_4049_);
                        v___x_4053_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4052_,
                            v___f_4051_,
                        );
                        return v___x_4053_;
                    }
                    12 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        v_var_4054_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc(v_var_4054_);
                        v_i_4055_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc_ref(v_i_4055_);
                        v_updateHeader_4056_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_4002_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_args_4057_ = crate::leanh::lean_ctor_get(v_e_4002_, 2);
                        crate::leanh::lean_inc_ref(v_args_4057_);
                        v___x_4058_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        v___x_4059_ = crate::leanh::lean_box((v_updateHeader_4056_) as usize);
                        crate::leanh::lean_inc(v_toBind_4004_);
                        v___f_4060_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__4___boxed
                                as *mut core::ffi::c_void,
                            10,
                            9,
                        );
                        crate::leanh::lean_closure_set(v___f_4060_, 0, v___x_4058_);
                        crate::leanh::lean_closure_set(v___f_4060_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4060_, 2, v_i_4055_);
                        crate::leanh::lean_closure_set(v___f_4060_, 3, v___x_4059_);
                        crate::leanh::lean_closure_set(v___f_4060_, 4, v_toPure_4005_);
                        crate::leanh::lean_closure_set(v___f_4060_, 5, v_args_4057_);
                        crate::leanh::lean_closure_set(v___f_4060_, 6, v_inst_4000_);
                        crate::leanh::lean_closure_set(v___f_4060_, 7, v___f_4007_);
                        crate::leanh::lean_closure_set(v___f_4060_, 8, v_toBind_4004_);
                        v___x_4061_ = crate::leanh::lean_apply_1(v_f_4001_, v_var_4054_);
                        v___x_4062_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4061_,
                            v___f_4060_,
                        );
                        return v___x_4062_;
                    }
                    13 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_ty_4063_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc_ref(v_ty_4063_);
                        v_fvarId_4064_ = crate::leanh::lean_ctor_get(v_e_4002_, 1);
                        crate::leanh::lean_inc(v_fvarId_4064_);
                        v___x_4065_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        v___f_4066_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__6___boxed
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_4066_, 0, v___x_4065_);
                        crate::leanh::lean_closure_set(v___f_4066_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4066_, 2, v_ty_4063_);
                        crate::leanh::lean_closure_set(v___f_4066_, 3, v_toPure_4005_);
                        v___x_4067_ = crate::leanh::lean_apply_1(v_f_4001_, v_fvarId_4064_);
                        v___x_4068_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4067_,
                            v___f_4066_,
                        );
                        return v___x_4068_;
                    }
                    14 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_fvarId_4069_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc(v_fvarId_4069_);
                        v___x_4070_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        v___f_4071_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__9___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_4071_, 0, v___x_4070_);
                        crate::leanh::lean_closure_set(v___f_4071_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4071_, 2, v_toPure_4005_);
                        v___x_4072_ = crate::leanh::lean_apply_1(v_f_4001_, v_fvarId_4069_);
                        v___x_4073_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4072_,
                            v___f_4071_,
                        );
                        return v___x_4073_;
                    }
                    15 => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v_fvarId_4074_ = crate::leanh::lean_ctor_get(v_e_4002_, 0);
                        crate::leanh::lean_inc(v_fvarId_4074_);
                        v___x_4075_ = crate::leanh::lean_box((v_pu_3999_) as usize);
                        v___f_4076_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___lam__10___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_4076_, 0, v___x_4075_);
                        crate::leanh::lean_closure_set(v___f_4076_, 1, v_e_4002_);
                        crate::leanh::lean_closure_set(v___f_4076_, 2, v_toPure_4005_);
                        v___x_4077_ = crate::leanh::lean_apply_1(v_f_4001_, v_fvarId_4074_);
                        v___x_4078_ = crate::leanh::lean_apply_4(
                            v_toBind_4004_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4077_,
                            v___f_4076_,
                        );
                        return v___x_4078_;
                    }
                    _ => {
                        crate::leanh::lean_inc(v_toPure_4005_);
                        crate::leanh::lean_dec_ref(v___f_4017_);
                        crate::leanh::lean_dec_ref(v___f_4009_);
                        crate::leanh::lean_dec_ref(v___f_4007_);
                        crate::leanh::lean_dec(v_toBind_4004_);
                        crate::leanh::lean_dec(v_f_4001_);
                        crate::leanh::lean_dec_ref(v_inst_4000_);
                        v___x_4079_ = crate::leanh::lean_apply_2(
                            v_toPure_4005_,
                            crate::leanh::lean_box(0),
                            v_e_4002_,
                        );
                        return v___x_4079_;
                    }
                }
            }
            1 => {
                v_sz_4012_ = lean_array_size(v_args_4011_);
                v___x_4013_ = 0usize;
                v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4000_,
                    v___f_4007_,
                    v_sz_4012_,
                    v___x_4013_,
                    v_args_4011_,
                );
                v___x_4015_ = crate::leanh::lean_apply_4(
                    v_toBind_4004_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4014_,
                    v___f_4009_,
                );
                return v___x_4015_;
            }
            2 => {
                v___x_4020_ = crate::leanh::lean_apply_1(v_f_4001_, v_fvarId_4019_);
                v___x_4021_ = crate::leanh::lean_apply_4(
                    v_toBind_4004_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4020_,
                    v___f_4017_,
                );
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg___boxed(
    mut v_pu_4080_: *mut crate::leanh::LeanObject,
    mut v_inst_4081_: *mut crate::leanh::LeanObject,
    mut v_f_4082_: *mut crate::leanh::LeanObject,
    mut v_e_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4084_: u8 = 0;
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4084_ = (crate::leanh::lean_unbox(v_pu_4080_) as u8);
    v_res_4085_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_boxed_4084_,
        v_inst_4081_,
        v_f_4082_,
        v_e_4083_,
    );
    return v_res_4085_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM(
    mut v_m_4086_: *mut crate::leanh::LeanObject,
    mut v_pu_4087_: u8,
    mut v_inst_4088_: *mut crate::leanh::LeanObject,
    mut v_inst_4089_: *mut crate::leanh::LeanObject,
    mut v_f_4090_: *mut crate::leanh::LeanObject,
    mut v_e_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4087_,
        v_inst_4089_,
        v_f_4090_,
        v_e_4091_,
    );
    return v___x_4092_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_mapFVarM___boxed(
    mut v_m_4093_: *mut crate::leanh::LeanObject,
    mut v_pu_4094_: *mut crate::leanh::LeanObject,
    mut v_inst_4095_: *mut crate::leanh::LeanObject,
    mut v_inst_4096_: *mut crate::leanh::LeanObject,
    mut v_f_4097_: *mut crate::leanh::LeanObject,
    mut v_e_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4099_: u8 = 0;
    let mut v_res_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4099_ = (crate::leanh::lean_unbox(v_pu_4094_) as u8);
    v_res_4100_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM(
        v_m_4093_,
        v_pu_boxed_4099_,
        v_inst_4095_,
        v_inst_4096_,
        v_f_4097_,
        v_e_4098_,
    );
    crate::leanh::lean_dec(v_inst_4095_);
    return v_res_4100_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0(
    mut v_inst_4101_: *mut crate::leanh::LeanObject,
    mut v_f_4102_: *mut crate::leanh::LeanObject,
    mut v_x_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_4101_, v_f_4102_, v___y_4104_);
    return v___x_4105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3(
    mut v_args_4106_: *mut crate::leanh::LeanObject,
    mut v_toPure_4107_: *mut crate::leanh::LeanObject,
    mut v_inst_4108_: *mut crate::leanh::LeanObject,
    mut v___f_4109_: *mut crate::leanh::LeanObject,
    mut v_____r_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    v___x_4111_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4112_ = lean_array_get_size(v_args_4106_);
    v___x_4113_ = crate::leanh::lean_box(0);
    v___x_4114_ = lean_nat_dec_lt(v___x_4111_, v___x_4112_);
    if v___x_4114_ == 0 {
        let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_4109_);
        crate::leanh::lean_dec_ref(v_inst_4108_);
        crate::leanh::lean_dec_ref(v_args_4106_);
        v___x_4115_ =
            crate::leanh::lean_apply_2(v_toPure_4107_, crate::leanh::lean_box(0), v___x_4113_);
        return v___x_4115_;
    } else {
        let mut v___x_4116_: u8 = 0;
        v___x_4116_ = lean_nat_dec_le(v___x_4112_, v___x_4112_);
        if v___x_4116_ == 0 {
            if v___x_4114_ == 0 {
                let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___f_4109_);
                crate::leanh::lean_dec_ref(v_inst_4108_);
                crate::leanh::lean_dec_ref(v_args_4106_);
                v___x_4117_ = crate::leanh::lean_apply_2(
                    v_toPure_4107_,
                    crate::leanh::lean_box(0),
                    v___x_4113_,
                );
                return v___x_4117_;
            } else {
                let mut v___x_4118_: usize = 0;
                let mut v___x_4119_: usize = 0;
                let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_toPure_4107_);
                v___x_4118_ = 0usize;
                v___x_4119_ = lean_usize_of_nat(v___x_4112_);
                v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4108_,
                    v___f_4109_,
                    v_args_4106_,
                    v___x_4118_,
                    v___x_4119_,
                    v___x_4113_,
                );
                return v___x_4120_;
            }
        } else {
            let mut v___x_4121_: usize = 0;
            let mut v___x_4122_: usize = 0;
            let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_4107_);
            v___x_4121_ = 0usize;
            v___x_4122_ = lean_usize_of_nat(v___x_4112_);
            v___x_4123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4108_,
                v___f_4109_,
                v_args_4106_,
                v___x_4121_,
                v___x_4122_,
                v___x_4113_,
            );
            return v___x_4123_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(
    mut v_inst_4124_: *mut crate::leanh::LeanObject,
    mut v_f_4125_: *mut crate::leanh::LeanObject,
    mut v_e_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: usize = 0;
    let mut v___x_4141_: usize = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: usize = 0;
    let mut v___x_4157_: usize = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: usize = 0;
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: u8 = 0;
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: usize = 0;
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: usize = 0;
    let mut v___x_4179_: usize = 0;
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4127_ = crate::leanh::lean_ctor_get(v_inst_4124_, 0);
                v_toBind_4128_ = crate::leanh::lean_ctor_get(v_inst_4124_, 1);
                v_toPure_4129_ = crate::leanh::lean_ctor_get(v_toApplicative_4127_, 1);
                crate::leanh::lean_inc(v_f_4125_);
                crate::leanh::lean_inc_ref(v_inst_4124_);
                v___f_4130_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4130_, 0, v_inst_4124_);
                crate::leanh::lean_closure_set(v___f_4130_, 1, v_f_4125_);
                match crate::leanh::lean_obj_tag(v_e_4126_) {
                    2 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_struct_4146_ = crate::leanh::lean_ctor_get(v_e_4126_, 2);
                        crate::leanh::lean_inc(v_struct_4146_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4147_ = crate::leanh::lean_apply_1(v_f_4125_, v_struct_4146_);
                        return v___x_4147_;
                    }
                    3 => {
                        crate::leanh::lean_dec(v_f_4125_);
                        v_args_4148_ = crate::leanh::lean_ctor_get(v_e_4126_, 2);
                        crate::leanh::lean_inc_ref(v_args_4148_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4149_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4150_ = lean_array_get_size(v_args_4148_);
                        v___x_4151_ = crate::leanh::lean_box(0);
                        v___x_4152_ = lean_nat_dec_lt(v___x_4149_, v___x_4150_);
                        if v___x_4152_ == 0 {
                            crate::leanh::lean_inc(v_toPure_4129_);
                            crate::leanh::lean_dec_ref(v_args_4148_);
                            crate::leanh::lean_dec_ref(v___f_4130_);
                            crate::leanh::lean_dec_ref(v_inst_4124_);
                            v___x_4153_ = crate::leanh::lean_apply_2(
                                v_toPure_4129_,
                                crate::leanh::lean_box(0),
                                v___x_4151_,
                            );
                            return v___x_4153_;
                        } else {
                            v___x_4154_ = lean_nat_dec_le(v___x_4150_, v___x_4150_);
                            if v___x_4154_ == 0 {
                                if v___x_4152_ == 0 {
                                    crate::leanh::lean_inc(v_toPure_4129_);
                                    crate::leanh::lean_dec_ref(v_args_4148_);
                                    crate::leanh::lean_dec_ref(v___f_4130_);
                                    crate::leanh::lean_dec_ref(v_inst_4124_);
                                    v___x_4155_ = crate::leanh::lean_apply_2(
                                        v_toPure_4129_,
                                        crate::leanh::lean_box(0),
                                        v___x_4151_,
                                    );
                                    return v___x_4155_;
                                } else {
                                    v___x_4156_ = 0usize;
                                    v___x_4157_ = lean_usize_of_nat(v___x_4150_);
                                    v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_4124_, v___f_4130_, v_args_4148_, v___x_4156_, v___x_4157_, v___x_4151_);
                                    return v___x_4158_;
                                }
                            } else {
                                v___x_4159_ = 0usize;
                                v___x_4160_ = lean_usize_of_nat(v___x_4150_);
                                v___x_4161_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v_inst_4124_,
                                        v___f_4130_,
                                        v_args_4148_,
                                        v___x_4159_,
                                        v___x_4160_,
                                        v___x_4151_,
                                    );
                                return v___x_4161_;
                            }
                        }
                    }
                    4 => {
                        crate::leanh::lean_inc(v_toPure_4129_);
                        crate::leanh::lean_inc(v_toBind_4128_);
                        v_fvarId_4162_ = crate::leanh::lean_ctor_get(v_e_4126_, 0);
                        crate::leanh::lean_inc(v_fvarId_4162_);
                        v_args_4163_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc_ref(v_args_4163_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___f_4164_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_4164_, 0, v_args_4163_);
                        crate::leanh::lean_closure_set(v___f_4164_, 1, v_toPure_4129_);
                        crate::leanh::lean_closure_set(v___f_4164_, 2, v_inst_4124_);
                        crate::leanh::lean_closure_set(v___f_4164_, 3, v___f_4130_);
                        v___x_4165_ = crate::leanh::lean_apply_1(v_f_4125_, v_fvarId_4162_);
                        v___x_4166_ = crate::leanh::lean_apply_4(
                            v_toBind_4128_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4165_,
                            v___f_4164_,
                        );
                        return v___x_4166_;
                    }
                    5 => {
                        crate::leanh::lean_dec(v_f_4125_);
                        v_args_4167_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc_ref(v_args_4167_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4168_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4169_ = lean_array_get_size(v_args_4167_);
                        v___x_4170_ = crate::leanh::lean_box(0);
                        v___x_4171_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
                        if v___x_4171_ == 0 {
                            crate::leanh::lean_inc(v_toPure_4129_);
                            crate::leanh::lean_dec_ref(v_args_4167_);
                            crate::leanh::lean_dec_ref(v___f_4130_);
                            crate::leanh::lean_dec_ref(v_inst_4124_);
                            v___x_4172_ = crate::leanh::lean_apply_2(
                                v_toPure_4129_,
                                crate::leanh::lean_box(0),
                                v___x_4170_,
                            );
                            return v___x_4172_;
                        } else {
                            v___x_4173_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
                            if v___x_4173_ == 0 {
                                if v___x_4171_ == 0 {
                                    crate::leanh::lean_inc(v_toPure_4129_);
                                    crate::leanh::lean_dec_ref(v_args_4167_);
                                    crate::leanh::lean_dec_ref(v___f_4130_);
                                    crate::leanh::lean_dec_ref(v_inst_4124_);
                                    v___x_4174_ = crate::leanh::lean_apply_2(
                                        v_toPure_4129_,
                                        crate::leanh::lean_box(0),
                                        v___x_4170_,
                                    );
                                    return v___x_4174_;
                                } else {
                                    v___x_4175_ = 0usize;
                                    v___x_4176_ = lean_usize_of_nat(v___x_4169_);
                                    v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v_inst_4124_, v___f_4130_, v_args_4167_, v___x_4175_, v___x_4176_, v___x_4170_);
                                    return v___x_4177_;
                                }
                            } else {
                                v___x_4178_ = 0usize;
                                v___x_4179_ = lean_usize_of_nat(v___x_4169_);
                                v___x_4180_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v_inst_4124_,
                                        v___f_4130_,
                                        v_args_4167_,
                                        v___x_4178_,
                                        v___x_4179_,
                                        v___x_4170_,
                                    );
                                return v___x_4180_;
                            }
                        }
                    }
                    6 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_var_4181_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc(v_var_4181_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4182_ = crate::leanh::lean_apply_1(v_f_4125_, v_var_4181_);
                        return v___x_4182_;
                    }
                    7 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_var_4183_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc(v_var_4183_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4184_ = crate::leanh::lean_apply_1(v_f_4125_, v_var_4183_);
                        return v___x_4184_;
                    }
                    8 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_var_4185_ = crate::leanh::lean_ctor_get(v_e_4126_, 2);
                        crate::leanh::lean_inc(v_var_4185_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 3);
                        v___x_4186_ = crate::leanh::lean_apply_1(v_f_4125_, v_var_4185_);
                        return v___x_4186_;
                    }
                    9 => {
                        crate::leanh::lean_dec(v_f_4125_);
                        v_args_4187_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc_ref(v_args_4187_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v_args_4132_ = v_args_4187_;
                        state = 1;
                        continue;
                    }
                    10 => {
                        crate::leanh::lean_dec(v_f_4125_);
                        v_args_4188_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc_ref(v_args_4188_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v_args_4132_ = v_args_4188_;
                        state = 1;
                        continue;
                    }
                    11 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_var_4189_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc(v_var_4189_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4190_ = crate::leanh::lean_apply_1(v_f_4125_, v_var_4189_);
                        return v___x_4190_;
                    }
                    12 => {
                        crate::leanh::lean_inc(v_toPure_4129_);
                        crate::leanh::lean_inc(v_toBind_4128_);
                        v_var_4191_ = crate::leanh::lean_ctor_get(v_e_4126_, 0);
                        crate::leanh::lean_inc(v_var_4191_);
                        v_args_4192_ = crate::leanh::lean_ctor_get(v_e_4126_, 2);
                        crate::leanh::lean_inc_ref(v_args_4192_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 3);
                        v___f_4193_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg___lam__3
                                as *mut core::ffi::c_void,
                            5,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_4193_, 0, v_args_4192_);
                        crate::leanh::lean_closure_set(v___f_4193_, 1, v_toPure_4129_);
                        crate::leanh::lean_closure_set(v___f_4193_, 2, v_inst_4124_);
                        crate::leanh::lean_closure_set(v___f_4193_, 3, v___f_4130_);
                        v___x_4194_ = crate::leanh::lean_apply_1(v_f_4125_, v_var_4191_);
                        v___x_4195_ = crate::leanh::lean_apply_4(
                            v_toBind_4128_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4194_,
                            v___f_4193_,
                        );
                        return v___x_4195_;
                    }
                    13 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_fvarId_4196_ = crate::leanh::lean_ctor_get(v_e_4126_, 1);
                        crate::leanh::lean_inc(v_fvarId_4196_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 2);
                        v___x_4197_ = crate::leanh::lean_apply_1(v_f_4125_, v_fvarId_4196_);
                        return v___x_4197_;
                    }
                    14 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_fvarId_4198_ = crate::leanh::lean_ctor_get(v_e_4126_, 0);
                        crate::leanh::lean_inc(v_fvarId_4198_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 1);
                        v___x_4199_ = crate::leanh::lean_apply_1(v_f_4125_, v_fvarId_4198_);
                        return v___x_4199_;
                    }
                    15 => {
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v_fvarId_4200_ = crate::leanh::lean_ctor_get(v_e_4126_, 0);
                        crate::leanh::lean_inc(v_fvarId_4200_);
                        crate::leanh::lean_dec_ref_known(v_e_4126_, 1);
                        v___x_4201_ = crate::leanh::lean_apply_1(v_f_4125_, v_fvarId_4200_);
                        return v___x_4201_;
                    }
                    _ => {
                        crate::leanh::lean_inc(v_toPure_4129_);
                        crate::leanh::lean_dec_ref(v___f_4130_);
                        crate::leanh::lean_dec(v_e_4126_);
                        crate::leanh::lean_dec(v_f_4125_);
                        crate::leanh::lean_dec_ref(v_inst_4124_);
                        v___x_4202_ = crate::leanh::lean_box(0);
                        v___x_4203_ = crate::leanh::lean_apply_2(
                            v_toPure_4129_,
                            crate::leanh::lean_box(0),
                            v___x_4202_,
                        );
                        return v___x_4203_;
                    }
                }
            }
            1 => {
                v___x_4133_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4134_ = lean_array_get_size(v_args_4132_);
                v___x_4135_ = crate::leanh::lean_box(0);
                v___x_4136_ = lean_nat_dec_lt(v___x_4133_, v___x_4134_);
                if v___x_4136_ == 0 {
                    crate::leanh::lean_inc(v_toPure_4129_);
                    crate::leanh::lean_dec_ref(v_args_4132_);
                    crate::leanh::lean_dec_ref(v___f_4130_);
                    crate::leanh::lean_dec_ref(v_inst_4124_);
                    v___x_4137_ = crate::leanh::lean_apply_2(
                        v_toPure_4129_,
                        crate::leanh::lean_box(0),
                        v___x_4135_,
                    );
                    return v___x_4137_;
                } else {
                    v___x_4138_ = lean_nat_dec_le(v___x_4134_, v___x_4134_);
                    if v___x_4138_ == 0 {
                        if v___x_4136_ == 0 {
                            crate::leanh::lean_inc(v_toPure_4129_);
                            crate::leanh::lean_dec_ref(v_args_4132_);
                            crate::leanh::lean_dec_ref(v___f_4130_);
                            crate::leanh::lean_dec_ref(v_inst_4124_);
                            v___x_4139_ = crate::leanh::lean_apply_2(
                                v_toPure_4129_,
                                crate::leanh::lean_box(0),
                                v___x_4135_,
                            );
                            return v___x_4139_;
                        } else {
                            v___x_4140_ = 0usize;
                            v___x_4141_ = lean_usize_of_nat(v___x_4134_);
                            v___x_4142_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v_inst_4124_,
                                    v___f_4130_,
                                    v_args_4132_,
                                    v___x_4140_,
                                    v___x_4141_,
                                    v___x_4135_,
                                );
                            return v___x_4142_;
                        }
                    } else {
                        v___x_4143_ = 0usize;
                        v___x_4144_ = lean_usize_of_nat(v___x_4134_);
                        v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_4124_,
                            v___f_4130_,
                            v_args_4132_,
                            v___x_4143_,
                            v___x_4144_,
                            v___x_4135_,
                        );
                        return v___x_4145_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM(
    mut v_m_4204_: *mut crate::leanh::LeanObject,
    mut v_pu_4205_: u8,
    mut v_inst_4206_: *mut crate::leanh::LeanObject,
    mut v_f_4207_: *mut crate::leanh::LeanObject,
    mut v_e_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4206_, v_f_4207_, v_e_4208_);
    return v___x_4209_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___boxed(
    mut v_m_4210_: *mut crate::leanh::LeanObject,
    mut v_pu_4211_: *mut crate::leanh::LeanObject,
    mut v_inst_4212_: *mut crate::leanh::LeanObject,
    mut v_f_4213_: *mut crate::leanh::LeanObject,
    mut v_e_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4215_ = (crate::leanh::lean_unbox(v_pu_4211_) as u8);
    v_res_4216_ = l_Lean_Compiler_LCNF_LetValue_forFVarM(
        v_m_4210_,
        v_pu_boxed_4215_,
        v_inst_4212_,
        v_f_4213_,
        v_e_4214_,
    );
    return v_res_4216_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(
    mut v_pu_4217_: u8,
    mut v_m_4218_: *mut crate::leanh::LeanObject,
    mut v_inst_4219_: *mut crate::leanh::LeanObject,
    mut v_inst_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4223_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4217_,
        v_inst_4220_,
        v___y_4221_,
        v___y_4222_,
    );
    return v___x_4223_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed(
    mut v_pu_4224_: *mut crate::leanh::LeanObject,
    mut v_m_4225_: *mut crate::leanh::LeanObject,
    mut v_inst_4226_: *mut crate::leanh::LeanObject,
    mut v_inst_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
    mut v___y_4229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4230_: u8 = 0;
    let mut v_res_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4230_ = (crate::leanh::lean_unbox(v_pu_4224_) as u8);
    v_res_4231_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0(
        v_pu_boxed_4230_,
        v_m_4225_,
        v_inst_4226_,
        v_inst_4227_,
        v___y_4228_,
        v___y_4229_,
    );
    crate::leanh::lean_dec(v_inst_4226_);
    return v_res_4231_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__1(
    mut v_m_4232_: *mut crate::leanh::LeanObject,
    mut v_inst_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4236_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4233_, v___y_4234_, v___y_4235_);
    return v___x_4236_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue(
    mut v_pu_4238_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4239_ = crate::leanh::lean_box((v_pu_4238_) as usize);
    v___f_4240_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarLetValue___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4240_, 0, v___x_4239_);
    v___f_4241_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue___closed__0;
    v___x_4242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4242_, 0, v___f_4240_);
    crate::leanh::lean_ctor_set(v___x_4242_, 1, v___f_4241_);
    return v___x_4242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetValue___boxed(
    mut v_pu_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4244_: u8 = 0;
    let mut v_res_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4244_ = (crate::leanh::lean_unbox(v_pu_4243_) as u8);
    v_res_4245_ = l_Lean_Compiler_LCNF_instTraverseFVarLetValue(v_pu_boxed_4244_);
    return v_res_4245_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(
    mut v_pu_4246_: u8,
    mut v_decl_4247_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4248_: *mut crate::leanh::LeanObject,
    mut v_inst_4249_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = crate::leanh::lean_box((v_pu_4246_) as usize);
    v___x_4252_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_4252_, 0, v___x_4251_);
    crate::leanh::lean_closure_set(v___x_4252_, 1, v_decl_4247_);
    crate::leanh::lean_closure_set(v___x_4252_, 2, v_____do__lift_4248_);
    crate::leanh::lean_closure_set(v___x_4252_, 3, v_____do__lift_4250_);
    v___x_4253_ = crate::leanh::lean_apply_2(v_inst_4249_, crate::leanh::lean_box(0), v___x_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_4254_: *mut crate::leanh::LeanObject,
    mut v_decl_4255_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4256_: *mut crate::leanh::LeanObject,
    mut v_inst_4257_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4259_: u8 = 0;
    let mut v_res_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4259_ = (crate::leanh::lean_unbox(v_pu_4254_) as u8);
    v_res_4260_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0(
        v_pu_boxed_4259_,
        v_decl_4255_,
        v_____do__lift_4256_,
        v_inst_4257_,
        v_____do__lift_4258_,
    );
    return v_res_4260_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(
    mut v_pu_4261_: u8,
    mut v_decl_4262_: *mut crate::leanh::LeanObject,
    mut v_inst_4263_: *mut crate::leanh::LeanObject,
    mut v_inst_4264_: *mut crate::leanh::LeanObject,
    mut v_f_4265_: *mut crate::leanh::LeanObject,
    mut v_value_4266_: *mut crate::leanh::LeanObject,
    mut v_toBind_4267_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = crate::leanh::lean_box((v_pu_4261_) as usize);
    v___f_4270_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4270_, 0, v___x_4269_);
    crate::leanh::lean_closure_set(v___f_4270_, 1, v_decl_4262_);
    crate::leanh::lean_closure_set(v___f_4270_, 2, v_____do__lift_4268_);
    crate::leanh::lean_closure_set(v___f_4270_, 3, v_inst_4263_);
    v___x_4271_ = l_Lean_Compiler_LCNF_LetValue_mapFVarM___redArg(
        v_pu_4261_,
        v_inst_4264_,
        v_f_4265_,
        v_value_4266_,
    );
    v___x_4272_ = crate::leanh::lean_apply_4(
        v_toBind_4267_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4271_,
        v___f_4270_,
    );
    return v___x_4272_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_4273_: *mut crate::leanh::LeanObject,
    mut v_decl_4274_: *mut crate::leanh::LeanObject,
    mut v_inst_4275_: *mut crate::leanh::LeanObject,
    mut v_inst_4276_: *mut crate::leanh::LeanObject,
    mut v_f_4277_: *mut crate::leanh::LeanObject,
    mut v_value_4278_: *mut crate::leanh::LeanObject,
    mut v_toBind_4279_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4281_: u8 = 0;
    let mut v_res_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4281_ = (crate::leanh::lean_unbox(v_pu_4273_) as u8);
    v_res_4282_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1(
        v_pu_boxed_4281_,
        v_decl_4274_,
        v_inst_4275_,
        v_inst_4276_,
        v_f_4277_,
        v_value_4278_,
        v_toBind_4279_,
        v_____do__lift_4280_,
    );
    return v_res_4282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
    mut v_pu_4283_: u8,
    mut v_inst_4284_: *mut crate::leanh::LeanObject,
    mut v_inst_4285_: *mut crate::leanh::LeanObject,
    mut v_f_4286_: *mut crate::leanh::LeanObject,
    mut v_decl_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4288_ = crate::leanh::lean_ctor_get(v_inst_4285_, 1);
    crate::leanh::lean_inc_n(v_toBind_4288_, 2);
    v_type_4289_ = crate::leanh::lean_ctor_get(v_decl_4287_, 2);
    crate::leanh::lean_inc_ref(v_type_4289_);
    v_value_4290_ = crate::leanh::lean_ctor_get(v_decl_4287_, 3);
    crate::leanh::lean_inc(v_value_4290_);
    v___x_4291_ = crate::leanh::lean_box((v_pu_4283_) as usize);
    crate::leanh::lean_inc(v_f_4286_);
    crate::leanh::lean_inc_ref(v_inst_4285_);
    v___f_4292_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4292_, 0, v___x_4291_);
    crate::leanh::lean_closure_set(v___f_4292_, 1, v_decl_4287_);
    crate::leanh::lean_closure_set(v___f_4292_, 2, v_inst_4284_);
    crate::leanh::lean_closure_set(v___f_4292_, 3, v_inst_4285_);
    crate::leanh::lean_closure_set(v___f_4292_, 4, v_f_4286_);
    crate::leanh::lean_closure_set(v___f_4292_, 5, v_value_4290_);
    crate::leanh::lean_closure_set(v___f_4292_, 6, v_toBind_4288_);
    v___x_4293_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_4285_, v_f_4286_, v_type_4289_);
    v___x_4294_ = crate::leanh::lean_apply_4(
        v_toBind_4288_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4293_,
        v___f_4292_,
    );
    return v___x_4294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg___boxed(
    mut v_pu_4295_: *mut crate::leanh::LeanObject,
    mut v_inst_4296_: *mut crate::leanh::LeanObject,
    mut v_inst_4297_: *mut crate::leanh::LeanObject,
    mut v_f_4298_: *mut crate::leanh::LeanObject,
    mut v_decl_4299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4300_: u8 = 0;
    let mut v_res_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4300_ = (crate::leanh::lean_unbox(v_pu_4295_) as u8);
    v_res_4301_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_boxed_4300_,
        v_inst_4296_,
        v_inst_4297_,
        v_f_4298_,
        v_decl_4299_,
    );
    return v_res_4301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM(
    mut v_m_4302_: *mut crate::leanh::LeanObject,
    mut v_pu_4303_: u8,
    mut v_inst_4304_: *mut crate::leanh::LeanObject,
    mut v_inst_4305_: *mut crate::leanh::LeanObject,
    mut v_f_4306_: *mut crate::leanh::LeanObject,
    mut v_decl_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_4303_,
        v_inst_4304_,
        v_inst_4305_,
        v_f_4306_,
        v_decl_4307_,
    );
    return v___x_4308_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_mapFVarM___boxed(
    mut v_m_4309_: *mut crate::leanh::LeanObject,
    mut v_pu_4310_: *mut crate::leanh::LeanObject,
    mut v_inst_4311_: *mut crate::leanh::LeanObject,
    mut v_inst_4312_: *mut crate::leanh::LeanObject,
    mut v_f_4313_: *mut crate::leanh::LeanObject,
    mut v_decl_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4315_: u8 = 0;
    let mut v_res_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4315_ = (crate::leanh::lean_unbox(v_pu_4310_) as u8);
    v_res_4316_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM(
        v_m_4309_,
        v_pu_boxed_4315_,
        v_inst_4311_,
        v_inst_4312_,
        v_f_4313_,
        v_decl_4314_,
    );
    return v_res_4316_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0(
    mut v_inst_4317_: *mut crate::leanh::LeanObject,
    mut v_f_4318_: *mut crate::leanh::LeanObject,
    mut v_value_4319_: *mut crate::leanh::LeanObject,
    mut v_____r_4320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ =
        l_Lean_Compiler_LCNF_LetValue_forFVarM___redArg(v_inst_4317_, v_f_4318_, v_value_4319_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
    mut v_inst_4322_: *mut crate::leanh::LeanObject,
    mut v_f_4323_: *mut crate::leanh::LeanObject,
    mut v_decl_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4325_ = crate::leanh::lean_ctor_get(v_inst_4322_, 1);
    crate::leanh::lean_inc(v_toBind_4325_);
    v_type_4326_ = crate::leanh::lean_ctor_get(v_decl_4324_, 2);
    crate::leanh::lean_inc_ref(v_type_4326_);
    v_value_4327_ = crate::leanh::lean_ctor_get(v_decl_4324_, 3);
    crate::leanh::lean_inc(v_value_4327_);
    crate::leanh::lean_dec_ref(v_decl_4324_);
    crate::leanh::lean_inc(v_f_4323_);
    crate::leanh::lean_inc_ref(v_inst_4322_);
    v___f_4328_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4328_, 0, v_inst_4322_);
    crate::leanh::lean_closure_set(v___f_4328_, 1, v_f_4323_);
    crate::leanh::lean_closure_set(v___f_4328_, 2, v_value_4327_);
    v___x_4329_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_4322_, v_f_4323_, v_type_4326_);
    v___x_4330_ = crate::leanh::lean_apply_4(
        v_toBind_4325_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4329_,
        v___f_4328_,
    );
    return v___x_4330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM(
    mut v_m_4331_: *mut crate::leanh::LeanObject,
    mut v_pu_4332_: u8,
    mut v_inst_4333_: *mut crate::leanh::LeanObject,
    mut v_f_4334_: *mut crate::leanh::LeanObject,
    mut v_decl_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ =
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_4333_, v_f_4334_, v_decl_4335_);
    return v___x_4336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___boxed(
    mut v_m_4337_: *mut crate::leanh::LeanObject,
    mut v_pu_4338_: *mut crate::leanh::LeanObject,
    mut v_inst_4339_: *mut crate::leanh::LeanObject,
    mut v_f_4340_: *mut crate::leanh::LeanObject,
    mut v_decl_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4342_: u8 = 0;
    let mut v_res_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4342_ = (crate::leanh::lean_unbox(v_pu_4338_) as u8);
    v_res_4343_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM(
        v_m_4337_,
        v_pu_boxed_4342_,
        v_inst_4339_,
        v_f_4340_,
        v_decl_4341_,
    );
    return v_res_4343_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(
    mut v_pu_4344_: u8,
    mut v_m_4345_: *mut crate::leanh::LeanObject,
    mut v_inst_4346_: *mut crate::leanh::LeanObject,
    mut v_inst_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
        v_pu_4344_,
        v_inst_4346_,
        v_inst_4347_,
        v___y_4348_,
        v___y_4349_,
    );
    return v___x_4350_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed(
    mut v_pu_4351_: *mut crate::leanh::LeanObject,
    mut v_m_4352_: *mut crate::leanh::LeanObject,
    mut v_inst_4353_: *mut crate::leanh::LeanObject,
    mut v_inst_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4357_: u8 = 0;
    let mut v_res_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4357_ = (crate::leanh::lean_unbox(v_pu_4351_) as u8);
    v_res_4358_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0(
        v_pu_boxed_4357_,
        v_m_4352_,
        v_inst_4353_,
        v_inst_4354_,
        v___y_4355_,
        v___y_4356_,
    );
    return v_res_4358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__1(
    mut v_m_4359_: *mut crate::leanh::LeanObject,
    mut v_inst_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ =
        l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(v_inst_4360_, v___y_4361_, v___y_4362_);
    return v___x_4363_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(
    mut v_pu_4365_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4366_ = crate::leanh::lean_box((v_pu_4365_) as usize);
    v___f_4367_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4367_, 0, v___x_4366_);
    v___f_4368_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___closed__0;
    v___x_4369_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4369_, 0, v___f_4367_);
    crate::leanh::lean_ctor_set(v___x_4369_, 1, v___f_4368_);
    return v___x_4369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarLetDecl___boxed(
    mut v_pu_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4371_: u8 = 0;
    let mut v_res_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4371_ = (crate::leanh::lean_unbox(v_pu_4370_) as u8);
    v_res_4372_ = l_Lean_Compiler_LCNF_instTraverseFVarLetDecl(v_pu_boxed_4371_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(
    mut v_pu_4373_: u8,
    mut v_param_4374_: *mut crate::leanh::LeanObject,
    mut v_inst_4375_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = crate::leanh::lean_box((v_pu_4373_) as usize);
    v___x_4378_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4378_, 0, v___x_4377_);
    crate::leanh::lean_closure_set(v___x_4378_, 1, v_param_4374_);
    crate::leanh::lean_closure_set(v___x_4378_, 2, v_____do__lift_4376_);
    v___x_4379_ = crate::leanh::lean_apply_2(v_inst_4375_, crate::leanh::lean_box(0), v___x_4378_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_4380_: *mut crate::leanh::LeanObject,
    mut v_param_4381_: *mut crate::leanh::LeanObject,
    mut v_inst_4382_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4384_: u8 = 0;
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4384_ = (crate::leanh::lean_unbox(v_pu_4380_) as u8);
    v_res_4385_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0(
        v_pu_boxed_4384_,
        v_param_4381_,
        v_inst_4382_,
        v_____do__lift_4383_,
    );
    return v_res_4385_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
    mut v_pu_4386_: u8,
    mut v_inst_4387_: *mut crate::leanh::LeanObject,
    mut v_inst_4388_: *mut crate::leanh::LeanObject,
    mut v_f_4389_: *mut crate::leanh::LeanObject,
    mut v_param_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4391_ = crate::leanh::lean_ctor_get(v_inst_4388_, 1);
    crate::leanh::lean_inc(v_toBind_4391_);
    v_type_4392_ = crate::leanh::lean_ctor_get(v_param_4390_, 2);
    crate::leanh::lean_inc_ref(v_type_4392_);
    v___x_4393_ = crate::leanh::lean_box((v_pu_4386_) as usize);
    v___f_4394_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4394_, 0, v___x_4393_);
    crate::leanh::lean_closure_set(v___f_4394_, 1, v_param_4390_);
    crate::leanh::lean_closure_set(v___f_4394_, 2, v_inst_4387_);
    v___x_4395_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_4388_, v_f_4389_, v_type_4392_);
    v___x_4396_ = crate::leanh::lean_apply_4(
        v_toBind_4391_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4395_,
        v___f_4394_,
    );
    return v___x_4396_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___redArg___boxed(
    mut v_pu_4397_: *mut crate::leanh::LeanObject,
    mut v_inst_4398_: *mut crate::leanh::LeanObject,
    mut v_inst_4399_: *mut crate::leanh::LeanObject,
    mut v_f_4400_: *mut crate::leanh::LeanObject,
    mut v_param_4401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4402_: u8 = 0;
    let mut v_res_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4402_ = (crate::leanh::lean_unbox(v_pu_4397_) as u8);
    v_res_4403_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_boxed_4402_,
        v_inst_4398_,
        v_inst_4399_,
        v_f_4400_,
        v_param_4401_,
    );
    return v_res_4403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM(
    mut v_m_4404_: *mut crate::leanh::LeanObject,
    mut v_pu_4405_: u8,
    mut v_inst_4406_: *mut crate::leanh::LeanObject,
    mut v_inst_4407_: *mut crate::leanh::LeanObject,
    mut v_f_4408_: *mut crate::leanh::LeanObject,
    mut v_param_4409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_4405_,
        v_inst_4406_,
        v_inst_4407_,
        v_f_4408_,
        v_param_4409_,
    );
    return v___x_4410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_mapFVarM___boxed(
    mut v_m_4411_: *mut crate::leanh::LeanObject,
    mut v_pu_4412_: *mut crate::leanh::LeanObject,
    mut v_inst_4413_: *mut crate::leanh::LeanObject,
    mut v_inst_4414_: *mut crate::leanh::LeanObject,
    mut v_f_4415_: *mut crate::leanh::LeanObject,
    mut v_param_4416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4417_: u8 = 0;
    let mut v_res_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4417_ = (crate::leanh::lean_unbox(v_pu_4412_) as u8);
    v_res_4418_ = l_Lean_Compiler_LCNF_Param_mapFVarM(
        v_m_4411_,
        v_pu_boxed_4417_,
        v_inst_4413_,
        v_inst_4414_,
        v_f_4415_,
        v_param_4416_,
    );
    return v_res_4418_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___redArg(
    mut v_inst_4419_: *mut crate::leanh::LeanObject,
    mut v_f_4420_: *mut crate::leanh::LeanObject,
    mut v_param_4421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_4422_ = crate::leanh::lean_ctor_get(v_param_4421_, 2);
    crate::leanh::lean_inc_ref(v_type_4422_);
    crate::leanh::lean_dec_ref(v_param_4421_);
    v___x_4423_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_4419_, v_f_4420_, v_type_4422_);
    return v___x_4423_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM(
    mut v_m_4424_: *mut crate::leanh::LeanObject,
    mut v_pu_4425_: u8,
    mut v_inst_4426_: *mut crate::leanh::LeanObject,
    mut v_f_4427_: *mut crate::leanh::LeanObject,
    mut v_param_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_4426_, v_f_4427_, v_param_4428_);
    return v___x_4429_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___boxed(
    mut v_m_4430_: *mut crate::leanh::LeanObject,
    mut v_pu_4431_: *mut crate::leanh::LeanObject,
    mut v_inst_4432_: *mut crate::leanh::LeanObject,
    mut v_f_4433_: *mut crate::leanh::LeanObject,
    mut v_param_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4435_: u8 = 0;
    let mut v_res_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4435_ = (crate::leanh::lean_unbox(v_pu_4431_) as u8);
    v_res_4436_ = l_Lean_Compiler_LCNF_Param_forFVarM(
        v_m_4430_,
        v_pu_boxed_4435_,
        v_inst_4432_,
        v_f_4433_,
        v_param_4434_,
    );
    return v_res_4436_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(
    mut v_pu_4437_: u8,
    mut v_m_4438_: *mut crate::leanh::LeanObject,
    mut v_inst_4439_: *mut crate::leanh::LeanObject,
    mut v_inst_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lean_Compiler_LCNF_Param_mapFVarM___redArg(
        v_pu_4437_,
        v_inst_4439_,
        v_inst_4440_,
        v___y_4441_,
        v___y_4442_,
    );
    return v___x_4443_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed(
    mut v_pu_4444_: *mut crate::leanh::LeanObject,
    mut v_m_4445_: *mut crate::leanh::LeanObject,
    mut v_inst_4446_: *mut crate::leanh::LeanObject,
    mut v_inst_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4450_: u8 = 0;
    let mut v_res_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4450_ = (crate::leanh::lean_unbox(v_pu_4444_) as u8);
    v_res_4451_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0(
        v_pu_boxed_4450_,
        v_m_4445_,
        v_inst_4446_,
        v_inst_4447_,
        v___y_4448_,
        v___y_4449_,
    );
    return v_res_4451_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__1(
    mut v_m_4452_: *mut crate::leanh::LeanObject,
    mut v_inst_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_4453_, v___y_4454_, v___y_4455_);
    return v___x_4456_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam(
    mut v_pu_4458_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = crate::leanh::lean_box((v_pu_4458_) as usize);
    v___f_4460_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarParam___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4460_, 0, v___x_4459_);
    v___f_4461_ = l_Lean_Compiler_LCNF_instTraverseFVarParam___closed__0;
    v___x_4462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4462_, 0, v___f_4460_);
    crate::leanh::lean_ctor_set(v___x_4462_, 1, v___f_4461_);
    return v___x_4462_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarParam___boxed(
    mut v_pu_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4464_: u8 = 0;
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4464_ = (crate::leanh::lean_unbox(v_pu_4463_) as u8);
    v_res_4465_ = l_Lean_Compiler_LCNF_instTraverseFVarParam(v_pu_boxed_4464_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(
    mut v_decl_4466_: *mut crate::leanh::LeanObject,
    mut v_toPure_4467_: *mut crate::leanh::LeanObject,
    mut v_c_4468_: *mut crate::leanh::LeanObject,
    mut v_k_4469_: *mut crate::leanh::LeanObject,
    mut v_decl_4470_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4473_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: usize = 0;
    let mut v___x_4478_: usize = 0;
    let mut v___x_4479_: u8 = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: usize = 0;
    let mut v___x_4482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4477_ = lean_ptr_addr(v_k_4469_);
                v___x_4478_ = lean_ptr_addr(v_____do__lift_4471_);
                v___x_4479_ = lean_usize_dec_eq(v___x_4477_, v___x_4478_);
                if v___x_4479_ == 0 {
                    v___y_4473_ = v___x_4479_;
                    state = 1;
                    continue;
                } else {
                    v___x_4480_ = lean_ptr_addr(v_decl_4470_);
                    v___x_4481_ = lean_ptr_addr(v_decl_4466_);
                    v___x_4482_ = lean_usize_dec_eq(v___x_4480_, v___x_4481_);
                    v___y_4473_ = v___x_4482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4473_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4468_);
                    v___x_4474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4474_, 0, v_decl_4466_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 1, v_____do__lift_4471_);
                    v___x_4475_ = crate::leanh::lean_apply_2(
                        v_toPure_4467_,
                        crate::leanh::lean_box(0),
                        v___x_4474_,
                    );
                    return v___x_4475_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_4471_);
                    crate::leanh::lean_dec_ref(v_decl_4466_);
                    v___x_4476_ = crate::leanh::lean_apply_2(
                        v_toPure_4467_,
                        crate::leanh::lean_box(0),
                        v_c_4468_,
                    );
                    return v___x_4476_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed(
    mut v_decl_4483_: *mut crate::leanh::LeanObject,
    mut v_toPure_4484_: *mut crate::leanh::LeanObject,
    mut v_c_4485_: *mut crate::leanh::LeanObject,
    mut v_k_4486_: *mut crate::leanh::LeanObject,
    mut v_decl_4487_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0(
        v_decl_4483_,
        v_toPure_4484_,
        v_c_4485_,
        v_k_4486_,
        v_decl_4487_,
        v_____do__lift_4488_,
    );
    crate::leanh::lean_dec_ref(v_decl_4487_);
    crate::leanh::lean_dec_ref(v_k_4486_);
    return v_res_4489_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(
    mut v_____do__lift_4490_: *mut crate::leanh::LeanObject,
    mut v_i_4491_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4492_: *mut crate::leanh::LeanObject,
    mut v_toPure_4493_: *mut crate::leanh::LeanObject,
    mut v_y_4494_: *mut crate::leanh::LeanObject,
    mut v_k_4495_: *mut crate::leanh::LeanObject,
    mut v_c_4496_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4497_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4500_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: usize = 0;
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: usize = 0;
    let mut v___x_4515_: usize = 0;
    let mut v___x_4516_: u8 = 0;
    let mut v___x_4517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4514_ = lean_ptr_addr(v_fvarId_4497_);
                v___x_4515_ = lean_ptr_addr(v_____do__lift_4490_);
                v___x_4516_ = lean_usize_dec_eq(v___x_4514_, v___x_4515_);
                if v___x_4516_ == 0 {
                    v___y_4500_ = v___x_4516_;
                    state = 1;
                    continue;
                } else {
                    v___x_4517_ = lean_nat_dec_eq(v_i_4491_, v_i_4491_);
                    v___y_4500_ = v___x_4517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4500_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4496_);
                    v___x_4501_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4501_, 0, v_____do__lift_4490_);
                    crate::leanh::lean_ctor_set(v___x_4501_, 1, v_i_4491_);
                    crate::leanh::lean_ctor_set(v___x_4501_, 2, v_____do__lift_4492_);
                    crate::leanh::lean_ctor_set(v___x_4501_, 3, v_____do__lift_4498_);
                    v___x_4502_ = crate::leanh::lean_apply_2(
                        v_toPure_4493_,
                        crate::leanh::lean_box(0),
                        v___x_4501_,
                    );
                    return v___x_4502_;
                } else {
                    v___x_4503_ = lean_ptr_addr(v_y_4494_);
                    v___x_4504_ = lean_ptr_addr(v_____do__lift_4492_);
                    v___x_4505_ = lean_usize_dec_eq(v___x_4503_, v___x_4504_);
                    if v___x_4505_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4496_);
                        v___x_4506_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4506_, 0, v_____do__lift_4490_);
                        crate::leanh::lean_ctor_set(v___x_4506_, 1, v_i_4491_);
                        crate::leanh::lean_ctor_set(v___x_4506_, 2, v_____do__lift_4492_);
                        crate::leanh::lean_ctor_set(v___x_4506_, 3, v_____do__lift_4498_);
                        v___x_4507_ = crate::leanh::lean_apply_2(
                            v_toPure_4493_,
                            crate::leanh::lean_box(0),
                            v___x_4506_,
                        );
                        return v___x_4507_;
                    } else {
                        v___x_4508_ = lean_ptr_addr(v_k_4495_);
                        v___x_4509_ = lean_ptr_addr(v_____do__lift_4498_);
                        v___x_4510_ = lean_usize_dec_eq(v___x_4508_, v___x_4509_);
                        if v___x_4510_ == 0 {
                            crate::leanh::lean_dec_ref(v_c_4496_);
                            v___x_4511_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4511_, 0, v_____do__lift_4490_);
                            crate::leanh::lean_ctor_set(v___x_4511_, 1, v_i_4491_);
                            crate::leanh::lean_ctor_set(v___x_4511_, 2, v_____do__lift_4492_);
                            crate::leanh::lean_ctor_set(v___x_4511_, 3, v_____do__lift_4498_);
                            v___x_4512_ = crate::leanh::lean_apply_2(
                                v_toPure_4493_,
                                crate::leanh::lean_box(0),
                                v___x_4511_,
                            );
                            return v___x_4512_;
                        } else {
                            crate::leanh::lean_dec_ref(v_____do__lift_4498_);
                            crate::leanh::lean_dec(v_____do__lift_4492_);
                            crate::leanh::lean_dec(v_i_4491_);
                            crate::leanh::lean_dec(v_____do__lift_4490_);
                            v___x_4513_ = crate::leanh::lean_apply_2(
                                v_toPure_4493_,
                                crate::leanh::lean_box(0),
                                v_c_4496_,
                            );
                            return v___x_4513_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed(
    mut v_____do__lift_4518_: *mut crate::leanh::LeanObject,
    mut v_i_4519_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4520_: *mut crate::leanh::LeanObject,
    mut v_toPure_4521_: *mut crate::leanh::LeanObject,
    mut v_y_4522_: *mut crate::leanh::LeanObject,
    mut v_k_4523_: *mut crate::leanh::LeanObject,
    mut v_c_4524_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4525_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4527_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17(
        v_____do__lift_4518_,
        v_i_4519_,
        v_____do__lift_4520_,
        v_toPure_4521_,
        v_y_4522_,
        v_k_4523_,
        v_c_4524_,
        v_fvarId_4525_,
        v_____do__lift_4526_,
    );
    crate::leanh::lean_dec(v_fvarId_4525_);
    crate::leanh::lean_dec_ref(v_k_4523_);
    crate::leanh::lean_dec(v_y_4522_);
    return v_res_4527_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(
    mut v_fvarId_4528_: *mut crate::leanh::LeanObject,
    mut v_toPure_4529_: *mut crate::leanh::LeanObject,
    mut v_c_4530_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4532_: u8 = 0;
    v___x_4532_ = l_Lean_instBEqFVarId_beq(v_fvarId_4528_, v_____do__lift_4531_);
    if v___x_4532_ == 0 {
        let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_c_4530_);
        v___x_4533_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4533_, 0, v_____do__lift_4531_);
        v___x_4534_ =
            crate::leanh::lean_apply_2(v_toPure_4529_, crate::leanh::lean_box(0), v___x_4533_);
        return v___x_4534_;
    } else {
        let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____do__lift_4531_);
        v___x_4535_ =
            crate::leanh::lean_apply_2(v_toPure_4529_, crate::leanh::lean_box(0), v_c_4530_);
        return v___x_4535_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed(
    mut v_fvarId_4536_: *mut crate::leanh::LeanObject,
    mut v_toPure_4537_: *mut crate::leanh::LeanObject,
    mut v_c_4538_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4540_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15(
        v_fvarId_4536_,
        v_toPure_4537_,
        v_c_4538_,
        v_____do__lift_4539_,
    );
    crate::leanh::lean_dec(v_fvarId_4536_);
    return v_res_4540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(
    mut v_____do__lift_4541_: *mut crate::leanh::LeanObject,
    mut v_cidx_4542_: *mut crate::leanh::LeanObject,
    mut v_toPure_4543_: *mut crate::leanh::LeanObject,
    mut v_k_4544_: *mut crate::leanh::LeanObject,
    mut v_c_4545_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4546_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4549_: u8 = 0;
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: usize = 0;
    let mut v___x_4553_: usize = 0;
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4558_ = lean_ptr_addr(v_fvarId_4546_);
                v___x_4559_ = lean_ptr_addr(v_____do__lift_4541_);
                v___x_4560_ = lean_usize_dec_eq(v___x_4558_, v___x_4559_);
                if v___x_4560_ == 0 {
                    v___y_4549_ = v___x_4560_;
                    state = 1;
                    continue;
                } else {
                    v___x_4561_ = lean_nat_dec_eq(v_cidx_4542_, v_cidx_4542_);
                    v___y_4549_ = v___x_4561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4549_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4545_);
                    v___x_4550_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4550_, 0, v_____do__lift_4541_);
                    crate::leanh::lean_ctor_set(v___x_4550_, 1, v_cidx_4542_);
                    crate::leanh::lean_ctor_set(v___x_4550_, 2, v_____do__lift_4547_);
                    v___x_4551_ = crate::leanh::lean_apply_2(
                        v_toPure_4543_,
                        crate::leanh::lean_box(0),
                        v___x_4550_,
                    );
                    return v___x_4551_;
                } else {
                    v___x_4552_ = lean_ptr_addr(v_k_4544_);
                    v___x_4553_ = lean_ptr_addr(v_____do__lift_4547_);
                    v___x_4554_ = lean_usize_dec_eq(v___x_4552_, v___x_4553_);
                    if v___x_4554_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4545_);
                        v___x_4555_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4555_, 0, v_____do__lift_4541_);
                        crate::leanh::lean_ctor_set(v___x_4555_, 1, v_cidx_4542_);
                        crate::leanh::lean_ctor_set(v___x_4555_, 2, v_____do__lift_4547_);
                        v___x_4556_ = crate::leanh::lean_apply_2(
                            v_toPure_4543_,
                            crate::leanh::lean_box(0),
                            v___x_4555_,
                        );
                        return v___x_4556_;
                    } else {
                        crate::leanh::lean_dec_ref(v_____do__lift_4547_);
                        crate::leanh::lean_dec(v_cidx_4542_);
                        crate::leanh::lean_dec(v_____do__lift_4541_);
                        v___x_4557_ = crate::leanh::lean_apply_2(
                            v_toPure_4543_,
                            crate::leanh::lean_box(0),
                            v_c_4545_,
                        );
                        return v___x_4557_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed(
    mut v_____do__lift_4562_: *mut crate::leanh::LeanObject,
    mut v_cidx_4563_: *mut crate::leanh::LeanObject,
    mut v_toPure_4564_: *mut crate::leanh::LeanObject,
    mut v_k_4565_: *mut crate::leanh::LeanObject,
    mut v_c_4566_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4567_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27(
        v_____do__lift_4562_,
        v_cidx_4563_,
        v_toPure_4564_,
        v_k_4565_,
        v_c_4566_,
        v_fvarId_4567_,
        v_____do__lift_4568_,
    );
    crate::leanh::lean_dec(v_fvarId_4567_);
    crate::leanh::lean_dec_ref(v_k_4565_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(
    mut v_____do__lift_4570_: *mut crate::leanh::LeanObject,
    mut v_n_4571_: *mut crate::leanh::LeanObject,
    mut v_check_4572_: u8,
    mut v_persistent_4573_: u8,
    mut v_toPure_4574_: *mut crate::leanh::LeanObject,
    mut v_k_4575_: *mut crate::leanh::LeanObject,
    mut v_c_4576_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4577_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4580_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: usize = 0;
    let mut v___x_4584_: usize = 0;
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: usize = 0;
    let mut v___x_4590_: usize = 0;
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4589_ = lean_ptr_addr(v_fvarId_4577_);
                v___x_4590_ = lean_ptr_addr(v_____do__lift_4570_);
                v___x_4591_ = lean_usize_dec_eq(v___x_4589_, v___x_4590_);
                if v___x_4591_ == 0 {
                    v___y_4580_ = v___x_4591_;
                    state = 1;
                    continue;
                } else {
                    v___x_4592_ = lean_nat_dec_eq(v_n_4571_, v_n_4571_);
                    v___y_4580_ = v___x_4592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4580_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4576_);
                    v___x_4581_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_4581_, 0, v_____do__lift_4570_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 1, v_n_4571_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 2, v_____do__lift_4578_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4581_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_4572_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4581_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_4573_,
                    );
                    v___x_4582_ = crate::leanh::lean_apply_2(
                        v_toPure_4574_,
                        crate::leanh::lean_box(0),
                        v___x_4581_,
                    );
                    return v___x_4582_;
                } else {
                    v___x_4583_ = lean_ptr_addr(v_k_4575_);
                    v___x_4584_ = lean_ptr_addr(v_____do__lift_4578_);
                    v___x_4585_ = lean_usize_dec_eq(v___x_4583_, v___x_4584_);
                    if v___x_4585_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4576_);
                        v___x_4586_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_4586_, 0, v_____do__lift_4570_);
                        crate::leanh::lean_ctor_set(v___x_4586_, 1, v_n_4571_);
                        crate::leanh::lean_ctor_set(v___x_4586_, 2, v_____do__lift_4578_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v_check_4572_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4586_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v_persistent_4573_,
                        );
                        v___x_4587_ = crate::leanh::lean_apply_2(
                            v_toPure_4574_,
                            crate::leanh::lean_box(0),
                            v___x_4586_,
                        );
                        return v___x_4587_;
                    } else {
                        crate::leanh::lean_dec_ref(v_____do__lift_4578_);
                        crate::leanh::lean_dec(v_n_4571_);
                        crate::leanh::lean_dec(v_____do__lift_4570_);
                        v___x_4588_ = crate::leanh::lean_apply_2(
                            v_toPure_4574_,
                            crate::leanh::lean_box(0),
                            v_c_4576_,
                        );
                        return v___x_4588_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed(
    mut v_____do__lift_4593_: *mut crate::leanh::LeanObject,
    mut v_n_4594_: *mut crate::leanh::LeanObject,
    mut v_check_4595_: *mut crate::leanh::LeanObject,
    mut v_persistent_4596_: *mut crate::leanh::LeanObject,
    mut v_toPure_4597_: *mut crate::leanh::LeanObject,
    mut v_k_4598_: *mut crate::leanh::LeanObject,
    mut v_c_4599_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4600_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_1824__boxed_4602_: u8 = 0;
    let mut v_persistent_1825__boxed_4603_: u8 = 0;
    let mut v_res_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_1824__boxed_4602_ = (crate::leanh::lean_unbox(v_check_4595_) as u8);
    v_persistent_1825__boxed_4603_ = (crate::leanh::lean_unbox(v_persistent_4596_) as u8);
    v_res_4604_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29(
        v_____do__lift_4593_,
        v_n_4594_,
        v_check_1824__boxed_4602_,
        v_persistent_1825__boxed_4603_,
        v_toPure_4597_,
        v_k_4598_,
        v_c_4599_,
        v_fvarId_4600_,
        v_____do__lift_4601_,
    );
    crate::leanh::lean_dec(v_fvarId_4600_);
    crate::leanh::lean_dec_ref(v_k_4598_);
    return v_res_4604_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(
    mut v_____do__lift_4605_: *mut crate::leanh::LeanObject,
    mut v_i_4606_: *mut crate::leanh::LeanObject,
    mut v_offset_4607_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4608_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4609_: *mut crate::leanh::LeanObject,
    mut v_toPure_4610_: *mut crate::leanh::LeanObject,
    mut v_y_4611_: *mut crate::leanh::LeanObject,
    mut v_ty_4612_: *mut crate::leanh::LeanObject,
    mut v_k_4613_: *mut crate::leanh::LeanObject,
    mut v_c_4614_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4615_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: usize = 0;
    let mut v___x_4626_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: usize = 0;
    let mut v___x_4630_: usize = 0;
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: usize = 0;
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4640_ = lean_ptr_addr(v_fvarId_4615_);
                v___x_4641_ = lean_ptr_addr(v_____do__lift_4605_);
                v___x_4642_ = lean_usize_dec_eq(v___x_4640_, v___x_4641_);
                if v___x_4642_ == 0 {
                    v___y_4618_ = v___x_4642_;
                    state = 1;
                    continue;
                } else {
                    v___x_4643_ = lean_nat_dec_eq(v_i_4606_, v_i_4606_);
                    v___y_4618_ = v___x_4643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4618_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4614_);
                    v___x_4619_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4619_, 0, v_____do__lift_4605_);
                    crate::leanh::lean_ctor_set(v___x_4619_, 1, v_i_4606_);
                    crate::leanh::lean_ctor_set(v___x_4619_, 2, v_offset_4607_);
                    crate::leanh::lean_ctor_set(v___x_4619_, 3, v_____do__lift_4608_);
                    crate::leanh::lean_ctor_set(v___x_4619_, 4, v_____do__lift_4609_);
                    crate::leanh::lean_ctor_set(v___x_4619_, 5, v_____do__lift_4616_);
                    v___x_4620_ = crate::leanh::lean_apply_2(
                        v_toPure_4610_,
                        crate::leanh::lean_box(0),
                        v___x_4619_,
                    );
                    return v___x_4620_;
                } else {
                    v___x_4621_ = lean_nat_dec_eq(v_offset_4607_, v_offset_4607_);
                    if v___x_4621_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4614_);
                        v___x_4622_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4622_, 0, v_____do__lift_4605_);
                        crate::leanh::lean_ctor_set(v___x_4622_, 1, v_i_4606_);
                        crate::leanh::lean_ctor_set(v___x_4622_, 2, v_offset_4607_);
                        crate::leanh::lean_ctor_set(v___x_4622_, 3, v_____do__lift_4608_);
                        crate::leanh::lean_ctor_set(v___x_4622_, 4, v_____do__lift_4609_);
                        crate::leanh::lean_ctor_set(v___x_4622_, 5, v_____do__lift_4616_);
                        v___x_4623_ = crate::leanh::lean_apply_2(
                            v_toPure_4610_,
                            crate::leanh::lean_box(0),
                            v___x_4622_,
                        );
                        return v___x_4623_;
                    } else {
                        v___x_4624_ = lean_ptr_addr(v_y_4611_);
                        v___x_4625_ = lean_ptr_addr(v_____do__lift_4608_);
                        v___x_4626_ = lean_usize_dec_eq(v___x_4624_, v___x_4625_);
                        if v___x_4626_ == 0 {
                            crate::leanh::lean_dec_ref(v_c_4614_);
                            v___x_4627_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4627_, 0, v_____do__lift_4605_);
                            crate::leanh::lean_ctor_set(v___x_4627_, 1, v_i_4606_);
                            crate::leanh::lean_ctor_set(v___x_4627_, 2, v_offset_4607_);
                            crate::leanh::lean_ctor_set(v___x_4627_, 3, v_____do__lift_4608_);
                            crate::leanh::lean_ctor_set(v___x_4627_, 4, v_____do__lift_4609_);
                            crate::leanh::lean_ctor_set(v___x_4627_, 5, v_____do__lift_4616_);
                            v___x_4628_ = crate::leanh::lean_apply_2(
                                v_toPure_4610_,
                                crate::leanh::lean_box(0),
                                v___x_4627_,
                            );
                            return v___x_4628_;
                        } else {
                            v___x_4629_ = lean_ptr_addr(v_ty_4612_);
                            v___x_4630_ = lean_ptr_addr(v_____do__lift_4609_);
                            v___x_4631_ = lean_usize_dec_eq(v___x_4629_, v___x_4630_);
                            if v___x_4631_ == 0 {
                                crate::leanh::lean_dec_ref(v_c_4614_);
                                v___x_4632_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4632_, 0, v_____do__lift_4605_);
                                crate::leanh::lean_ctor_set(v___x_4632_, 1, v_i_4606_);
                                crate::leanh::lean_ctor_set(v___x_4632_, 2, v_offset_4607_);
                                crate::leanh::lean_ctor_set(v___x_4632_, 3, v_____do__lift_4608_);
                                crate::leanh::lean_ctor_set(v___x_4632_, 4, v_____do__lift_4609_);
                                crate::leanh::lean_ctor_set(v___x_4632_, 5, v_____do__lift_4616_);
                                v___x_4633_ = crate::leanh::lean_apply_2(
                                    v_toPure_4610_,
                                    crate::leanh::lean_box(0),
                                    v___x_4632_,
                                );
                                return v___x_4633_;
                            } else {
                                v___x_4634_ = lean_ptr_addr(v_k_4613_);
                                v___x_4635_ = lean_ptr_addr(v_____do__lift_4616_);
                                v___x_4636_ = lean_usize_dec_eq(v___x_4634_, v___x_4635_);
                                if v___x_4636_ == 0 {
                                    crate::leanh::lean_dec_ref(v_c_4614_);
                                    v___x_4637_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v___x_4637_,
                                        0,
                                        v_____do__lift_4605_,
                                    );
                                    crate::leanh::lean_ctor_set(v___x_4637_, 1, v_i_4606_);
                                    crate::leanh::lean_ctor_set(v___x_4637_, 2, v_offset_4607_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_4637_,
                                        3,
                                        v_____do__lift_4608_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v___x_4637_,
                                        4,
                                        v_____do__lift_4609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v___x_4637_,
                                        5,
                                        v_____do__lift_4616_,
                                    );
                                    v___x_4638_ = crate::leanh::lean_apply_2(
                                        v_toPure_4610_,
                                        crate::leanh::lean_box(0),
                                        v___x_4637_,
                                    );
                                    return v___x_4638_;
                                } else {
                                    crate::leanh::lean_dec_ref(v_____do__lift_4616_);
                                    crate::leanh::lean_dec_ref(v_____do__lift_4609_);
                                    crate::leanh::lean_dec(v_____do__lift_4608_);
                                    crate::leanh::lean_dec(v_offset_4607_);
                                    crate::leanh::lean_dec(v_i_4606_);
                                    crate::leanh::lean_dec(v_____do__lift_4605_);
                                    v___x_4639_ = crate::leanh::lean_apply_2(
                                        v_toPure_4610_,
                                        crate::leanh::lean_box(0),
                                        v_c_4614_,
                                    );
                                    return v___x_4639_;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed(
    mut v_____do__lift_4644_: *mut crate::leanh::LeanObject,
    mut v_i_4645_: *mut crate::leanh::LeanObject,
    mut v_offset_4646_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4647_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4648_: *mut crate::leanh::LeanObject,
    mut v_toPure_4649_: *mut crate::leanh::LeanObject,
    mut v_y_4650_: *mut crate::leanh::LeanObject,
    mut v_ty_4651_: *mut crate::leanh::LeanObject,
    mut v_k_4652_: *mut crate::leanh::LeanObject,
    mut v_c_4653_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4654_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4656_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23(
        v_____do__lift_4644_,
        v_i_4645_,
        v_offset_4646_,
        v_____do__lift_4647_,
        v_____do__lift_4648_,
        v_toPure_4649_,
        v_y_4650_,
        v_ty_4651_,
        v_k_4652_,
        v_c_4653_,
        v_fvarId_4654_,
        v_____do__lift_4655_,
    );
    crate::leanh::lean_dec(v_fvarId_4654_);
    crate::leanh::lean_dec_ref(v_k_4652_);
    crate::leanh::lean_dec_ref(v_ty_4651_);
    crate::leanh::lean_dec(v_y_4650_);
    return v_res_4656_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(
    mut v_pu_4657_: u8,
    mut v_decl_4658_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4659_: *mut crate::leanh::LeanObject,
    mut v_params_4660_: *mut crate::leanh::LeanObject,
    mut v_inst_4661_: *mut crate::leanh::LeanObject,
    mut v_toBind_4662_: *mut crate::leanh::LeanObject,
    mut v___f_4663_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = crate::leanh::lean_box((v_pu_4657_) as usize);
    v___x_4666_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___x_4666_, 0, v___x_4665_);
    crate::leanh::lean_closure_set(v___x_4666_, 1, v_decl_4658_);
    crate::leanh::lean_closure_set(v___x_4666_, 2, v_____do__lift_4659_);
    crate::leanh::lean_closure_set(v___x_4666_, 3, v_params_4660_);
    crate::leanh::lean_closure_set(v___x_4666_, 4, v_____do__lift_4664_);
    v___x_4667_ = crate::leanh::lean_apply_2(v_inst_4661_, crate::leanh::lean_box(0), v___x_4666_);
    v___x_4668_ = crate::leanh::lean_apply_4(
        v_toBind_4662_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4667_,
        v___f_4663_,
    );
    return v___x_4668_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed(
    mut v_pu_4669_: *mut crate::leanh::LeanObject,
    mut v_decl_4670_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4671_: *mut crate::leanh::LeanObject,
    mut v_params_4672_: *mut crate::leanh::LeanObject,
    mut v_inst_4673_: *mut crate::leanh::LeanObject,
    mut v_toBind_4674_: *mut crate::leanh::LeanObject,
    mut v___f_4675_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4677_: u8 = 0;
    let mut v_res_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4677_ = (crate::leanh::lean_unbox(v_pu_4669_) as u8);
    v_res_4678_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4(
        v_pu_boxed_4677_,
        v_decl_4670_,
        v_____do__lift_4671_,
        v_params_4672_,
        v_inst_4673_,
        v_toBind_4674_,
        v___f_4675_,
        v_____do__lift_4676_,
    );
    return v_res_4678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(
    mut v_____do__lift_4679_: *mut crate::leanh::LeanObject,
    mut v_toPure_4680_: *mut crate::leanh::LeanObject,
    mut v_c_4681_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4682_: *mut crate::leanh::LeanObject,
    mut v_args_4683_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4686_: u8 = 0;
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: usize = 0;
    let mut v___x_4692_: usize = 0;
    let mut v___x_4693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4690_ = l_Lean_instBEqFVarId_beq(v_fvarId_4682_, v_____do__lift_4679_);
                if v___x_4690_ == 0 {
                    v___y_4686_ = v___x_4690_;
                    state = 1;
                    continue;
                } else {
                    v___x_4691_ = lean_ptr_addr(v_args_4683_);
                    v___x_4692_ = lean_ptr_addr(v_____do__lift_4684_);
                    v___x_4693_ = lean_usize_dec_eq(v___x_4691_, v___x_4692_);
                    v___y_4686_ = v___x_4693_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4686_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4681_);
                    v___x_4687_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4687_, 0, v_____do__lift_4679_);
                    crate::leanh::lean_ctor_set(v___x_4687_, 1, v_____do__lift_4684_);
                    v___x_4688_ = crate::leanh::lean_apply_2(
                        v_toPure_4680_,
                        crate::leanh::lean_box(0),
                        v___x_4687_,
                    );
                    return v___x_4688_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_4684_);
                    crate::leanh::lean_dec(v_____do__lift_4679_);
                    v___x_4689_ = crate::leanh::lean_apply_2(
                        v_toPure_4680_,
                        crate::leanh::lean_box(0),
                        v_c_4681_,
                    );
                    return v___x_4689_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed(
    mut v_____do__lift_4694_: *mut crate::leanh::LeanObject,
    mut v_toPure_4695_: *mut crate::leanh::LeanObject,
    mut v_c_4696_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4697_: *mut crate::leanh::LeanObject,
    mut v_args_4698_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4700_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12(
        v_____do__lift_4694_,
        v_toPure_4695_,
        v_c_4696_,
        v_fvarId_4697_,
        v_args_4698_,
        v_____do__lift_4699_,
    );
    crate::leanh::lean_dec_ref(v_args_4698_);
    crate::leanh::lean_dec(v_fvarId_4697_);
    return v_res_4700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(
    mut v_toPure_4701_: *mut crate::leanh::LeanObject,
    mut v_c_4702_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4703_: *mut crate::leanh::LeanObject,
    mut v_args_4704_: *mut crate::leanh::LeanObject,
    mut v_pu_4705_: u8,
    mut v_inst_4706_: *mut crate::leanh::LeanObject,
    mut v_inst_4707_: *mut crate::leanh::LeanObject,
    mut v_f_4708_: *mut crate::leanh::LeanObject,
    mut v_toBind_4709_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4714_: usize = 0;
    let mut v___x_4715_: usize = 0;
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_args_4704_);
    v___f_4711_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__12___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4711_, 0, v_____do__lift_4710_);
    crate::leanh::lean_closure_set(v___f_4711_, 1, v_toPure_4701_);
    crate::leanh::lean_closure_set(v___f_4711_, 2, v_c_4702_);
    crate::leanh::lean_closure_set(v___f_4711_, 3, v_fvarId_4703_);
    crate::leanh::lean_closure_set(v___f_4711_, 4, v_args_4704_);
    v___x_4712_ = crate::leanh::lean_box((v_pu_4705_) as usize);
    crate::leanh::lean_inc_ref(v_inst_4707_);
    v___x_4713_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Arg_mapFVarM___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_4713_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4713_, 1, v___x_4712_);
    crate::leanh::lean_closure_set(v___x_4713_, 2, v_inst_4706_);
    crate::leanh::lean_closure_set(v___x_4713_, 3, v_inst_4707_);
    crate::leanh::lean_closure_set(v___x_4713_, 4, v_f_4708_);
    v_sz_4714_ = lean_array_size(v_args_4704_);
    v___x_4715_ = 0usize;
    v___x_4716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4707_,
        v___x_4713_,
        v_sz_4714_,
        v___x_4715_,
        v_args_4704_,
    );
    v___x_4717_ = crate::leanh::lean_apply_4(
        v_toBind_4709_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4716_,
        v___f_4711_,
    );
    return v___x_4717_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed(
    mut v_toPure_4718_: *mut crate::leanh::LeanObject,
    mut v_c_4719_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4720_: *mut crate::leanh::LeanObject,
    mut v_args_4721_: *mut crate::leanh::LeanObject,
    mut v_pu_4722_: *mut crate::leanh::LeanObject,
    mut v_inst_4723_: *mut crate::leanh::LeanObject,
    mut v_inst_4724_: *mut crate::leanh::LeanObject,
    mut v_f_4725_: *mut crate::leanh::LeanObject,
    mut v_toBind_4726_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4728_: u8 = 0;
    let mut v_res_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4728_ = (crate::leanh::lean_unbox(v_pu_4722_) as u8);
    v_res_4729_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9(
        v_toPure_4718_,
        v_c_4719_,
        v_fvarId_4720_,
        v_args_4721_,
        v_pu_boxed_4728_,
        v_inst_4723_,
        v_inst_4724_,
        v_f_4725_,
        v_toBind_4726_,
        v_____do__lift_4727_,
    );
    return v_res_4729_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(
    mut v_typeName_4730_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4731_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4732_: *mut crate::leanh::LeanObject,
    mut v_toPure_4733_: *mut crate::leanh::LeanObject,
    mut v_discr_4734_: *mut crate::leanh::LeanObject,
    mut v_c_4735_: *mut crate::leanh::LeanObject,
    mut v_alts_4736_: *mut crate::leanh::LeanObject,
    mut v_resultType_4737_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: u8 = 0;
    let mut v___x_4745_: u8 = 0;
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: usize = 0;
    let mut v___x_4748_: usize = 0;
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4747_ = lean_ptr_addr(v_alts_4736_);
                v___x_4748_ = lean_ptr_addr(v_____do__lift_4738_);
                v___x_4749_ = lean_usize_dec_eq(v___x_4747_, v___x_4748_);
                if v___x_4749_ == 0 {
                    v___y_4744_ = v___x_4749_;
                    state = 2;
                    continue;
                } else {
                    v___x_4750_ = lean_ptr_addr(v_resultType_4737_);
                    v___x_4751_ = lean_ptr_addr(v_____do__lift_4731_);
                    v___x_4752_ = lean_usize_dec_eq(v___x_4750_, v___x_4751_);
                    v___y_4744_ = v___x_4752_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4740_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4740_, 0, v_typeName_4730_);
                crate::leanh::lean_ctor_set(v___x_4740_, 1, v_____do__lift_4731_);
                crate::leanh::lean_ctor_set(v___x_4740_, 2, v_____do__lift_4732_);
                crate::leanh::lean_ctor_set(v___x_4740_, 3, v_____do__lift_4738_);
                v___x_4741_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4740_);
                v___x_4742_ = crate::leanh::lean_apply_2(
                    v_toPure_4733_,
                    crate::leanh::lean_box(0),
                    v___x_4741_,
                );
                return v___x_4742_;
            }
            2 => {
                if v___y_4744_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4735_);
                    state = 1;
                    continue;
                } else {
                    v___x_4745_ = l_Lean_instBEqFVarId_beq(v_discr_4734_, v_____do__lift_4732_);
                    if v___x_4745_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4735_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_____do__lift_4738_);
                        crate::leanh::lean_dec(v_____do__lift_4732_);
                        crate::leanh::lean_dec_ref(v_____do__lift_4731_);
                        crate::leanh::lean_dec(v_typeName_4730_);
                        v___x_4746_ = crate::leanh::lean_apply_2(
                            v_toPure_4733_,
                            crate::leanh::lean_box(0),
                            v_c_4735_,
                        );
                        return v___x_4746_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed(
    mut v_typeName_4753_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4754_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4755_: *mut crate::leanh::LeanObject,
    mut v_toPure_4756_: *mut crate::leanh::LeanObject,
    mut v_discr_4757_: *mut crate::leanh::LeanObject,
    mut v_c_4758_: *mut crate::leanh::LeanObject,
    mut v_alts_4759_: *mut crate::leanh::LeanObject,
    mut v_resultType_4760_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11(
        v_typeName_4753_,
        v_____do__lift_4754_,
        v_____do__lift_4755_,
        v_toPure_4756_,
        v_discr_4757_,
        v_c_4758_,
        v_alts_4759_,
        v_resultType_4760_,
        v_____do__lift_4761_,
    );
    crate::leanh::lean_dec_ref(v_resultType_4760_);
    crate::leanh::lean_dec_ref(v_alts_4759_);
    crate::leanh::lean_dec(v_discr_4757_);
    return v_res_4762_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13(
    mut v_typeName_4763_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4764_: *mut crate::leanh::LeanObject,
    mut v_toPure_4765_: *mut crate::leanh::LeanObject,
    mut v_discr_4766_: *mut crate::leanh::LeanObject,
    mut v_c_4767_: *mut crate::leanh::LeanObject,
    mut v_alts_4768_: *mut crate::leanh::LeanObject,
    mut v_resultType_4769_: *mut crate::leanh::LeanObject,
    mut v_inst_4770_: *mut crate::leanh::LeanObject,
    mut v___f_4771_: *mut crate::leanh::LeanObject,
    mut v_toBind_4772_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_alts_4768_);
    v___f_4774_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__11___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_4774_, 0, v_typeName_4763_);
    crate::leanh::lean_closure_set(v___f_4774_, 1, v_____do__lift_4764_);
    crate::leanh::lean_closure_set(v___f_4774_, 2, v_____do__lift_4773_);
    crate::leanh::lean_closure_set(v___f_4774_, 3, v_toPure_4765_);
    crate::leanh::lean_closure_set(v___f_4774_, 4, v_discr_4766_);
    crate::leanh::lean_closure_set(v___f_4774_, 5, v_c_4767_);
    crate::leanh::lean_closure_set(v___f_4774_, 6, v_alts_4768_);
    crate::leanh::lean_closure_set(v___f_4774_, 7, v_resultType_4769_);
    v___x_4775_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4776_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4770_,
        v___f_4771_,
        v___x_4775_,
        v_alts_4768_,
    );
    v___x_4777_ = crate::leanh::lean_apply_4(
        v_toBind_4772_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4776_,
        v___f_4774_,
    );
    return v___x_4777_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14(
    mut v_typeName_4778_: *mut crate::leanh::LeanObject,
    mut v_toPure_4779_: *mut crate::leanh::LeanObject,
    mut v_discr_4780_: *mut crate::leanh::LeanObject,
    mut v_c_4781_: *mut crate::leanh::LeanObject,
    mut v_alts_4782_: *mut crate::leanh::LeanObject,
    mut v_resultType_4783_: *mut crate::leanh::LeanObject,
    mut v_inst_4784_: *mut crate::leanh::LeanObject,
    mut v___f_4785_: *mut crate::leanh::LeanObject,
    mut v_toBind_4786_: *mut crate::leanh::LeanObject,
    mut v_f_4787_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_4786_);
    crate::leanh::lean_inc(v_discr_4780_);
    v___f_4789_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__13 as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_4789_, 0, v_typeName_4778_);
    crate::leanh::lean_closure_set(v___f_4789_, 1, v_____do__lift_4788_);
    crate::leanh::lean_closure_set(v___f_4789_, 2, v_toPure_4779_);
    crate::leanh::lean_closure_set(v___f_4789_, 3, v_discr_4780_);
    crate::leanh::lean_closure_set(v___f_4789_, 4, v_c_4781_);
    crate::leanh::lean_closure_set(v___f_4789_, 5, v_alts_4782_);
    crate::leanh::lean_closure_set(v___f_4789_, 6, v_resultType_4783_);
    crate::leanh::lean_closure_set(v___f_4789_, 7, v_inst_4784_);
    crate::leanh::lean_closure_set(v___f_4789_, 8, v___f_4785_);
    crate::leanh::lean_closure_set(v___f_4789_, 9, v_toBind_4786_);
    v___x_4790_ = crate::leanh::lean_apply_1(v_f_4787_, v_discr_4780_);
    v___x_4791_ = crate::leanh::lean_apply_4(
        v_toBind_4786_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4790_,
        v___f_4789_,
    );
    return v___x_4791_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(
    mut v_____do__lift_4792_: *mut crate::leanh::LeanObject,
    mut v_n_4793_: *mut crate::leanh::LeanObject,
    mut v_check_4794_: u8,
    mut v_persistent_4795_: u8,
    mut v_objs_x3f_4796_: *mut crate::leanh::LeanObject,
    mut v_toPure_4797_: *mut crate::leanh::LeanObject,
    mut v_k_4798_: *mut crate::leanh::LeanObject,
    mut v_c_4799_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4800_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4803_: u8 = 0;
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: usize = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: usize = 0;
    let mut v___x_4817_: usize = 0;
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4816_ = lean_ptr_addr(v_fvarId_4800_);
                v___x_4817_ = lean_ptr_addr(v_____do__lift_4792_);
                v___x_4818_ = lean_usize_dec_eq(v___x_4816_, v___x_4817_);
                if v___x_4818_ == 0 {
                    v___y_4803_ = v___x_4818_;
                    state = 1;
                    continue;
                } else {
                    v___x_4819_ = lean_nat_dec_eq(v_n_4793_, v_n_4793_);
                    v___y_4803_ = v___x_4819_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4803_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4799_);
                    v___x_4804_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_4804_, 0, v_____do__lift_4792_);
                    crate::leanh::lean_ctor_set(v___x_4804_, 1, v_n_4793_);
                    crate::leanh::lean_ctor_set(v___x_4804_, 2, v_objs_x3f_4796_);
                    crate::leanh::lean_ctor_set(v___x_4804_, 3, v_____do__lift_4801_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4804_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_4794_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4804_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_4795_,
                    );
                    v___x_4805_ = crate::leanh::lean_apply_2(
                        v_toPure_4797_,
                        crate::leanh::lean_box(0),
                        v___x_4804_,
                    );
                    return v___x_4805_;
                } else {
                    v___x_4806_ = lean_ptr_addr(v_objs_x3f_4796_);
                    v___x_4807_ = lean_usize_dec_eq(v___x_4806_, v___x_4806_);
                    if v___x_4807_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4799_);
                        v___x_4808_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_4808_, 0, v_____do__lift_4792_);
                        crate::leanh::lean_ctor_set(v___x_4808_, 1, v_n_4793_);
                        crate::leanh::lean_ctor_set(v___x_4808_, 2, v_objs_x3f_4796_);
                        crate::leanh::lean_ctor_set(v___x_4808_, 3, v_____do__lift_4801_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4808_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v_check_4794_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4808_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                            v_persistent_4795_,
                        );
                        v___x_4809_ = crate::leanh::lean_apply_2(
                            v_toPure_4797_,
                            crate::leanh::lean_box(0),
                            v___x_4808_,
                        );
                        return v___x_4809_;
                    } else {
                        v___x_4810_ = lean_ptr_addr(v_k_4798_);
                        v___x_4811_ = lean_ptr_addr(v_____do__lift_4801_);
                        v___x_4812_ = lean_usize_dec_eq(v___x_4810_, v___x_4811_);
                        if v___x_4812_ == 0 {
                            crate::leanh::lean_dec_ref(v_c_4799_);
                            v___x_4813_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                            crate::leanh::lean_ctor_set(v___x_4813_, 0, v_____do__lift_4792_);
                            crate::leanh::lean_ctor_set(v___x_4813_, 1, v_n_4793_);
                            crate::leanh::lean_ctor_set(v___x_4813_, 2, v_objs_x3f_4796_);
                            crate::leanh::lean_ctor_set(v___x_4813_, 3, v_____do__lift_4801_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_4813_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v_check_4794_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_4813_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1)
                                    as u32,
                                v_persistent_4795_,
                            );
                            v___x_4814_ = crate::leanh::lean_apply_2(
                                v_toPure_4797_,
                                crate::leanh::lean_box(0),
                                v___x_4813_,
                            );
                            return v___x_4814_;
                        } else {
                            crate::leanh::lean_dec_ref(v_____do__lift_4801_);
                            crate::leanh::lean_dec(v_objs_x3f_4796_);
                            crate::leanh::lean_dec(v_n_4793_);
                            crate::leanh::lean_dec(v_____do__lift_4792_);
                            v___x_4815_ = crate::leanh::lean_apply_2(
                                v_toPure_4797_,
                                crate::leanh::lean_box(0),
                                v_c_4799_,
                            );
                            return v___x_4815_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed(
    mut v_____do__lift_4820_: *mut crate::leanh::LeanObject,
    mut v_n_4821_: *mut crate::leanh::LeanObject,
    mut v_check_4822_: *mut crate::leanh::LeanObject,
    mut v_persistent_4823_: *mut crate::leanh::LeanObject,
    mut v_objs_x3f_4824_: *mut crate::leanh::LeanObject,
    mut v_toPure_4825_: *mut crate::leanh::LeanObject,
    mut v_k_4826_: *mut crate::leanh::LeanObject,
    mut v_c_4827_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4828_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_2130__boxed_4830_: u8 = 0;
    let mut v_persistent_2131__boxed_4831_: u8 = 0;
    let mut v_res_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_2130__boxed_4830_ = (crate::leanh::lean_unbox(v_check_4822_) as u8);
    v_persistent_2131__boxed_4831_ = (crate::leanh::lean_unbox(v_persistent_4823_) as u8);
    v_res_4832_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31(
        v_____do__lift_4820_,
        v_n_4821_,
        v_check_2130__boxed_4830_,
        v_persistent_2131__boxed_4831_,
        v_objs_x3f_4824_,
        v_toPure_4825_,
        v_k_4826_,
        v_c_4827_,
        v_fvarId_4828_,
        v_____do__lift_4829_,
    );
    crate::leanh::lean_dec(v_fvarId_4828_);
    crate::leanh::lean_dec_ref(v_k_4826_);
    return v_res_4832_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(
    mut v_decl_4833_: *mut crate::leanh::LeanObject,
    mut v_toPure_4834_: *mut crate::leanh::LeanObject,
    mut v_c_4835_: *mut crate::leanh::LeanObject,
    mut v_k_4836_: *mut crate::leanh::LeanObject,
    mut v_decl_4837_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4840_: u8 = 0;
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v___x_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4844_ = lean_ptr_addr(v_k_4836_);
                v___x_4845_ = lean_ptr_addr(v_____do__lift_4838_);
                v___x_4846_ = lean_usize_dec_eq(v___x_4844_, v___x_4845_);
                if v___x_4846_ == 0 {
                    v___y_4840_ = v___x_4846_;
                    state = 1;
                    continue;
                } else {
                    v___x_4847_ = lean_ptr_addr(v_decl_4837_);
                    v___x_4848_ = lean_ptr_addr(v_decl_4833_);
                    v___x_4849_ = lean_usize_dec_eq(v___x_4847_, v___x_4848_);
                    v___y_4840_ = v___x_4849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4840_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4835_);
                    v___x_4841_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4841_, 0, v_decl_4833_);
                    crate::leanh::lean_ctor_set(v___x_4841_, 1, v_____do__lift_4838_);
                    v___x_4842_ = crate::leanh::lean_apply_2(
                        v_toPure_4834_,
                        crate::leanh::lean_box(0),
                        v___x_4841_,
                    );
                    return v___x_4842_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_4838_);
                    crate::leanh::lean_dec_ref(v_decl_4833_);
                    v___x_4843_ = crate::leanh::lean_apply_2(
                        v_toPure_4834_,
                        crate::leanh::lean_box(0),
                        v_c_4835_,
                    );
                    return v___x_4843_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed(
    mut v_decl_4850_: *mut crate::leanh::LeanObject,
    mut v_toPure_4851_: *mut crate::leanh::LeanObject,
    mut v_c_4852_: *mut crate::leanh::LeanObject,
    mut v_k_4853_: *mut crate::leanh::LeanObject,
    mut v_decl_4854_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4856_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7(
        v_decl_4850_,
        v_toPure_4851_,
        v_c_4852_,
        v_k_4853_,
        v_decl_4854_,
        v_____do__lift_4855_,
    );
    crate::leanh::lean_dec_ref(v_decl_4854_);
    crate::leanh::lean_dec_ref(v_k_4853_);
    return v_res_4856_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(
    mut v_decl_4857_: *mut crate::leanh::LeanObject,
    mut v_toPure_4858_: *mut crate::leanh::LeanObject,
    mut v_c_4859_: *mut crate::leanh::LeanObject,
    mut v_k_4860_: *mut crate::leanh::LeanObject,
    mut v_decl_4861_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4864_: u8 = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: usize = 0;
    let mut v___x_4869_: usize = 0;
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: usize = 0;
    let mut v___x_4873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4868_ = lean_ptr_addr(v_k_4860_);
                v___x_4869_ = lean_ptr_addr(v_____do__lift_4862_);
                v___x_4870_ = lean_usize_dec_eq(v___x_4868_, v___x_4869_);
                if v___x_4870_ == 0 {
                    v___y_4864_ = v___x_4870_;
                    state = 1;
                    continue;
                } else {
                    v___x_4871_ = lean_ptr_addr(v_decl_4861_);
                    v___x_4872_ = lean_ptr_addr(v_decl_4857_);
                    v___x_4873_ = lean_usize_dec_eq(v___x_4871_, v___x_4872_);
                    v___y_4864_ = v___x_4873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4864_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4859_);
                    v___x_4865_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4865_, 0, v_decl_4857_);
                    crate::leanh::lean_ctor_set(v___x_4865_, 1, v_____do__lift_4862_);
                    v___x_4866_ = crate::leanh::lean_apply_2(
                        v_toPure_4858_,
                        crate::leanh::lean_box(0),
                        v___x_4865_,
                    );
                    return v___x_4866_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_4862_);
                    crate::leanh::lean_dec_ref(v_decl_4857_);
                    v___x_4867_ = crate::leanh::lean_apply_2(
                        v_toPure_4858_,
                        crate::leanh::lean_box(0),
                        v_c_4859_,
                    );
                    return v___x_4867_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed(
    mut v_decl_4874_: *mut crate::leanh::LeanObject,
    mut v_toPure_4875_: *mut crate::leanh::LeanObject,
    mut v_c_4876_: *mut crate::leanh::LeanObject,
    mut v_k_4877_: *mut crate::leanh::LeanObject,
    mut v_decl_4878_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4880_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2(
        v_decl_4874_,
        v_toPure_4875_,
        v_c_4876_,
        v_k_4877_,
        v_decl_4878_,
        v_____do__lift_4879_,
    );
    crate::leanh::lean_dec_ref(v_decl_4878_);
    crate::leanh::lean_dec_ref(v_k_4877_);
    return v_res_4880_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(
    mut v_____do__lift_4881_: *mut crate::leanh::LeanObject,
    mut v_i_4882_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4883_: *mut crate::leanh::LeanObject,
    mut v_toPure_4884_: *mut crate::leanh::LeanObject,
    mut v_y_4885_: *mut crate::leanh::LeanObject,
    mut v_k_4886_: *mut crate::leanh::LeanObject,
    mut v_c_4887_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4888_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4891_: u8 = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: usize = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: u8 = 0;
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: u8 = 0;
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: usize = 0;
    let mut v___x_4906_: usize = 0;
    let mut v___x_4907_: u8 = 0;
    let mut v___x_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4905_ = lean_ptr_addr(v_fvarId_4888_);
                v___x_4906_ = lean_ptr_addr(v_____do__lift_4881_);
                v___x_4907_ = lean_usize_dec_eq(v___x_4905_, v___x_4906_);
                if v___x_4907_ == 0 {
                    v___y_4891_ = v___x_4907_;
                    state = 1;
                    continue;
                } else {
                    v___x_4908_ = lean_nat_dec_eq(v_i_4882_, v_i_4882_);
                    v___y_4891_ = v___x_4908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4891_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4887_);
                    v___x_4892_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4892_, 0, v_____do__lift_4881_);
                    crate::leanh::lean_ctor_set(v___x_4892_, 1, v_i_4882_);
                    crate::leanh::lean_ctor_set(v___x_4892_, 2, v_____do__lift_4883_);
                    crate::leanh::lean_ctor_set(v___x_4892_, 3, v_____do__lift_4889_);
                    v___x_4893_ = crate::leanh::lean_apply_2(
                        v_toPure_4884_,
                        crate::leanh::lean_box(0),
                        v___x_4892_,
                    );
                    return v___x_4893_;
                } else {
                    v___x_4894_ = lean_ptr_addr(v_y_4885_);
                    v___x_4895_ = lean_ptr_addr(v_____do__lift_4883_);
                    v___x_4896_ = lean_usize_dec_eq(v___x_4894_, v___x_4895_);
                    if v___x_4896_ == 0 {
                        crate::leanh::lean_dec_ref(v_c_4887_);
                        v___x_4897_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4897_, 0, v_____do__lift_4881_);
                        crate::leanh::lean_ctor_set(v___x_4897_, 1, v_i_4882_);
                        crate::leanh::lean_ctor_set(v___x_4897_, 2, v_____do__lift_4883_);
                        crate::leanh::lean_ctor_set(v___x_4897_, 3, v_____do__lift_4889_);
                        v___x_4898_ = crate::leanh::lean_apply_2(
                            v_toPure_4884_,
                            crate::leanh::lean_box(0),
                            v___x_4897_,
                        );
                        return v___x_4898_;
                    } else {
                        v___x_4899_ = lean_ptr_addr(v_k_4886_);
                        v___x_4900_ = lean_ptr_addr(v_____do__lift_4889_);
                        v___x_4901_ = lean_usize_dec_eq(v___x_4899_, v___x_4900_);
                        if v___x_4901_ == 0 {
                            crate::leanh::lean_dec_ref(v_c_4887_);
                            v___x_4902_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4902_, 0, v_____do__lift_4881_);
                            crate::leanh::lean_ctor_set(v___x_4902_, 1, v_i_4882_);
                            crate::leanh::lean_ctor_set(v___x_4902_, 2, v_____do__lift_4883_);
                            crate::leanh::lean_ctor_set(v___x_4902_, 3, v_____do__lift_4889_);
                            v___x_4903_ = crate::leanh::lean_apply_2(
                                v_toPure_4884_,
                                crate::leanh::lean_box(0),
                                v___x_4902_,
                            );
                            return v___x_4903_;
                        } else {
                            crate::leanh::lean_dec_ref(v_____do__lift_4889_);
                            crate::leanh::lean_dec(v_____do__lift_4883_);
                            crate::leanh::lean_dec(v_i_4882_);
                            crate::leanh::lean_dec(v_____do__lift_4881_);
                            v___x_4904_ = crate::leanh::lean_apply_2(
                                v_toPure_4884_,
                                crate::leanh::lean_box(0),
                                v_c_4887_,
                            );
                            return v___x_4904_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed(
    mut v_____do__lift_4909_: *mut crate::leanh::LeanObject,
    mut v_i_4910_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4911_: *mut crate::leanh::LeanObject,
    mut v_toPure_4912_: *mut crate::leanh::LeanObject,
    mut v_y_4913_: *mut crate::leanh::LeanObject,
    mut v_k_4914_: *mut crate::leanh::LeanObject,
    mut v_c_4915_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4916_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20(
        v_____do__lift_4909_,
        v_i_4910_,
        v_____do__lift_4911_,
        v_toPure_4912_,
        v_y_4913_,
        v_k_4914_,
        v_c_4915_,
        v_fvarId_4916_,
        v_____do__lift_4917_,
    );
    crate::leanh::lean_dec(v_fvarId_4916_);
    crate::leanh::lean_dec_ref(v_k_4914_);
    crate::leanh::lean_dec(v_y_4913_);
    return v_res_4918_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(
    mut v_____do__lift_4919_: *mut crate::leanh::LeanObject,
    mut v_toPure_4920_: *mut crate::leanh::LeanObject,
    mut v_c_4921_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4922_: *mut crate::leanh::LeanObject,
    mut v_k_4923_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4926_: u8 = 0;
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: usize = 0;
    let mut v___x_4932_: u8 = 0;
    let mut v___x_4933_: usize = 0;
    let mut v___x_4934_: usize = 0;
    let mut v___x_4935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4930_ = lean_ptr_addr(v_fvarId_4922_);
                v___x_4931_ = lean_ptr_addr(v_____do__lift_4919_);
                v___x_4932_ = lean_usize_dec_eq(v___x_4930_, v___x_4931_);
                if v___x_4932_ == 0 {
                    v___y_4926_ = v___x_4932_;
                    state = 1;
                    continue;
                } else {
                    v___x_4933_ = lean_ptr_addr(v_k_4923_);
                    v___x_4934_ = lean_ptr_addr(v_____do__lift_4924_);
                    v___x_4935_ = lean_usize_dec_eq(v___x_4933_, v___x_4934_);
                    v___y_4926_ = v___x_4935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4926_ == 0 {
                    crate::leanh::lean_dec_ref(v_c_4921_);
                    v___x_4927_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4927_, 0, v_____do__lift_4919_);
                    crate::leanh::lean_ctor_set(v___x_4927_, 1, v_____do__lift_4924_);
                    v___x_4928_ = crate::leanh::lean_apply_2(
                        v_toPure_4920_,
                        crate::leanh::lean_box(0),
                        v___x_4927_,
                    );
                    return v___x_4928_;
                } else {
                    crate::leanh::lean_dec_ref(v_____do__lift_4924_);
                    crate::leanh::lean_dec(v_____do__lift_4919_);
                    v___x_4929_ = crate::leanh::lean_apply_2(
                        v_toPure_4920_,
                        crate::leanh::lean_box(0),
                        v_c_4921_,
                    );
                    return v___x_4929_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed(
    mut v_____do__lift_4936_: *mut crate::leanh::LeanObject,
    mut v_toPure_4937_: *mut crate::leanh::LeanObject,
    mut v_c_4938_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4939_: *mut crate::leanh::LeanObject,
    mut v_k_4940_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4942_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33(
        v_____do__lift_4936_,
        v_toPure_4937_,
        v_c_4938_,
        v_fvarId_4939_,
        v_k_4940_,
        v_____do__lift_4941_,
    );
    crate::leanh::lean_dec_ref(v_k_4940_);
    crate::leanh::lean_dec(v_fvarId_4939_);
    return v_res_4942_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(
    mut v_type_4943_: *mut crate::leanh::LeanObject,
    mut v_toPure_4944_: *mut crate::leanh::LeanObject,
    mut v_c_4945_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4947_: usize = 0;
    let mut v___x_4948_: usize = 0;
    let mut v___x_4949_: u8 = 0;
    v___x_4947_ = lean_ptr_addr(v_type_4943_);
    v___x_4948_ = lean_ptr_addr(v_____do__lift_4946_);
    v___x_4949_ = lean_usize_dec_eq(v___x_4947_, v___x_4948_);
    if v___x_4949_ == 0 {
        let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_c_4945_);
        v___x_4950_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4950_, 0, v_____do__lift_4946_);
        v___x_4951_ =
            crate::leanh::lean_apply_2(v_toPure_4944_, crate::leanh::lean_box(0), v___x_4950_);
        return v___x_4951_;
    } else {
        let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____do__lift_4946_);
        v___x_4952_ =
            crate::leanh::lean_apply_2(v_toPure_4944_, crate::leanh::lean_box(0), v_c_4945_);
        return v___x_4952_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed(
    mut v_type_4953_: *mut crate::leanh::LeanObject,
    mut v_toPure_4954_: *mut crate::leanh::LeanObject,
    mut v_c_4955_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16(
        v_type_4953_,
        v_toPure_4954_,
        v_c_4955_,
        v_____do__lift_4956_,
    );
    crate::leanh::lean_dec_ref(v_type_4953_);
    return v_res_4957_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(
    mut v_toPure_4958_: *mut crate::leanh::LeanObject,
    mut v_c_4959_: *mut crate::leanh::LeanObject,
    mut v_k_4960_: *mut crate::leanh::LeanObject,
    mut v_decl_4961_: *mut crate::leanh::LeanObject,
    mut v_pu_4962_: u8,
    mut v_inst_4963_: *mut crate::leanh::LeanObject,
    mut v_inst_4964_: *mut crate::leanh::LeanObject,
    mut v_f_4965_: *mut crate::leanh::LeanObject,
    mut v_toBind_4966_: *mut crate::leanh::LeanObject,
    mut v_decl_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_4960_);
    v___f_4968_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4968_, 0, v_decl_4967_);
    crate::leanh::lean_closure_set(v___f_4968_, 1, v_toPure_4958_);
    crate::leanh::lean_closure_set(v___f_4968_, 2, v_c_4959_);
    crate::leanh::lean_closure_set(v___f_4968_, 3, v_k_4960_);
    crate::leanh::lean_closure_set(v___f_4968_, 4, v_decl_4961_);
    v___x_4969_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_4962_,
        v_inst_4963_,
        v_inst_4964_,
        v_f_4965_,
        v_k_4960_,
    );
    v___x_4970_ = crate::leanh::lean_apply_4(
        v_toBind_4966_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4969_,
        v___f_4968_,
    );
    return v___x_4970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed(
    mut v_toPure_4971_: *mut crate::leanh::LeanObject,
    mut v_c_4972_: *mut crate::leanh::LeanObject,
    mut v_k_4973_: *mut crate::leanh::LeanObject,
    mut v_decl_4974_: *mut crate::leanh::LeanObject,
    mut v_pu_4975_: *mut crate::leanh::LeanObject,
    mut v_inst_4976_: *mut crate::leanh::LeanObject,
    mut v_inst_4977_: *mut crate::leanh::LeanObject,
    mut v_f_4978_: *mut crate::leanh::LeanObject,
    mut v_toBind_4979_: *mut crate::leanh::LeanObject,
    mut v_decl_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4981_ = (crate::leanh::lean_unbox(v_pu_4975_) as u8);
    v_res_4982_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1(
        v_toPure_4971_,
        v_c_4972_,
        v_k_4973_,
        v_decl_4974_,
        v_pu_boxed_4981_,
        v_inst_4976_,
        v_inst_4977_,
        v_f_4978_,
        v_toBind_4979_,
        v_decl_4980_,
    );
    return v_res_4982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(
    mut v_toPure_4983_: *mut crate::leanh::LeanObject,
    mut v_c_4984_: *mut crate::leanh::LeanObject,
    mut v_k_4985_: *mut crate::leanh::LeanObject,
    mut v_decl_4986_: *mut crate::leanh::LeanObject,
    mut v_pu_4987_: u8,
    mut v_inst_4988_: *mut crate::leanh::LeanObject,
    mut v_inst_4989_: *mut crate::leanh::LeanObject,
    mut v_f_4990_: *mut crate::leanh::LeanObject,
    mut v_toBind_4991_: *mut crate::leanh::LeanObject,
    mut v_decl_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_4985_);
    v___f_4993_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4993_, 0, v_decl_4992_);
    crate::leanh::lean_closure_set(v___f_4993_, 1, v_toPure_4983_);
    crate::leanh::lean_closure_set(v___f_4993_, 2, v_c_4984_);
    crate::leanh::lean_closure_set(v___f_4993_, 3, v_k_4985_);
    crate::leanh::lean_closure_set(v___f_4993_, 4, v_decl_4986_);
    v___x_4994_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_4987_,
        v_inst_4988_,
        v_inst_4989_,
        v_f_4990_,
        v_k_4985_,
    );
    v___x_4995_ = crate::leanh::lean_apply_4(
        v_toBind_4991_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4994_,
        v___f_4993_,
    );
    return v___x_4995_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed(
    mut v_toPure_4996_: *mut crate::leanh::LeanObject,
    mut v_c_4997_: *mut crate::leanh::LeanObject,
    mut v_k_4998_: *mut crate::leanh::LeanObject,
    mut v_decl_4999_: *mut crate::leanh::LeanObject,
    mut v_pu_5000_: *mut crate::leanh::LeanObject,
    mut v_inst_5001_: *mut crate::leanh::LeanObject,
    mut v_inst_5002_: *mut crate::leanh::LeanObject,
    mut v_f_5003_: *mut crate::leanh::LeanObject,
    mut v_toBind_5004_: *mut crate::leanh::LeanObject,
    mut v_decl_5005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5006_: u8 = 0;
    let mut v_res_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5006_ = (crate::leanh::lean_unbox(v_pu_5000_) as u8);
    v_res_5007_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3(
        v_toPure_4996_,
        v_c_4997_,
        v_k_4998_,
        v_decl_4999_,
        v_pu_boxed_5006_,
        v_inst_5001_,
        v_inst_5002_,
        v_f_5003_,
        v_toBind_5004_,
        v_decl_5005_,
    );
    return v_res_5007_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(
    mut v_pu_5008_: u8,
    mut v_decl_5009_: *mut crate::leanh::LeanObject,
    mut v_params_5010_: *mut crate::leanh::LeanObject,
    mut v_inst_5011_: *mut crate::leanh::LeanObject,
    mut v_toBind_5012_: *mut crate::leanh::LeanObject,
    mut v___f_5013_: *mut crate::leanh::LeanObject,
    mut v_inst_5014_: *mut crate::leanh::LeanObject,
    mut v_f_5015_: *mut crate::leanh::LeanObject,
    mut v_value_5016_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5018_ = crate::leanh::lean_box((v_pu_5008_) as usize);
    crate::leanh::lean_inc(v_toBind_5012_);
    crate::leanh::lean_inc(v_inst_5011_);
    v___f_5019_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_5019_, 0, v___x_5018_);
    crate::leanh::lean_closure_set(v___f_5019_, 1, v_decl_5009_);
    crate::leanh::lean_closure_set(v___f_5019_, 2, v_____do__lift_5017_);
    crate::leanh::lean_closure_set(v___f_5019_, 3, v_params_5010_);
    crate::leanh::lean_closure_set(v___f_5019_, 4, v_inst_5011_);
    crate::leanh::lean_closure_set(v___f_5019_, 5, v_toBind_5012_);
    crate::leanh::lean_closure_set(v___f_5019_, 6, v___f_5013_);
    v___x_5020_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5008_,
        v_inst_5011_,
        v_inst_5014_,
        v_f_5015_,
        v_value_5016_,
    );
    v___x_5021_ = crate::leanh::lean_apply_4(
        v_toBind_5012_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5020_,
        v___f_5019_,
    );
    return v___x_5021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed(
    mut v_pu_5022_: *mut crate::leanh::LeanObject,
    mut v_decl_5023_: *mut crate::leanh::LeanObject,
    mut v_params_5024_: *mut crate::leanh::LeanObject,
    mut v_inst_5025_: *mut crate::leanh::LeanObject,
    mut v_toBind_5026_: *mut crate::leanh::LeanObject,
    mut v___f_5027_: *mut crate::leanh::LeanObject,
    mut v_inst_5028_: *mut crate::leanh::LeanObject,
    mut v_f_5029_: *mut crate::leanh::LeanObject,
    mut v_value_5030_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5032_: u8 = 0;
    let mut v_res_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5032_ = (crate::leanh::lean_unbox(v_pu_5022_) as u8);
    v_res_5033_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5(
        v_pu_boxed_5032_,
        v_decl_5023_,
        v_params_5024_,
        v_inst_5025_,
        v_toBind_5026_,
        v___f_5027_,
        v_inst_5028_,
        v_f_5029_,
        v_value_5030_,
        v_____do__lift_5031_,
    );
    return v_res_5033_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(
    mut v_pu_5034_: u8,
    mut v_decl_5035_: *mut crate::leanh::LeanObject,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v_toBind_5037_: *mut crate::leanh::LeanObject,
    mut v___f_5038_: *mut crate::leanh::LeanObject,
    mut v_inst_5039_: *mut crate::leanh::LeanObject,
    mut v_f_5040_: *mut crate::leanh::LeanObject,
    mut v_value_5041_: *mut crate::leanh::LeanObject,
    mut v_type_5042_: *mut crate::leanh::LeanObject,
    mut v_params_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5044_ = crate::leanh::lean_box((v_pu_5034_) as usize);
    crate::leanh::lean_inc(v_f_5040_);
    crate::leanh::lean_inc_ref(v_inst_5039_);
    crate::leanh::lean_inc(v_toBind_5037_);
    v___f_5045_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_5045_, 0, v___x_5044_);
    crate::leanh::lean_closure_set(v___f_5045_, 1, v_decl_5035_);
    crate::leanh::lean_closure_set(v___f_5045_, 2, v_params_5043_);
    crate::leanh::lean_closure_set(v___f_5045_, 3, v_inst_5036_);
    crate::leanh::lean_closure_set(v___f_5045_, 4, v_toBind_5037_);
    crate::leanh::lean_closure_set(v___f_5045_, 5, v___f_5038_);
    crate::leanh::lean_closure_set(v___f_5045_, 6, v_inst_5039_);
    crate::leanh::lean_closure_set(v___f_5045_, 7, v_f_5040_);
    crate::leanh::lean_closure_set(v___f_5045_, 8, v_value_5041_);
    v___x_5046_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5039_, v_f_5040_, v_type_5042_);
    v___x_5047_ = crate::leanh::lean_apply_4(
        v_toBind_5037_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5046_,
        v___f_5045_,
    );
    return v___x_5047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed(
    mut v_pu_5048_: *mut crate::leanh::LeanObject,
    mut v_decl_5049_: *mut crate::leanh::LeanObject,
    mut v_inst_5050_: *mut crate::leanh::LeanObject,
    mut v_toBind_5051_: *mut crate::leanh::LeanObject,
    mut v___f_5052_: *mut crate::leanh::LeanObject,
    mut v_inst_5053_: *mut crate::leanh::LeanObject,
    mut v_f_5054_: *mut crate::leanh::LeanObject,
    mut v_value_5055_: *mut crate::leanh::LeanObject,
    mut v_type_5056_: *mut crate::leanh::LeanObject,
    mut v_params_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5058_ = (crate::leanh::lean_unbox(v_pu_5048_) as u8);
    v_res_5059_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6(
        v_pu_boxed_5058_,
        v_decl_5049_,
        v_inst_5050_,
        v_toBind_5051_,
        v___f_5052_,
        v_inst_5053_,
        v_f_5054_,
        v_value_5055_,
        v_type_5056_,
        v_params_5057_,
    );
    return v_res_5059_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(
    mut v_toPure_5060_: *mut crate::leanh::LeanObject,
    mut v_c_5061_: *mut crate::leanh::LeanObject,
    mut v_k_5062_: *mut crate::leanh::LeanObject,
    mut v_decl_5063_: *mut crate::leanh::LeanObject,
    mut v_pu_5064_: u8,
    mut v_inst_5065_: *mut crate::leanh::LeanObject,
    mut v_inst_5066_: *mut crate::leanh::LeanObject,
    mut v_f_5067_: *mut crate::leanh::LeanObject,
    mut v_toBind_5068_: *mut crate::leanh::LeanObject,
    mut v_decl_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5062_);
    v___f_5070_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5070_, 0, v_decl_5069_);
    crate::leanh::lean_closure_set(v___f_5070_, 1, v_toPure_5060_);
    crate::leanh::lean_closure_set(v___f_5070_, 2, v_c_5061_);
    crate::leanh::lean_closure_set(v___f_5070_, 3, v_k_5062_);
    crate::leanh::lean_closure_set(v___f_5070_, 4, v_decl_5063_);
    v___x_5071_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5064_,
        v_inst_5065_,
        v_inst_5066_,
        v_f_5067_,
        v_k_5062_,
    );
    v___x_5072_ = crate::leanh::lean_apply_4(
        v_toBind_5068_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5071_,
        v___f_5070_,
    );
    return v___x_5072_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed(
    mut v_toPure_5073_: *mut crate::leanh::LeanObject,
    mut v_c_5074_: *mut crate::leanh::LeanObject,
    mut v_k_5075_: *mut crate::leanh::LeanObject,
    mut v_decl_5076_: *mut crate::leanh::LeanObject,
    mut v_pu_5077_: *mut crate::leanh::LeanObject,
    mut v_inst_5078_: *mut crate::leanh::LeanObject,
    mut v_inst_5079_: *mut crate::leanh::LeanObject,
    mut v_f_5080_: *mut crate::leanh::LeanObject,
    mut v_toBind_5081_: *mut crate::leanh::LeanObject,
    mut v_decl_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5083_: u8 = 0;
    let mut v_res_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5083_ = (crate::leanh::lean_unbox(v_pu_5077_) as u8);
    v_res_5084_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8(
        v_toPure_5073_,
        v_c_5074_,
        v_k_5075_,
        v_decl_5076_,
        v_pu_boxed_5083_,
        v_inst_5078_,
        v_inst_5079_,
        v_f_5080_,
        v_toBind_5081_,
        v_decl_5082_,
    );
    return v_res_5084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed(
    mut v_pu_5085_: *mut crate::leanh::LeanObject,
    mut v_inst_5086_: *mut crate::leanh::LeanObject,
    mut v_inst_5087_: *mut crate::leanh::LeanObject,
    mut v_f_5088_: *mut crate::leanh::LeanObject,
    mut v_x_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5090_: u8 = 0;
    let mut v_res_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5090_ = (crate::leanh::lean_unbox(v_pu_5085_) as u8);
    v_res_5091_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(
        v_pu_boxed_5090_,
        v_inst_5086_,
        v_inst_5087_,
        v_f_5088_,
        v_x_5089_,
    );
    return v_res_5091_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(
    mut v_____do__lift_5092_: *mut crate::leanh::LeanObject,
    mut v_i_5093_: *mut crate::leanh::LeanObject,
    mut v_toPure_5094_: *mut crate::leanh::LeanObject,
    mut v_y_5095_: *mut crate::leanh::LeanObject,
    mut v_k_5096_: *mut crate::leanh::LeanObject,
    mut v_c_5097_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5098_: *mut crate::leanh::LeanObject,
    mut v_pu_5099_: u8,
    mut v_inst_5100_: *mut crate::leanh::LeanObject,
    mut v_inst_5101_: *mut crate::leanh::LeanObject,
    mut v_f_5102_: *mut crate::leanh::LeanObject,
    mut v_toBind_5103_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5096_);
    v___f_5105_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__17___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5105_, 0, v_____do__lift_5092_);
    crate::leanh::lean_closure_set(v___f_5105_, 1, v_i_5093_);
    crate::leanh::lean_closure_set(v___f_5105_, 2, v_____do__lift_5104_);
    crate::leanh::lean_closure_set(v___f_5105_, 3, v_toPure_5094_);
    crate::leanh::lean_closure_set(v___f_5105_, 4, v_y_5095_);
    crate::leanh::lean_closure_set(v___f_5105_, 5, v_k_5096_);
    crate::leanh::lean_closure_set(v___f_5105_, 6, v_c_5097_);
    crate::leanh::lean_closure_set(v___f_5105_, 7, v_fvarId_5098_);
    v___x_5106_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5099_,
        v_inst_5100_,
        v_inst_5101_,
        v_f_5102_,
        v_k_5096_,
    );
    v___x_5107_ = crate::leanh::lean_apply_4(
        v_toBind_5103_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5106_,
        v___f_5105_,
    );
    return v___x_5107_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed(
    mut v_____do__lift_5108_: *mut crate::leanh::LeanObject,
    mut v_i_5109_: *mut crate::leanh::LeanObject,
    mut v_toPure_5110_: *mut crate::leanh::LeanObject,
    mut v_y_5111_: *mut crate::leanh::LeanObject,
    mut v_k_5112_: *mut crate::leanh::LeanObject,
    mut v_c_5113_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5114_: *mut crate::leanh::LeanObject,
    mut v_pu_5115_: *mut crate::leanh::LeanObject,
    mut v_inst_5116_: *mut crate::leanh::LeanObject,
    mut v_inst_5117_: *mut crate::leanh::LeanObject,
    mut v_f_5118_: *mut crate::leanh::LeanObject,
    mut v_toBind_5119_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5121_: u8 = 0;
    let mut v_res_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5121_ = (crate::leanh::lean_unbox(v_pu_5115_) as u8);
    v_res_5122_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18(
        v_____do__lift_5108_,
        v_i_5109_,
        v_toPure_5110_,
        v_y_5111_,
        v_k_5112_,
        v_c_5113_,
        v_fvarId_5114_,
        v_pu_boxed_5121_,
        v_inst_5116_,
        v_inst_5117_,
        v_f_5118_,
        v_toBind_5119_,
        v_____do__lift_5120_,
    );
    return v_res_5122_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(
    mut v_i_5123_: *mut crate::leanh::LeanObject,
    mut v_toPure_5124_: *mut crate::leanh::LeanObject,
    mut v_y_5125_: *mut crate::leanh::LeanObject,
    mut v_k_5126_: *mut crate::leanh::LeanObject,
    mut v_c_5127_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5128_: *mut crate::leanh::LeanObject,
    mut v_pu_5129_: u8,
    mut v_inst_5130_: *mut crate::leanh::LeanObject,
    mut v_inst_5131_: *mut crate::leanh::LeanObject,
    mut v_f_5132_: *mut crate::leanh::LeanObject,
    mut v_toBind_5133_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = crate::leanh::lean_box((v_pu_5129_) as usize);
    crate::leanh::lean_inc(v_toBind_5133_);
    crate::leanh::lean_inc(v_f_5132_);
    crate::leanh::lean_inc_ref(v_inst_5131_);
    crate::leanh::lean_inc(v_y_5125_);
    v___f_5136_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__18___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_5136_, 0, v_____do__lift_5134_);
    crate::leanh::lean_closure_set(v___f_5136_, 1, v_i_5123_);
    crate::leanh::lean_closure_set(v___f_5136_, 2, v_toPure_5124_);
    crate::leanh::lean_closure_set(v___f_5136_, 3, v_y_5125_);
    crate::leanh::lean_closure_set(v___f_5136_, 4, v_k_5126_);
    crate::leanh::lean_closure_set(v___f_5136_, 5, v_c_5127_);
    crate::leanh::lean_closure_set(v___f_5136_, 6, v_fvarId_5128_);
    crate::leanh::lean_closure_set(v___f_5136_, 7, v___x_5135_);
    crate::leanh::lean_closure_set(v___f_5136_, 8, v_inst_5130_);
    crate::leanh::lean_closure_set(v___f_5136_, 9, v_inst_5131_);
    crate::leanh::lean_closure_set(v___f_5136_, 10, v_f_5132_);
    crate::leanh::lean_closure_set(v___f_5136_, 11, v_toBind_5133_);
    v___x_5137_ =
        l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_5129_, v_inst_5131_, v_f_5132_, v_y_5125_);
    v___x_5138_ = crate::leanh::lean_apply_4(
        v_toBind_5133_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5137_,
        v___f_5136_,
    );
    return v___x_5138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed(
    mut v_i_5139_: *mut crate::leanh::LeanObject,
    mut v_toPure_5140_: *mut crate::leanh::LeanObject,
    mut v_y_5141_: *mut crate::leanh::LeanObject,
    mut v_k_5142_: *mut crate::leanh::LeanObject,
    mut v_c_5143_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5144_: *mut crate::leanh::LeanObject,
    mut v_pu_5145_: *mut crate::leanh::LeanObject,
    mut v_inst_5146_: *mut crate::leanh::LeanObject,
    mut v_inst_5147_: *mut crate::leanh::LeanObject,
    mut v_f_5148_: *mut crate::leanh::LeanObject,
    mut v_toBind_5149_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5151_: u8 = 0;
    let mut v_res_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5151_ = (crate::leanh::lean_unbox(v_pu_5145_) as u8);
    v_res_5152_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19(
        v_i_5139_,
        v_toPure_5140_,
        v_y_5141_,
        v_k_5142_,
        v_c_5143_,
        v_fvarId_5144_,
        v_pu_boxed_5151_,
        v_inst_5146_,
        v_inst_5147_,
        v_f_5148_,
        v_toBind_5149_,
        v_____do__lift_5150_,
    );
    return v_res_5152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(
    mut v_____do__lift_5153_: *mut crate::leanh::LeanObject,
    mut v_i_5154_: *mut crate::leanh::LeanObject,
    mut v_toPure_5155_: *mut crate::leanh::LeanObject,
    mut v_y_5156_: *mut crate::leanh::LeanObject,
    mut v_k_5157_: *mut crate::leanh::LeanObject,
    mut v_c_5158_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5159_: *mut crate::leanh::LeanObject,
    mut v_pu_5160_: u8,
    mut v_inst_5161_: *mut crate::leanh::LeanObject,
    mut v_inst_5162_: *mut crate::leanh::LeanObject,
    mut v_f_5163_: *mut crate::leanh::LeanObject,
    mut v_toBind_5164_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5157_);
    v___f_5166_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__20___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5166_, 0, v_____do__lift_5153_);
    crate::leanh::lean_closure_set(v___f_5166_, 1, v_i_5154_);
    crate::leanh::lean_closure_set(v___f_5166_, 2, v_____do__lift_5165_);
    crate::leanh::lean_closure_set(v___f_5166_, 3, v_toPure_5155_);
    crate::leanh::lean_closure_set(v___f_5166_, 4, v_y_5156_);
    crate::leanh::lean_closure_set(v___f_5166_, 5, v_k_5157_);
    crate::leanh::lean_closure_set(v___f_5166_, 6, v_c_5158_);
    crate::leanh::lean_closure_set(v___f_5166_, 7, v_fvarId_5159_);
    v___x_5167_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5160_,
        v_inst_5161_,
        v_inst_5162_,
        v_f_5163_,
        v_k_5157_,
    );
    v___x_5168_ = crate::leanh::lean_apply_4(
        v_toBind_5164_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5167_,
        v___f_5166_,
    );
    return v___x_5168_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed(
    mut v_____do__lift_5169_: *mut crate::leanh::LeanObject,
    mut v_i_5170_: *mut crate::leanh::LeanObject,
    mut v_toPure_5171_: *mut crate::leanh::LeanObject,
    mut v_y_5172_: *mut crate::leanh::LeanObject,
    mut v_k_5173_: *mut crate::leanh::LeanObject,
    mut v_c_5174_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5175_: *mut crate::leanh::LeanObject,
    mut v_pu_5176_: *mut crate::leanh::LeanObject,
    mut v_inst_5177_: *mut crate::leanh::LeanObject,
    mut v_inst_5178_: *mut crate::leanh::LeanObject,
    mut v_f_5179_: *mut crate::leanh::LeanObject,
    mut v_toBind_5180_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5182_: u8 = 0;
    let mut v_res_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5182_ = (crate::leanh::lean_unbox(v_pu_5176_) as u8);
    v_res_5183_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21(
        v_____do__lift_5169_,
        v_i_5170_,
        v_toPure_5171_,
        v_y_5172_,
        v_k_5173_,
        v_c_5174_,
        v_fvarId_5175_,
        v_pu_boxed_5182_,
        v_inst_5177_,
        v_inst_5178_,
        v_f_5179_,
        v_toBind_5180_,
        v_____do__lift_5181_,
    );
    return v_res_5183_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(
    mut v_i_5184_: *mut crate::leanh::LeanObject,
    mut v_toPure_5185_: *mut crate::leanh::LeanObject,
    mut v_y_5186_: *mut crate::leanh::LeanObject,
    mut v_k_5187_: *mut crate::leanh::LeanObject,
    mut v_c_5188_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5189_: *mut crate::leanh::LeanObject,
    mut v_pu_5190_: u8,
    mut v_inst_5191_: *mut crate::leanh::LeanObject,
    mut v_inst_5192_: *mut crate::leanh::LeanObject,
    mut v_f_5193_: *mut crate::leanh::LeanObject,
    mut v_toBind_5194_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5196_ = crate::leanh::lean_box((v_pu_5190_) as usize);
    crate::leanh::lean_inc(v_toBind_5194_);
    crate::leanh::lean_inc(v_f_5193_);
    crate::leanh::lean_inc(v_y_5186_);
    v___f_5197_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__21___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_5197_, 0, v_____do__lift_5195_);
    crate::leanh::lean_closure_set(v___f_5197_, 1, v_i_5184_);
    crate::leanh::lean_closure_set(v___f_5197_, 2, v_toPure_5185_);
    crate::leanh::lean_closure_set(v___f_5197_, 3, v_y_5186_);
    crate::leanh::lean_closure_set(v___f_5197_, 4, v_k_5187_);
    crate::leanh::lean_closure_set(v___f_5197_, 5, v_c_5188_);
    crate::leanh::lean_closure_set(v___f_5197_, 6, v_fvarId_5189_);
    crate::leanh::lean_closure_set(v___f_5197_, 7, v___x_5196_);
    crate::leanh::lean_closure_set(v___f_5197_, 8, v_inst_5191_);
    crate::leanh::lean_closure_set(v___f_5197_, 9, v_inst_5192_);
    crate::leanh::lean_closure_set(v___f_5197_, 10, v_f_5193_);
    crate::leanh::lean_closure_set(v___f_5197_, 11, v_toBind_5194_);
    v___x_5198_ = crate::leanh::lean_apply_1(v_f_5193_, v_y_5186_);
    v___x_5199_ = crate::leanh::lean_apply_4(
        v_toBind_5194_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5198_,
        v___f_5197_,
    );
    return v___x_5199_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed(
    mut v_i_5200_: *mut crate::leanh::LeanObject,
    mut v_toPure_5201_: *mut crate::leanh::LeanObject,
    mut v_y_5202_: *mut crate::leanh::LeanObject,
    mut v_k_5203_: *mut crate::leanh::LeanObject,
    mut v_c_5204_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5205_: *mut crate::leanh::LeanObject,
    mut v_pu_5206_: *mut crate::leanh::LeanObject,
    mut v_inst_5207_: *mut crate::leanh::LeanObject,
    mut v_inst_5208_: *mut crate::leanh::LeanObject,
    mut v_f_5209_: *mut crate::leanh::LeanObject,
    mut v_toBind_5210_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5212_: u8 = 0;
    let mut v_res_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5212_ = (crate::leanh::lean_unbox(v_pu_5206_) as u8);
    v_res_5213_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22(
        v_i_5200_,
        v_toPure_5201_,
        v_y_5202_,
        v_k_5203_,
        v_c_5204_,
        v_fvarId_5205_,
        v_pu_boxed_5212_,
        v_inst_5207_,
        v_inst_5208_,
        v_f_5209_,
        v_toBind_5210_,
        v_____do__lift_5211_,
    );
    return v_res_5213_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(
    mut v_____do__lift_5214_: *mut crate::leanh::LeanObject,
    mut v_i_5215_: *mut crate::leanh::LeanObject,
    mut v_offset_5216_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5217_: *mut crate::leanh::LeanObject,
    mut v_toPure_5218_: *mut crate::leanh::LeanObject,
    mut v_y_5219_: *mut crate::leanh::LeanObject,
    mut v_ty_5220_: *mut crate::leanh::LeanObject,
    mut v_k_5221_: *mut crate::leanh::LeanObject,
    mut v_c_5222_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5223_: *mut crate::leanh::LeanObject,
    mut v_pu_5224_: u8,
    mut v_inst_5225_: *mut crate::leanh::LeanObject,
    mut v_inst_5226_: *mut crate::leanh::LeanObject,
    mut v_f_5227_: *mut crate::leanh::LeanObject,
    mut v_toBind_5228_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5221_);
    v___f_5230_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__23___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_5230_, 0, v_____do__lift_5214_);
    crate::leanh::lean_closure_set(v___f_5230_, 1, v_i_5215_);
    crate::leanh::lean_closure_set(v___f_5230_, 2, v_offset_5216_);
    crate::leanh::lean_closure_set(v___f_5230_, 3, v_____do__lift_5217_);
    crate::leanh::lean_closure_set(v___f_5230_, 4, v_____do__lift_5229_);
    crate::leanh::lean_closure_set(v___f_5230_, 5, v_toPure_5218_);
    crate::leanh::lean_closure_set(v___f_5230_, 6, v_y_5219_);
    crate::leanh::lean_closure_set(v___f_5230_, 7, v_ty_5220_);
    crate::leanh::lean_closure_set(v___f_5230_, 8, v_k_5221_);
    crate::leanh::lean_closure_set(v___f_5230_, 9, v_c_5222_);
    crate::leanh::lean_closure_set(v___f_5230_, 10, v_fvarId_5223_);
    v___x_5231_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5224_,
        v_inst_5225_,
        v_inst_5226_,
        v_f_5227_,
        v_k_5221_,
    );
    v___x_5232_ = crate::leanh::lean_apply_4(
        v_toBind_5228_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5231_,
        v___f_5230_,
    );
    return v___x_5232_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed(
    mut v_____do__lift_5233_: *mut crate::leanh::LeanObject,
    mut v_i_5234_: *mut crate::leanh::LeanObject,
    mut v_offset_5235_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5236_: *mut crate::leanh::LeanObject,
    mut v_toPure_5237_: *mut crate::leanh::LeanObject,
    mut v_y_5238_: *mut crate::leanh::LeanObject,
    mut v_ty_5239_: *mut crate::leanh::LeanObject,
    mut v_k_5240_: *mut crate::leanh::LeanObject,
    mut v_c_5241_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5242_: *mut crate::leanh::LeanObject,
    mut v_pu_5243_: *mut crate::leanh::LeanObject,
    mut v_inst_5244_: *mut crate::leanh::LeanObject,
    mut v_inst_5245_: *mut crate::leanh::LeanObject,
    mut v_f_5246_: *mut crate::leanh::LeanObject,
    mut v_toBind_5247_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5249_: u8 = 0;
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5249_ = (crate::leanh::lean_unbox(v_pu_5243_) as u8);
    v_res_5250_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24(
        v_____do__lift_5233_,
        v_i_5234_,
        v_offset_5235_,
        v_____do__lift_5236_,
        v_toPure_5237_,
        v_y_5238_,
        v_ty_5239_,
        v_k_5240_,
        v_c_5241_,
        v_fvarId_5242_,
        v_pu_boxed_5249_,
        v_inst_5244_,
        v_inst_5245_,
        v_f_5246_,
        v_toBind_5247_,
        v_____do__lift_5248_,
    );
    return v_res_5250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(
    mut v_____do__lift_5251_: *mut crate::leanh::LeanObject,
    mut v_i_5252_: *mut crate::leanh::LeanObject,
    mut v_offset_5253_: *mut crate::leanh::LeanObject,
    mut v_toPure_5254_: *mut crate::leanh::LeanObject,
    mut v_y_5255_: *mut crate::leanh::LeanObject,
    mut v_ty_5256_: *mut crate::leanh::LeanObject,
    mut v_k_5257_: *mut crate::leanh::LeanObject,
    mut v_c_5258_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5259_: *mut crate::leanh::LeanObject,
    mut v_pu_5260_: u8,
    mut v_inst_5261_: *mut crate::leanh::LeanObject,
    mut v_inst_5262_: *mut crate::leanh::LeanObject,
    mut v_f_5263_: *mut crate::leanh::LeanObject,
    mut v_toBind_5264_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5266_ = crate::leanh::lean_box((v_pu_5260_) as usize);
    crate::leanh::lean_inc(v_toBind_5264_);
    crate::leanh::lean_inc(v_f_5263_);
    crate::leanh::lean_inc_ref(v_inst_5262_);
    crate::leanh::lean_inc_ref(v_ty_5256_);
    v___f_5267_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__24___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_5267_, 0, v_____do__lift_5251_);
    crate::leanh::lean_closure_set(v___f_5267_, 1, v_i_5252_);
    crate::leanh::lean_closure_set(v___f_5267_, 2, v_offset_5253_);
    crate::leanh::lean_closure_set(v___f_5267_, 3, v_____do__lift_5265_);
    crate::leanh::lean_closure_set(v___f_5267_, 4, v_toPure_5254_);
    crate::leanh::lean_closure_set(v___f_5267_, 5, v_y_5255_);
    crate::leanh::lean_closure_set(v___f_5267_, 6, v_ty_5256_);
    crate::leanh::lean_closure_set(v___f_5267_, 7, v_k_5257_);
    crate::leanh::lean_closure_set(v___f_5267_, 8, v_c_5258_);
    crate::leanh::lean_closure_set(v___f_5267_, 9, v_fvarId_5259_);
    crate::leanh::lean_closure_set(v___f_5267_, 10, v___x_5266_);
    crate::leanh::lean_closure_set(v___f_5267_, 11, v_inst_5261_);
    crate::leanh::lean_closure_set(v___f_5267_, 12, v_inst_5262_);
    crate::leanh::lean_closure_set(v___f_5267_, 13, v_f_5263_);
    crate::leanh::lean_closure_set(v___f_5267_, 14, v_toBind_5264_);
    v___x_5268_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5262_, v_f_5263_, v_ty_5256_);
    v___x_5269_ = crate::leanh::lean_apply_4(
        v_toBind_5264_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5268_,
        v___f_5267_,
    );
    return v___x_5269_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed(
    mut v_____do__lift_5270_: *mut crate::leanh::LeanObject,
    mut v_i_5271_: *mut crate::leanh::LeanObject,
    mut v_offset_5272_: *mut crate::leanh::LeanObject,
    mut v_toPure_5273_: *mut crate::leanh::LeanObject,
    mut v_y_5274_: *mut crate::leanh::LeanObject,
    mut v_ty_5275_: *mut crate::leanh::LeanObject,
    mut v_k_5276_: *mut crate::leanh::LeanObject,
    mut v_c_5277_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5278_: *mut crate::leanh::LeanObject,
    mut v_pu_5279_: *mut crate::leanh::LeanObject,
    mut v_inst_5280_: *mut crate::leanh::LeanObject,
    mut v_inst_5281_: *mut crate::leanh::LeanObject,
    mut v_f_5282_: *mut crate::leanh::LeanObject,
    mut v_toBind_5283_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5285_: u8 = 0;
    let mut v_res_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5285_ = (crate::leanh::lean_unbox(v_pu_5279_) as u8);
    v_res_5286_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25(
        v_____do__lift_5270_,
        v_i_5271_,
        v_offset_5272_,
        v_toPure_5273_,
        v_y_5274_,
        v_ty_5275_,
        v_k_5276_,
        v_c_5277_,
        v_fvarId_5278_,
        v_pu_boxed_5285_,
        v_inst_5280_,
        v_inst_5281_,
        v_f_5282_,
        v_toBind_5283_,
        v_____do__lift_5284_,
    );
    return v_res_5286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(
    mut v_i_5287_: *mut crate::leanh::LeanObject,
    mut v_offset_5288_: *mut crate::leanh::LeanObject,
    mut v_toPure_5289_: *mut crate::leanh::LeanObject,
    mut v_y_5290_: *mut crate::leanh::LeanObject,
    mut v_ty_5291_: *mut crate::leanh::LeanObject,
    mut v_k_5292_: *mut crate::leanh::LeanObject,
    mut v_c_5293_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5294_: *mut crate::leanh::LeanObject,
    mut v_pu_5295_: u8,
    mut v_inst_5296_: *mut crate::leanh::LeanObject,
    mut v_inst_5297_: *mut crate::leanh::LeanObject,
    mut v_f_5298_: *mut crate::leanh::LeanObject,
    mut v_toBind_5299_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5301_ = crate::leanh::lean_box((v_pu_5295_) as usize);
    crate::leanh::lean_inc(v_toBind_5299_);
    crate::leanh::lean_inc(v_f_5298_);
    crate::leanh::lean_inc(v_y_5290_);
    v___f_5302_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__25___boxed as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_5302_, 0, v_____do__lift_5300_);
    crate::leanh::lean_closure_set(v___f_5302_, 1, v_i_5287_);
    crate::leanh::lean_closure_set(v___f_5302_, 2, v_offset_5288_);
    crate::leanh::lean_closure_set(v___f_5302_, 3, v_toPure_5289_);
    crate::leanh::lean_closure_set(v___f_5302_, 4, v_y_5290_);
    crate::leanh::lean_closure_set(v___f_5302_, 5, v_ty_5291_);
    crate::leanh::lean_closure_set(v___f_5302_, 6, v_k_5292_);
    crate::leanh::lean_closure_set(v___f_5302_, 7, v_c_5293_);
    crate::leanh::lean_closure_set(v___f_5302_, 8, v_fvarId_5294_);
    crate::leanh::lean_closure_set(v___f_5302_, 9, v___x_5301_);
    crate::leanh::lean_closure_set(v___f_5302_, 10, v_inst_5296_);
    crate::leanh::lean_closure_set(v___f_5302_, 11, v_inst_5297_);
    crate::leanh::lean_closure_set(v___f_5302_, 12, v_f_5298_);
    crate::leanh::lean_closure_set(v___f_5302_, 13, v_toBind_5299_);
    v___x_5303_ = crate::leanh::lean_apply_1(v_f_5298_, v_y_5290_);
    v___x_5304_ = crate::leanh::lean_apply_4(
        v_toBind_5299_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5303_,
        v___f_5302_,
    );
    return v___x_5304_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed(
    mut v_i_5305_: *mut crate::leanh::LeanObject,
    mut v_offset_5306_: *mut crate::leanh::LeanObject,
    mut v_toPure_5307_: *mut crate::leanh::LeanObject,
    mut v_y_5308_: *mut crate::leanh::LeanObject,
    mut v_ty_5309_: *mut crate::leanh::LeanObject,
    mut v_k_5310_: *mut crate::leanh::LeanObject,
    mut v_c_5311_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5312_: *mut crate::leanh::LeanObject,
    mut v_pu_5313_: *mut crate::leanh::LeanObject,
    mut v_inst_5314_: *mut crate::leanh::LeanObject,
    mut v_inst_5315_: *mut crate::leanh::LeanObject,
    mut v_f_5316_: *mut crate::leanh::LeanObject,
    mut v_toBind_5317_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5319_: u8 = 0;
    let mut v_res_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5319_ = (crate::leanh::lean_unbox(v_pu_5313_) as u8);
    v_res_5320_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26(
        v_i_5305_,
        v_offset_5306_,
        v_toPure_5307_,
        v_y_5308_,
        v_ty_5309_,
        v_k_5310_,
        v_c_5311_,
        v_fvarId_5312_,
        v_pu_boxed_5319_,
        v_inst_5314_,
        v_inst_5315_,
        v_f_5316_,
        v_toBind_5317_,
        v_____do__lift_5318_,
    );
    return v_res_5320_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(
    mut v_cidx_5321_: *mut crate::leanh::LeanObject,
    mut v_toPure_5322_: *mut crate::leanh::LeanObject,
    mut v_k_5323_: *mut crate::leanh::LeanObject,
    mut v_c_5324_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5325_: *mut crate::leanh::LeanObject,
    mut v_pu_5326_: u8,
    mut v_inst_5327_: *mut crate::leanh::LeanObject,
    mut v_inst_5328_: *mut crate::leanh::LeanObject,
    mut v_f_5329_: *mut crate::leanh::LeanObject,
    mut v_toBind_5330_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5323_);
    v___f_5332_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__27___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5332_, 0, v_____do__lift_5331_);
    crate::leanh::lean_closure_set(v___f_5332_, 1, v_cidx_5321_);
    crate::leanh::lean_closure_set(v___f_5332_, 2, v_toPure_5322_);
    crate::leanh::lean_closure_set(v___f_5332_, 3, v_k_5323_);
    crate::leanh::lean_closure_set(v___f_5332_, 4, v_c_5324_);
    crate::leanh::lean_closure_set(v___f_5332_, 5, v_fvarId_5325_);
    v___x_5333_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5326_,
        v_inst_5327_,
        v_inst_5328_,
        v_f_5329_,
        v_k_5323_,
    );
    v___x_5334_ = crate::leanh::lean_apply_4(
        v_toBind_5330_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5333_,
        v___f_5332_,
    );
    return v___x_5334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed(
    mut v_cidx_5335_: *mut crate::leanh::LeanObject,
    mut v_toPure_5336_: *mut crate::leanh::LeanObject,
    mut v_k_5337_: *mut crate::leanh::LeanObject,
    mut v_c_5338_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5339_: *mut crate::leanh::LeanObject,
    mut v_pu_5340_: *mut crate::leanh::LeanObject,
    mut v_inst_5341_: *mut crate::leanh::LeanObject,
    mut v_inst_5342_: *mut crate::leanh::LeanObject,
    mut v_f_5343_: *mut crate::leanh::LeanObject,
    mut v_toBind_5344_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5346_: u8 = 0;
    let mut v_res_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5346_ = (crate::leanh::lean_unbox(v_pu_5340_) as u8);
    v_res_5347_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28(
        v_cidx_5335_,
        v_toPure_5336_,
        v_k_5337_,
        v_c_5338_,
        v_fvarId_5339_,
        v_pu_boxed_5346_,
        v_inst_5341_,
        v_inst_5342_,
        v_f_5343_,
        v_toBind_5344_,
        v_____do__lift_5345_,
    );
    return v_res_5347_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(
    mut v_n_5348_: *mut crate::leanh::LeanObject,
    mut v_check_5349_: u8,
    mut v_persistent_5350_: u8,
    mut v_toPure_5351_: *mut crate::leanh::LeanObject,
    mut v_k_5352_: *mut crate::leanh::LeanObject,
    mut v_c_5353_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5354_: *mut crate::leanh::LeanObject,
    mut v_pu_5355_: u8,
    mut v_inst_5356_: *mut crate::leanh::LeanObject,
    mut v_inst_5357_: *mut crate::leanh::LeanObject,
    mut v_f_5358_: *mut crate::leanh::LeanObject,
    mut v_toBind_5359_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5361_ = crate::leanh::lean_box((v_check_5349_) as usize);
    v___x_5362_ = crate::leanh::lean_box((v_persistent_5350_) as usize);
    crate::leanh::lean_inc_ref(v_k_5352_);
    v___f_5363_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__29___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5363_, 0, v_____do__lift_5360_);
    crate::leanh::lean_closure_set(v___f_5363_, 1, v_n_5348_);
    crate::leanh::lean_closure_set(v___f_5363_, 2, v___x_5361_);
    crate::leanh::lean_closure_set(v___f_5363_, 3, v___x_5362_);
    crate::leanh::lean_closure_set(v___f_5363_, 4, v_toPure_5351_);
    crate::leanh::lean_closure_set(v___f_5363_, 5, v_k_5352_);
    crate::leanh::lean_closure_set(v___f_5363_, 6, v_c_5353_);
    crate::leanh::lean_closure_set(v___f_5363_, 7, v_fvarId_5354_);
    v___x_5364_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5355_,
        v_inst_5356_,
        v_inst_5357_,
        v_f_5358_,
        v_k_5352_,
    );
    v___x_5365_ = crate::leanh::lean_apply_4(
        v_toBind_5359_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5364_,
        v___f_5363_,
    );
    return v___x_5365_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed(
    mut v_n_5366_: *mut crate::leanh::LeanObject,
    mut v_check_5367_: *mut crate::leanh::LeanObject,
    mut v_persistent_5368_: *mut crate::leanh::LeanObject,
    mut v_toPure_5369_: *mut crate::leanh::LeanObject,
    mut v_k_5370_: *mut crate::leanh::LeanObject,
    mut v_c_5371_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5372_: *mut crate::leanh::LeanObject,
    mut v_pu_5373_: *mut crate::leanh::LeanObject,
    mut v_inst_5374_: *mut crate::leanh::LeanObject,
    mut v_inst_5375_: *mut crate::leanh::LeanObject,
    mut v_f_5376_: *mut crate::leanh::LeanObject,
    mut v_toBind_5377_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_2471__boxed_5379_: u8 = 0;
    let mut v_persistent_2472__boxed_5380_: u8 = 0;
    let mut v_pu_boxed_5381_: u8 = 0;
    let mut v_res_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_2471__boxed_5379_ = (crate::leanh::lean_unbox(v_check_5367_) as u8);
    v_persistent_2472__boxed_5380_ = (crate::leanh::lean_unbox(v_persistent_5368_) as u8);
    v_pu_boxed_5381_ = (crate::leanh::lean_unbox(v_pu_5373_) as u8);
    v_res_5382_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30(
        v_n_5366_,
        v_check_2471__boxed_5379_,
        v_persistent_2472__boxed_5380_,
        v_toPure_5369_,
        v_k_5370_,
        v_c_5371_,
        v_fvarId_5372_,
        v_pu_boxed_5381_,
        v_inst_5374_,
        v_inst_5375_,
        v_f_5376_,
        v_toBind_5377_,
        v_____do__lift_5378_,
    );
    return v_res_5382_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(
    mut v_n_5383_: *mut crate::leanh::LeanObject,
    mut v_check_5384_: u8,
    mut v_persistent_5385_: u8,
    mut v_objs_x3f_5386_: *mut crate::leanh::LeanObject,
    mut v_toPure_5387_: *mut crate::leanh::LeanObject,
    mut v_k_5388_: *mut crate::leanh::LeanObject,
    mut v_c_5389_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5390_: *mut crate::leanh::LeanObject,
    mut v_pu_5391_: u8,
    mut v_inst_5392_: *mut crate::leanh::LeanObject,
    mut v_inst_5393_: *mut crate::leanh::LeanObject,
    mut v_f_5394_: *mut crate::leanh::LeanObject,
    mut v_toBind_5395_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5397_ = crate::leanh::lean_box((v_check_5384_) as usize);
    v___x_5398_ = crate::leanh::lean_box((v_persistent_5385_) as usize);
    crate::leanh::lean_inc_ref(v_k_5388_);
    v___f_5399_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__31___boxed as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_5399_, 0, v_____do__lift_5396_);
    crate::leanh::lean_closure_set(v___f_5399_, 1, v_n_5383_);
    crate::leanh::lean_closure_set(v___f_5399_, 2, v___x_5397_);
    crate::leanh::lean_closure_set(v___f_5399_, 3, v___x_5398_);
    crate::leanh::lean_closure_set(v___f_5399_, 4, v_objs_x3f_5386_);
    crate::leanh::lean_closure_set(v___f_5399_, 5, v_toPure_5387_);
    crate::leanh::lean_closure_set(v___f_5399_, 6, v_k_5388_);
    crate::leanh::lean_closure_set(v___f_5399_, 7, v_c_5389_);
    crate::leanh::lean_closure_set(v___f_5399_, 8, v_fvarId_5390_);
    v___x_5400_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5391_,
        v_inst_5392_,
        v_inst_5393_,
        v_f_5394_,
        v_k_5388_,
    );
    v___x_5401_ = crate::leanh::lean_apply_4(
        v_toBind_5395_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5400_,
        v___f_5399_,
    );
    return v___x_5401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed(
    mut v_n_5402_: *mut crate::leanh::LeanObject,
    mut v_check_5403_: *mut crate::leanh::LeanObject,
    mut v_persistent_5404_: *mut crate::leanh::LeanObject,
    mut v_objs_x3f_5405_: *mut crate::leanh::LeanObject,
    mut v_toPure_5406_: *mut crate::leanh::LeanObject,
    mut v_k_5407_: *mut crate::leanh::LeanObject,
    mut v_c_5408_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5409_: *mut crate::leanh::LeanObject,
    mut v_pu_5410_: *mut crate::leanh::LeanObject,
    mut v_inst_5411_: *mut crate::leanh::LeanObject,
    mut v_inst_5412_: *mut crate::leanh::LeanObject,
    mut v_f_5413_: *mut crate::leanh::LeanObject,
    mut v_toBind_5414_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_2482__boxed_5416_: u8 = 0;
    let mut v_persistent_2483__boxed_5417_: u8 = 0;
    let mut v_pu_boxed_5418_: u8 = 0;
    let mut v_res_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_2482__boxed_5416_ = (crate::leanh::lean_unbox(v_check_5403_) as u8);
    v_persistent_2483__boxed_5417_ = (crate::leanh::lean_unbox(v_persistent_5404_) as u8);
    v_pu_boxed_5418_ = (crate::leanh::lean_unbox(v_pu_5410_) as u8);
    v_res_5419_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32(
        v_n_5402_,
        v_check_2482__boxed_5416_,
        v_persistent_2483__boxed_5417_,
        v_objs_x3f_5405_,
        v_toPure_5406_,
        v_k_5407_,
        v_c_5408_,
        v_fvarId_5409_,
        v_pu_boxed_5418_,
        v_inst_5411_,
        v_inst_5412_,
        v_f_5413_,
        v_toBind_5414_,
        v_____do__lift_5415_,
    );
    return v_res_5419_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(
    mut v_toPure_5420_: *mut crate::leanh::LeanObject,
    mut v_c_5421_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5422_: *mut crate::leanh::LeanObject,
    mut v_k_5423_: *mut crate::leanh::LeanObject,
    mut v_pu_5424_: u8,
    mut v_inst_5425_: *mut crate::leanh::LeanObject,
    mut v_inst_5426_: *mut crate::leanh::LeanObject,
    mut v_f_5427_: *mut crate::leanh::LeanObject,
    mut v_toBind_5428_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_k_5423_);
    v___f_5430_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__33___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5430_, 0, v_____do__lift_5429_);
    crate::leanh::lean_closure_set(v___f_5430_, 1, v_toPure_5420_);
    crate::leanh::lean_closure_set(v___f_5430_, 2, v_c_5421_);
    crate::leanh::lean_closure_set(v___f_5430_, 3, v_fvarId_5422_);
    crate::leanh::lean_closure_set(v___f_5430_, 4, v_k_5423_);
    v___x_5431_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5424_,
        v_inst_5425_,
        v_inst_5426_,
        v_f_5427_,
        v_k_5423_,
    );
    v___x_5432_ = crate::leanh::lean_apply_4(
        v_toBind_5428_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5431_,
        v___f_5430_,
    );
    return v___x_5432_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed(
    mut v_toPure_5433_: *mut crate::leanh::LeanObject,
    mut v_c_5434_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5435_: *mut crate::leanh::LeanObject,
    mut v_k_5436_: *mut crate::leanh::LeanObject,
    mut v_pu_5437_: *mut crate::leanh::LeanObject,
    mut v_inst_5438_: *mut crate::leanh::LeanObject,
    mut v_inst_5439_: *mut crate::leanh::LeanObject,
    mut v_f_5440_: *mut crate::leanh::LeanObject,
    mut v_toBind_5441_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5443_: u8 = 0;
    let mut v_res_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5443_ = (crate::leanh::lean_unbox(v_pu_5437_) as u8);
    v_res_5444_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34(
        v_toPure_5433_,
        v_c_5434_,
        v_fvarId_5435_,
        v_k_5436_,
        v_pu_boxed_5443_,
        v_inst_5438_,
        v_inst_5439_,
        v_f_5440_,
        v_toBind_5441_,
        v_____do__lift_5442_,
    );
    return v_res_5444_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
    mut v_pu_5445_: u8,
    mut v_inst_5446_: *mut crate::leanh::LeanObject,
    mut v_inst_5447_: *mut crate::leanh::LeanObject,
    mut v_f_5448_: *mut crate::leanh::LeanObject,
    mut v_c_5449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_c_5449_) {
        0 => {
            let mut v_toApplicative_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5450_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5451_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5451_, 2);
            v_toPure_5452_ = crate::leanh::lean_ctor_get(v_toApplicative_5450_, 1);
            v_decl_5453_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_ref_n(v_decl_5453_, 2);
            v_k_5454_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc_ref(v_k_5454_);
            v___x_5455_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            crate::leanh::lean_inc_ref(v_inst_5447_);
            crate::leanh::lean_inc(v_inst_5446_);
            crate::leanh::lean_inc(v_toPure_5452_);
            v___f_5456_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__1___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5456_, 0, v_toPure_5452_);
            crate::leanh::lean_closure_set(v___f_5456_, 1, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5456_, 2, v_k_5454_);
            crate::leanh::lean_closure_set(v___f_5456_, 3, v_decl_5453_);
            crate::leanh::lean_closure_set(v___f_5456_, 4, v___x_5455_);
            crate::leanh::lean_closure_set(v___f_5456_, 5, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5456_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5456_, 7, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5456_, 8, v_toBind_5451_);
            v___x_5457_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
                v_pu_5445_,
                v_inst_5446_,
                v_inst_5447_,
                v_f_5448_,
                v_decl_5453_,
            );
            v___x_5458_ = crate::leanh::lean_apply_4(
                v_toBind_5451_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5457_,
                v___f_5456_,
            );
            return v___x_5458_;
        }
        1 => {
            let mut v_toApplicative_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_5473_: usize = 0;
            let mut v___x_5474_: usize = 0;
            let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5459_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_decl_5460_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_ref_n(v_decl_5460_, 2);
            v_toBind_5461_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5461_, 3);
            v_toPure_5462_ = crate::leanh::lean_ctor_get(v_toApplicative_5459_, 1);
            v_k_5463_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc_ref(v_k_5463_);
            v_params_5464_ = crate::leanh::lean_ctor_get(v_decl_5460_, 2);
            crate::leanh::lean_inc_ref(v_params_5464_);
            v_type_5465_ = crate::leanh::lean_ctor_get(v_decl_5460_, 3);
            crate::leanh::lean_inc_ref(v_type_5465_);
            v_value_5466_ = crate::leanh::lean_ctor_get(v_decl_5460_, 4);
            crate::leanh::lean_inc_ref(v_value_5466_);
            v___x_5467_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc_n(v_f_5448_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_5447_, 3);
            crate::leanh::lean_inc_n(v_inst_5446_, 2);
            crate::leanh::lean_inc(v_toPure_5462_);
            v___f_5468_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__3___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5468_, 0, v_toPure_5462_);
            crate::leanh::lean_closure_set(v___f_5468_, 1, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5468_, 2, v_k_5463_);
            crate::leanh::lean_closure_set(v___f_5468_, 3, v_decl_5460_);
            crate::leanh::lean_closure_set(v___f_5468_, 4, v___x_5467_);
            crate::leanh::lean_closure_set(v___f_5468_, 5, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5468_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5468_, 7, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5468_, 8, v_toBind_5461_);
            v___x_5469_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            v___f_5470_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5470_, 0, v___x_5469_);
            crate::leanh::lean_closure_set(v___f_5470_, 1, v_decl_5460_);
            crate::leanh::lean_closure_set(v___f_5470_, 2, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5470_, 3, v_toBind_5461_);
            crate::leanh::lean_closure_set(v___f_5470_, 4, v___f_5468_);
            crate::leanh::lean_closure_set(v___f_5470_, 5, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5470_, 6, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5470_, 7, v_value_5466_);
            crate::leanh::lean_closure_set(v___f_5470_, 8, v_type_5465_);
            v___x_5471_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            v___x_5472_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___x_5472_, 0, crate::leanh::lean_box(0));
            crate::leanh::lean_closure_set(v___x_5472_, 1, v___x_5471_);
            crate::leanh::lean_closure_set(v___x_5472_, 2, v_inst_5446_);
            crate::leanh::lean_closure_set(v___x_5472_, 3, v_inst_5447_);
            crate::leanh::lean_closure_set(v___x_5472_, 4, v_f_5448_);
            v_sz_5473_ = lean_array_size(v_params_5464_);
            v___x_5474_ = 0usize;
            v___x_5475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5447_,
                v___x_5472_,
                v_sz_5473_,
                v___x_5474_,
                v_params_5464_,
            );
            v___x_5476_ = crate::leanh::lean_apply_4(
                v_toBind_5461_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5475_,
                v___f_5470_,
            );
            return v___x_5476_;
        }
        2 => {
            let mut v_toApplicative_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_5491_: usize = 0;
            let mut v___x_5492_: usize = 0;
            let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5477_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_decl_5478_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_ref_n(v_decl_5478_, 2);
            v_toBind_5479_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5479_, 3);
            v_toPure_5480_ = crate::leanh::lean_ctor_get(v_toApplicative_5477_, 1);
            v_k_5481_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc_ref(v_k_5481_);
            v_params_5482_ = crate::leanh::lean_ctor_get(v_decl_5478_, 2);
            crate::leanh::lean_inc_ref(v_params_5482_);
            v_type_5483_ = crate::leanh::lean_ctor_get(v_decl_5478_, 3);
            crate::leanh::lean_inc_ref(v_type_5483_);
            v_value_5484_ = crate::leanh::lean_ctor_get(v_decl_5478_, 4);
            crate::leanh::lean_inc_ref(v_value_5484_);
            v___x_5485_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc_n(v_f_5448_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_5447_, 3);
            crate::leanh::lean_inc_n(v_inst_5446_, 2);
            crate::leanh::lean_inc(v_toPure_5480_);
            v___f_5486_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__8___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5486_, 0, v_toPure_5480_);
            crate::leanh::lean_closure_set(v___f_5486_, 1, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5486_, 2, v_k_5481_);
            crate::leanh::lean_closure_set(v___f_5486_, 3, v_decl_5478_);
            crate::leanh::lean_closure_set(v___f_5486_, 4, v___x_5485_);
            crate::leanh::lean_closure_set(v___f_5486_, 5, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5486_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5486_, 7, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5486_, 8, v_toBind_5479_);
            v___x_5487_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            v___f_5488_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__6___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5488_, 0, v___x_5487_);
            crate::leanh::lean_closure_set(v___f_5488_, 1, v_decl_5478_);
            crate::leanh::lean_closure_set(v___f_5488_, 2, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5488_, 3, v_toBind_5479_);
            crate::leanh::lean_closure_set(v___f_5488_, 4, v___f_5486_);
            crate::leanh::lean_closure_set(v___f_5488_, 5, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5488_, 6, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5488_, 7, v_value_5484_);
            crate::leanh::lean_closure_set(v___f_5488_, 8, v_type_5483_);
            v___x_5489_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            v___x_5490_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___x_5490_, 0, crate::leanh::lean_box(0));
            crate::leanh::lean_closure_set(v___x_5490_, 1, v___x_5489_);
            crate::leanh::lean_closure_set(v___x_5490_, 2, v_inst_5446_);
            crate::leanh::lean_closure_set(v___x_5490_, 3, v_inst_5447_);
            crate::leanh::lean_closure_set(v___x_5490_, 4, v_f_5448_);
            v_sz_5491_ = lean_array_size(v_params_5482_);
            v___x_5492_ = 0usize;
            v___x_5493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5447_,
                v___x_5490_,
                v_sz_5491_,
                v___x_5492_,
                v_params_5482_,
            );
            v___x_5494_ = crate::leanh::lean_apply_4(
                v_toBind_5479_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5493_,
                v___f_5488_,
            );
            return v___x_5494_;
        }
        3 => {
            let mut v_toApplicative_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5495_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5496_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5496_, 2);
            v_toPure_5497_ = crate::leanh::lean_ctor_get(v_toApplicative_5495_, 1);
            crate::leanh::lean_inc(v_toPure_5497_);
            v_fvarId_5498_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5498_, 2);
            v_args_5499_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc_ref(v_args_5499_);
            v___x_5500_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5501_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__9___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5501_, 0, v_toPure_5497_);
            crate::leanh::lean_closure_set(v___f_5501_, 1, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5501_, 2, v_fvarId_5498_);
            crate::leanh::lean_closure_set(v___f_5501_, 3, v_args_5499_);
            crate::leanh::lean_closure_set(v___f_5501_, 4, v___x_5500_);
            crate::leanh::lean_closure_set(v___f_5501_, 5, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5501_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5501_, 7, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5501_, 8, v_toBind_5496_);
            v___x_5502_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5498_);
            v___x_5503_ = crate::leanh::lean_apply_4(
                v_toBind_5496_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5502_,
                v___f_5501_,
            );
            return v___x_5503_;
        }
        4 => {
            let mut v_toApplicative_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cases_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_typeName_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_resultType_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_discr_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_alts_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5504_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_cases_5505_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            v_toBind_5506_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5506_, 2);
            v_toPure_5507_ = crate::leanh::lean_ctor_get(v_toApplicative_5504_, 1);
            v_typeName_5508_ = crate::leanh::lean_ctor_get(v_cases_5505_, 0);
            crate::leanh::lean_inc(v_typeName_5508_);
            v_resultType_5509_ = crate::leanh::lean_ctor_get(v_cases_5505_, 1);
            crate::leanh::lean_inc_ref_n(v_resultType_5509_, 2);
            v_discr_5510_ = crate::leanh::lean_ctor_get(v_cases_5505_, 2);
            crate::leanh::lean_inc(v_discr_5510_);
            v_alts_5511_ = crate::leanh::lean_ctor_get(v_cases_5505_, 3);
            crate::leanh::lean_inc_ref(v_alts_5511_);
            v___x_5512_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc_n(v_f_5448_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_5447_, 2);
            v___f_5513_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10___boxed
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5513_, 0, v___x_5512_);
            crate::leanh::lean_closure_set(v___f_5513_, 1, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5513_, 2, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5513_, 3, v_f_5448_);
            crate::leanh::lean_inc(v_toPure_5507_);
            v___f_5514_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__14 as *mut core::ffi::c_void,
                11,
                10,
            );
            crate::leanh::lean_closure_set(v___f_5514_, 0, v_typeName_5508_);
            crate::leanh::lean_closure_set(v___f_5514_, 1, v_toPure_5507_);
            crate::leanh::lean_closure_set(v___f_5514_, 2, v_discr_5510_);
            crate::leanh::lean_closure_set(v___f_5514_, 3, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5514_, 4, v_alts_5511_);
            crate::leanh::lean_closure_set(v___f_5514_, 5, v_resultType_5509_);
            crate::leanh::lean_closure_set(v___f_5514_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5514_, 7, v___f_5513_);
            crate::leanh::lean_closure_set(v___f_5514_, 8, v_toBind_5506_);
            crate::leanh::lean_closure_set(v___f_5514_, 9, v_f_5448_);
            v___x_5515_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(
                v_inst_5447_,
                v_f_5448_,
                v_resultType_5509_,
            );
            v___x_5516_ = crate::leanh::lean_apply_4(
                v_toBind_5506_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5515_,
                v___f_5514_,
            );
            return v___x_5516_;
        }
        5 => {
            let mut v_toApplicative_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5517_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_5517_);
            crate::leanh::lean_dec(v_inst_5446_);
            v_toBind_5518_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc(v_toBind_5518_);
            crate::leanh::lean_dec_ref(v_inst_5447_);
            v_toPure_5519_ = crate::leanh::lean_ctor_get(v_toApplicative_5517_, 1);
            crate::leanh::lean_inc(v_toPure_5519_);
            crate::leanh::lean_dec_ref(v_toApplicative_5517_);
            v_fvarId_5520_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5520_, 2);
            v___f_5521_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__15___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5521_, 0, v_fvarId_5520_);
            crate::leanh::lean_closure_set(v___f_5521_, 1, v_toPure_5519_);
            crate::leanh::lean_closure_set(v___f_5521_, 2, v_c_5449_);
            v___x_5522_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5520_);
            v___x_5523_ = crate::leanh::lean_apply_4(
                v_toBind_5518_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5522_,
                v___f_5521_,
            );
            return v___x_5523_;
        }
        6 => {
            let mut v_toApplicative_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5524_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            crate::leanh::lean_dec(v_inst_5446_);
            v_toBind_5525_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc(v_toBind_5525_);
            v_toPure_5526_ = crate::leanh::lean_ctor_get(v_toApplicative_5524_, 1);
            v_type_5527_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_ref_n(v_type_5527_, 2);
            crate::leanh::lean_inc(v_toPure_5526_);
            v___f_5528_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__16___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5528_, 0, v_type_5527_);
            crate::leanh::lean_closure_set(v___f_5528_, 1, v_toPure_5526_);
            crate::leanh::lean_closure_set(v___f_5528_, 2, v_c_5449_);
            v___x_5529_ =
                l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5447_, v_f_5448_, v_type_5527_);
            v___x_5530_ = crate::leanh::lean_apply_4(
                v_toBind_5525_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5529_,
                v___f_5528_,
            );
            return v___x_5530_;
        }
        7 => {
            let mut v_toApplicative_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5531_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5532_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5532_, 2);
            v_toPure_5533_ = crate::leanh::lean_ctor_get(v_toApplicative_5531_, 1);
            crate::leanh::lean_inc(v_toPure_5533_);
            v_fvarId_5534_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5534_, 2);
            v_i_5535_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_i_5535_);
            v_y_5536_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc(v_y_5536_);
            v_k_5537_ = crate::leanh::lean_ctor_get(v_c_5449_, 3);
            crate::leanh::lean_inc_ref(v_k_5537_);
            v___x_5538_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5539_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__19___boxed
                    as *mut core::ffi::c_void,
                12,
                11,
            );
            crate::leanh::lean_closure_set(v___f_5539_, 0, v_i_5535_);
            crate::leanh::lean_closure_set(v___f_5539_, 1, v_toPure_5533_);
            crate::leanh::lean_closure_set(v___f_5539_, 2, v_y_5536_);
            crate::leanh::lean_closure_set(v___f_5539_, 3, v_k_5537_);
            crate::leanh::lean_closure_set(v___f_5539_, 4, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5539_, 5, v_fvarId_5534_);
            crate::leanh::lean_closure_set(v___f_5539_, 6, v___x_5538_);
            crate::leanh::lean_closure_set(v___f_5539_, 7, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5539_, 8, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5539_, 9, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5539_, 10, v_toBind_5532_);
            v___x_5540_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5534_);
            v___x_5541_ = crate::leanh::lean_apply_4(
                v_toBind_5532_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5540_,
                v___f_5539_,
            );
            return v___x_5541_;
        }
        8 => {
            let mut v_toApplicative_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5542_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5543_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5543_, 2);
            v_toPure_5544_ = crate::leanh::lean_ctor_get(v_toApplicative_5542_, 1);
            crate::leanh::lean_inc(v_toPure_5544_);
            v_fvarId_5545_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5545_, 2);
            v_i_5546_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_i_5546_);
            v_y_5547_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc(v_y_5547_);
            v_k_5548_ = crate::leanh::lean_ctor_get(v_c_5449_, 3);
            crate::leanh::lean_inc_ref(v_k_5548_);
            v___x_5549_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5550_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__22___boxed
                    as *mut core::ffi::c_void,
                12,
                11,
            );
            crate::leanh::lean_closure_set(v___f_5550_, 0, v_i_5546_);
            crate::leanh::lean_closure_set(v___f_5550_, 1, v_toPure_5544_);
            crate::leanh::lean_closure_set(v___f_5550_, 2, v_y_5547_);
            crate::leanh::lean_closure_set(v___f_5550_, 3, v_k_5548_);
            crate::leanh::lean_closure_set(v___f_5550_, 4, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5550_, 5, v_fvarId_5545_);
            crate::leanh::lean_closure_set(v___f_5550_, 6, v___x_5549_);
            crate::leanh::lean_closure_set(v___f_5550_, 7, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5550_, 8, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5550_, 9, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5550_, 10, v_toBind_5543_);
            v___x_5551_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5545_);
            v___x_5552_ = crate::leanh::lean_apply_4(
                v_toBind_5543_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5551_,
                v___f_5550_,
            );
            return v___x_5552_;
        }
        9 => {
            let mut v_toApplicative_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_offset_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5553_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5554_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5554_, 2);
            v_toPure_5555_ = crate::leanh::lean_ctor_get(v_toApplicative_5553_, 1);
            crate::leanh::lean_inc(v_toPure_5555_);
            v_fvarId_5556_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5556_, 2);
            v_i_5557_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_i_5557_);
            v_offset_5558_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc(v_offset_5558_);
            v_y_5559_ = crate::leanh::lean_ctor_get(v_c_5449_, 3);
            crate::leanh::lean_inc(v_y_5559_);
            v_ty_5560_ = crate::leanh::lean_ctor_get(v_c_5449_, 4);
            crate::leanh::lean_inc_ref(v_ty_5560_);
            v_k_5561_ = crate::leanh::lean_ctor_get(v_c_5449_, 5);
            crate::leanh::lean_inc_ref(v_k_5561_);
            v___x_5562_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5563_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__26___boxed
                    as *mut core::ffi::c_void,
                14,
                13,
            );
            crate::leanh::lean_closure_set(v___f_5563_, 0, v_i_5557_);
            crate::leanh::lean_closure_set(v___f_5563_, 1, v_offset_5558_);
            crate::leanh::lean_closure_set(v___f_5563_, 2, v_toPure_5555_);
            crate::leanh::lean_closure_set(v___f_5563_, 3, v_y_5559_);
            crate::leanh::lean_closure_set(v___f_5563_, 4, v_ty_5560_);
            crate::leanh::lean_closure_set(v___f_5563_, 5, v_k_5561_);
            crate::leanh::lean_closure_set(v___f_5563_, 6, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5563_, 7, v_fvarId_5556_);
            crate::leanh::lean_closure_set(v___f_5563_, 8, v___x_5562_);
            crate::leanh::lean_closure_set(v___f_5563_, 9, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5563_, 10, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5563_, 11, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5563_, 12, v_toBind_5554_);
            v___x_5564_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5556_);
            v___x_5565_ = crate::leanh::lean_apply_4(
                v_toBind_5554_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5564_,
                v___f_5563_,
            );
            return v___x_5565_;
        }
        10 => {
            let mut v_toApplicative_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cidx_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5566_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5567_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5567_, 2);
            v_toPure_5568_ = crate::leanh::lean_ctor_get(v_toApplicative_5566_, 1);
            crate::leanh::lean_inc(v_toPure_5568_);
            v_fvarId_5569_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5569_, 2);
            v_cidx_5570_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_cidx_5570_);
            v_k_5571_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc_ref(v_k_5571_);
            v___x_5572_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5573_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__28___boxed
                    as *mut core::ffi::c_void,
                11,
                10,
            );
            crate::leanh::lean_closure_set(v___f_5573_, 0, v_cidx_5570_);
            crate::leanh::lean_closure_set(v___f_5573_, 1, v_toPure_5568_);
            crate::leanh::lean_closure_set(v___f_5573_, 2, v_k_5571_);
            crate::leanh::lean_closure_set(v___f_5573_, 3, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5573_, 4, v_fvarId_5569_);
            crate::leanh::lean_closure_set(v___f_5573_, 5, v___x_5572_);
            crate::leanh::lean_closure_set(v___f_5573_, 6, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5573_, 7, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5573_, 8, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5573_, 9, v_toBind_5567_);
            v___x_5574_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5569_);
            v___x_5575_ = crate::leanh::lean_apply_4(
                v_toBind_5567_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5574_,
                v___f_5573_,
            );
            return v___x_5575_;
        }
        11 => {
            let mut v_toApplicative_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_check_5581_: u8 = 0;
            let mut v_persistent_5582_: u8 = 0;
            let mut v_k_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5576_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5577_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5577_, 2);
            v_toPure_5578_ = crate::leanh::lean_ctor_get(v_toApplicative_5576_, 1);
            crate::leanh::lean_inc(v_toPure_5578_);
            v_fvarId_5579_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5579_, 2);
            v_n_5580_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_n_5580_);
            v_check_5581_ = crate::leanh::lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_persistent_5582_ = crate::leanh::lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
            );
            v_k_5583_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc_ref(v_k_5583_);
            v___x_5584_ = crate::leanh::lean_box((v_check_5581_) as usize);
            v___x_5585_ = crate::leanh::lean_box((v_persistent_5582_) as usize);
            v___x_5586_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5587_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__30___boxed
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            crate::leanh::lean_closure_set(v___f_5587_, 0, v_n_5580_);
            crate::leanh::lean_closure_set(v___f_5587_, 1, v___x_5584_);
            crate::leanh::lean_closure_set(v___f_5587_, 2, v___x_5585_);
            crate::leanh::lean_closure_set(v___f_5587_, 3, v_toPure_5578_);
            crate::leanh::lean_closure_set(v___f_5587_, 4, v_k_5583_);
            crate::leanh::lean_closure_set(v___f_5587_, 5, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5587_, 6, v_fvarId_5579_);
            crate::leanh::lean_closure_set(v___f_5587_, 7, v___x_5586_);
            crate::leanh::lean_closure_set(v___f_5587_, 8, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5587_, 9, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5587_, 10, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5587_, 11, v_toBind_5577_);
            v___x_5588_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5579_);
            v___x_5589_ = crate::leanh::lean_apply_4(
                v_toBind_5577_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5588_,
                v___f_5587_,
            );
            return v___x_5589_;
        }
        12 => {
            let mut v_toApplicative_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_check_5595_: u8 = 0;
            let mut v_persistent_5596_: u8 = 0;
            let mut v_objs_x3f_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5590_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5591_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5591_, 2);
            v_toPure_5592_ = crate::leanh::lean_ctor_get(v_toApplicative_5590_, 1);
            crate::leanh::lean_inc(v_toPure_5592_);
            v_fvarId_5593_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5593_, 2);
            v_n_5594_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc(v_n_5594_);
            v_check_5595_ = crate::leanh::lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v_persistent_5596_ = crate::leanh::lean_ctor_get_uint8(
                v_c_5449_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
            );
            v_objs_x3f_5597_ = crate::leanh::lean_ctor_get(v_c_5449_, 2);
            crate::leanh::lean_inc(v_objs_x3f_5597_);
            v_k_5598_ = crate::leanh::lean_ctor_get(v_c_5449_, 3);
            crate::leanh::lean_inc_ref(v_k_5598_);
            v___x_5599_ = crate::leanh::lean_box((v_check_5595_) as usize);
            v___x_5600_ = crate::leanh::lean_box((v_persistent_5596_) as usize);
            v___x_5601_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5602_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__32___boxed
                    as *mut core::ffi::c_void,
                14,
                13,
            );
            crate::leanh::lean_closure_set(v___f_5602_, 0, v_n_5594_);
            crate::leanh::lean_closure_set(v___f_5602_, 1, v___x_5599_);
            crate::leanh::lean_closure_set(v___f_5602_, 2, v___x_5600_);
            crate::leanh::lean_closure_set(v___f_5602_, 3, v_objs_x3f_5597_);
            crate::leanh::lean_closure_set(v___f_5602_, 4, v_toPure_5592_);
            crate::leanh::lean_closure_set(v___f_5602_, 5, v_k_5598_);
            crate::leanh::lean_closure_set(v___f_5602_, 6, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5602_, 7, v_fvarId_5593_);
            crate::leanh::lean_closure_set(v___f_5602_, 8, v___x_5601_);
            crate::leanh::lean_closure_set(v___f_5602_, 9, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5602_, 10, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5602_, 11, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5602_, 12, v_toBind_5591_);
            v___x_5603_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5593_);
            v___x_5604_ = crate::leanh::lean_apply_4(
                v_toBind_5591_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5603_,
                v___f_5602_,
            );
            return v___x_5604_;
        }
        _ => {
            let mut v_toApplicative_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5605_ = crate::leanh::lean_ctor_get(v_inst_5447_, 0);
            v_toBind_5606_ = crate::leanh::lean_ctor_get(v_inst_5447_, 1);
            crate::leanh::lean_inc_n(v_toBind_5606_, 2);
            v_toPure_5607_ = crate::leanh::lean_ctor_get(v_toApplicative_5605_, 1);
            crate::leanh::lean_inc(v_toPure_5607_);
            v_fvarId_5608_ = crate::leanh::lean_ctor_get(v_c_5449_, 0);
            crate::leanh::lean_inc_n(v_fvarId_5608_, 2);
            v_k_5609_ = crate::leanh::lean_ctor_get(v_c_5449_, 1);
            crate::leanh::lean_inc_ref(v_k_5609_);
            v___x_5610_ = crate::leanh::lean_box((v_pu_5445_) as usize);
            crate::leanh::lean_inc(v_f_5448_);
            v___f_5611_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__34___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            crate::leanh::lean_closure_set(v___f_5611_, 0, v_toPure_5607_);
            crate::leanh::lean_closure_set(v___f_5611_, 1, v_c_5449_);
            crate::leanh::lean_closure_set(v___f_5611_, 2, v_fvarId_5608_);
            crate::leanh::lean_closure_set(v___f_5611_, 3, v_k_5609_);
            crate::leanh::lean_closure_set(v___f_5611_, 4, v___x_5610_);
            crate::leanh::lean_closure_set(v___f_5611_, 5, v_inst_5446_);
            crate::leanh::lean_closure_set(v___f_5611_, 6, v_inst_5447_);
            crate::leanh::lean_closure_set(v___f_5611_, 7, v_f_5448_);
            crate::leanh::lean_closure_set(v___f_5611_, 8, v_toBind_5606_);
            v___x_5612_ = crate::leanh::lean_apply_1(v_f_5448_, v_fvarId_5608_);
            v___x_5613_ = crate::leanh::lean_apply_4(
                v_toBind_5606_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5612_,
                v___f_5611_,
            );
            return v___x_5613_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed(
    mut v_pu_5614_: *mut crate::leanh::LeanObject,
    mut v_inst_5615_: *mut crate::leanh::LeanObject,
    mut v_inst_5616_: *mut crate::leanh::LeanObject,
    mut v_f_5617_: *mut crate::leanh::LeanObject,
    mut v_c_5618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5619_: u8 = 0;
    let mut v_res_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5619_ = (crate::leanh::lean_unbox(v_pu_5614_) as u8);
    v_res_5620_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_boxed_5619_,
        v_inst_5615_,
        v_inst_5616_,
        v_f_5617_,
        v_c_5618_,
    );
    return v_res_5620_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___lam__10(
    mut v_pu_5621_: u8,
    mut v_inst_5622_: *mut crate::leanh::LeanObject,
    mut v_inst_5623_: *mut crate::leanh::LeanObject,
    mut v_f_5624_: *mut crate::leanh::LeanObject,
    mut v_x_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5626_ = crate::leanh::lean_box((v_pu_5621_) as usize);
    crate::leanh::lean_inc_ref(v_inst_5623_);
    v___x_5627_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_mapFVarM___redArg___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5627_, 0, v___x_5626_);
    crate::leanh::lean_closure_set(v___x_5627_, 1, v_inst_5622_);
    crate::leanh::lean_closure_set(v___x_5627_, 2, v_inst_5623_);
    crate::leanh::lean_closure_set(v___x_5627_, 3, v_f_5624_);
    v___x_5628_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(v_inst_5623_, v_x_5625_, v___x_5627_);
    return v___x_5628_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM(
    mut v_m_5629_: *mut crate::leanh::LeanObject,
    mut v_pu_5630_: u8,
    mut v_inst_5631_: *mut crate::leanh::LeanObject,
    mut v_inst_5632_: *mut crate::leanh::LeanObject,
    mut v_f_5633_: *mut crate::leanh::LeanObject,
    mut v_c_5634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5635_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5630_,
        v_inst_5631_,
        v_inst_5632_,
        v_f_5633_,
        v_c_5634_,
    );
    return v___x_5635_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_mapFVarM___boxed(
    mut v_m_5636_: *mut crate::leanh::LeanObject,
    mut v_pu_5637_: *mut crate::leanh::LeanObject,
    mut v_inst_5638_: *mut crate::leanh::LeanObject,
    mut v_inst_5639_: *mut crate::leanh::LeanObject,
    mut v_f_5640_: *mut crate::leanh::LeanObject,
    mut v_c_5641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5642_: u8 = 0;
    let mut v_res_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5642_ = (crate::leanh::lean_unbox(v_pu_5637_) as u8);
    v_res_5643_ = l_Lean_Compiler_LCNF_Code_mapFVarM(
        v_m_5636_,
        v_pu_boxed_5642_,
        v_inst_5638_,
        v_inst_5639_,
        v_f_5640_,
        v_c_5641_,
    );
    return v_res_5643_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1(
    mut v_inst_5644_: *mut crate::leanh::LeanObject,
    mut v_f_5645_: *mut crate::leanh::LeanObject,
    mut v_type_5646_: *mut crate::leanh::LeanObject,
    mut v_toBind_5647_: *mut crate::leanh::LeanObject,
    mut v___f_5648_: *mut crate::leanh::LeanObject,
    mut v_____r_5649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5650_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5644_, v_f_5645_, v_type_5646_);
    v___x_5651_ = crate::leanh::lean_apply_4(
        v_toBind_5647_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5650_,
        v___f_5648_,
    );
    return v___x_5651_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12(
    mut v_inst_5652_: *mut crate::leanh::LeanObject,
    mut v_f_5653_: *mut crate::leanh::LeanObject,
    mut v_ty_5654_: *mut crate::leanh::LeanObject,
    mut v_toBind_5655_: *mut crate::leanh::LeanObject,
    mut v___f_5656_: *mut crate::leanh::LeanObject,
    mut v_____r_5657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5658_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5652_, v_f_5653_, v_ty_5654_);
    v___x_5659_ = crate::leanh::lean_apply_4(
        v_toBind_5655_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5658_,
        v___f_5656_,
    );
    return v___x_5659_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4(
    mut v_args_5660_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_5661_: *mut crate::leanh::LeanObject,
    mut v_inst_5662_: *mut crate::leanh::LeanObject,
    mut v___f_5663_: *mut crate::leanh::LeanObject,
    mut v_____r_5664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    v___x_5665_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5666_ = lean_array_get_size(v_args_5660_);
    v___x_5667_ = crate::leanh::lean_box(0);
    v___x_5668_ = lean_nat_dec_lt(v___x_5665_, v___x_5666_);
    if v___x_5668_ == 0 {
        let mut v_toPure_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_5663_);
        crate::leanh::lean_dec_ref(v_inst_5662_);
        crate::leanh::lean_dec_ref(v_args_5660_);
        v_toPure_5669_ = crate::leanh::lean_ctor_get(v_toApplicative_5661_, 1);
        crate::leanh::lean_inc(v_toPure_5669_);
        crate::leanh::lean_dec_ref(v_toApplicative_5661_);
        v___x_5670_ =
            crate::leanh::lean_apply_2(v_toPure_5669_, crate::leanh::lean_box(0), v___x_5667_);
        return v___x_5670_;
    } else {
        let mut v___x_5671_: u8 = 0;
        v___x_5671_ = lean_nat_dec_le(v___x_5666_, v___x_5666_);
        if v___x_5671_ == 0 {
            if v___x_5668_ == 0 {
                let mut v_toPure_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___f_5663_);
                crate::leanh::lean_dec_ref(v_inst_5662_);
                crate::leanh::lean_dec_ref(v_args_5660_);
                v_toPure_5672_ = crate::leanh::lean_ctor_get(v_toApplicative_5661_, 1);
                crate::leanh::lean_inc(v_toPure_5672_);
                crate::leanh::lean_dec_ref(v_toApplicative_5661_);
                v___x_5673_ = crate::leanh::lean_apply_2(
                    v_toPure_5672_,
                    crate::leanh::lean_box(0),
                    v___x_5667_,
                );
                return v___x_5673_;
            } else {
                let mut v___x_5674_: usize = 0;
                let mut v___x_5675_: usize = 0;
                let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_toApplicative_5661_);
                v___x_5674_ = 0usize;
                v___x_5675_ = lean_usize_of_nat(v___x_5666_);
                v___x_5676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_5662_,
                    v___f_5663_,
                    v_args_5660_,
                    v___x_5674_,
                    v___x_5675_,
                    v___x_5667_,
                );
                return v___x_5676_;
            }
        } else {
            let mut v___x_5677_: usize = 0;
            let mut v___x_5678_: usize = 0;
            let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_toApplicative_5661_);
            v___x_5677_ = 0usize;
            v___x_5678_ = lean_usize_of_nat(v___x_5666_);
            v___x_5679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5662_,
                v___f_5663_,
                v_args_5660_,
                v___x_5677_,
                v___x_5678_,
                v___x_5667_,
            );
            return v___x_5679_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3(
    mut v_inst_5680_: *mut crate::leanh::LeanObject,
    mut v_f_5681_: *mut crate::leanh::LeanObject,
    mut v_x_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_5680_, v_f_5681_, v___y_5683_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10(
    mut v_inst_5685_: *mut crate::leanh::LeanObject,
    mut v_f_5686_: *mut crate::leanh::LeanObject,
    mut v_y_5687_: *mut crate::leanh::LeanObject,
    mut v_toBind_5688_: *mut crate::leanh::LeanObject,
    mut v___f_5689_: *mut crate::leanh::LeanObject,
    mut v_____r_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5691_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_5685_, v_f_5686_, v_y_5687_);
    v___x_5692_ = crate::leanh::lean_apply_4(
        v_toBind_5688_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5691_,
        v___f_5689_,
    );
    return v___x_5692_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11(
    mut v_f_5693_: *mut crate::leanh::LeanObject,
    mut v_y_5694_: *mut crate::leanh::LeanObject,
    mut v_toBind_5695_: *mut crate::leanh::LeanObject,
    mut v___f_5696_: *mut crate::leanh::LeanObject,
    mut v_____r_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5698_ = crate::leanh::lean_apply_1(v_f_5693_, v_y_5694_);
    v___x_5699_ = crate::leanh::lean_apply_4(
        v_toBind_5695_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5698_,
        v___f_5696_,
    );
    return v___x_5699_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7(
    mut v_f_5700_: *mut crate::leanh::LeanObject,
    mut v_discr_5701_: *mut crate::leanh::LeanObject,
    mut v_toBind_5702_: *mut crate::leanh::LeanObject,
    mut v___f_5703_: *mut crate::leanh::LeanObject,
    mut v_____r_5704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5705_ = crate::leanh::lean_apply_1(v_f_5700_, v_discr_5701_);
    v___x_5706_ = crate::leanh::lean_apply_4(
        v_toBind_5702_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5705_,
        v___f_5703_,
    );
    return v___x_5706_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6(
    mut v_alts_5707_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_5708_: *mut crate::leanh::LeanObject,
    mut v_inst_5709_: *mut crate::leanh::LeanObject,
    mut v___f_5710_: *mut crate::leanh::LeanObject,
    mut v_____r_5711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: u8 = 0;
    v___x_5712_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5713_ = lean_array_get_size(v_alts_5707_);
    v___x_5714_ = crate::leanh::lean_box(0);
    v___x_5715_ = lean_nat_dec_lt(v___x_5712_, v___x_5713_);
    if v___x_5715_ == 0 {
        let mut v_toPure_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_5710_);
        crate::leanh::lean_dec_ref(v_inst_5709_);
        crate::leanh::lean_dec_ref(v_alts_5707_);
        v_toPure_5716_ = crate::leanh::lean_ctor_get(v_toApplicative_5708_, 1);
        crate::leanh::lean_inc(v_toPure_5716_);
        crate::leanh::lean_dec_ref(v_toApplicative_5708_);
        v___x_5717_ =
            crate::leanh::lean_apply_2(v_toPure_5716_, crate::leanh::lean_box(0), v___x_5714_);
        return v___x_5717_;
    } else {
        let mut v___x_5718_: u8 = 0;
        v___x_5718_ = lean_nat_dec_le(v___x_5713_, v___x_5713_);
        if v___x_5718_ == 0 {
            if v___x_5715_ == 0 {
                let mut v_toPure_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___f_5710_);
                crate::leanh::lean_dec_ref(v_inst_5709_);
                crate::leanh::lean_dec_ref(v_alts_5707_);
                v_toPure_5719_ = crate::leanh::lean_ctor_get(v_toApplicative_5708_, 1);
                crate::leanh::lean_inc(v_toPure_5719_);
                crate::leanh::lean_dec_ref(v_toApplicative_5708_);
                v___x_5720_ = crate::leanh::lean_apply_2(
                    v_toPure_5719_,
                    crate::leanh::lean_box(0),
                    v___x_5714_,
                );
                return v___x_5720_;
            } else {
                let mut v___x_5721_: usize = 0;
                let mut v___x_5722_: usize = 0;
                let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_toApplicative_5708_);
                v___x_5721_ = 0usize;
                v___x_5722_ = lean_usize_of_nat(v___x_5713_);
                v___x_5723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_5709_,
                    v___f_5710_,
                    v_alts_5707_,
                    v___x_5721_,
                    v___x_5722_,
                    v___x_5714_,
                );
                return v___x_5723_;
            }
        } else {
            let mut v___x_5724_: usize = 0;
            let mut v___x_5725_: usize = 0;
            let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_toApplicative_5708_);
            v___x_5724_ = 0usize;
            v___x_5725_ = lean_usize_of_nat(v___x_5713_);
            v___x_5726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_5709_,
                v___f_5710_,
                v_alts_5707_,
                v___x_5724_,
                v___x_5725_,
                v___x_5714_,
            );
            return v___x_5726_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8(
    mut v_inst_5727_: *mut crate::leanh::LeanObject,
    mut v_f_5728_: *mut crate::leanh::LeanObject,
    mut v_x_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5731_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_5727_, v_f_5728_, v___y_5730_);
    return v___x_5731_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5(
    mut v_inst_5732_: *mut crate::leanh::LeanObject,
    mut v_f_5733_: *mut crate::leanh::LeanObject,
    mut v_x_5734_: *mut crate::leanh::LeanObject,
    mut v___y_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5736_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_5736_, 0, v_inst_5732_);
    crate::leanh::lean_closure_set(v___x_5736_, 1, v_f_5733_);
    v___x_5737_ = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(v___y_5735_, v___x_5736_);
    return v___x_5737_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2(
    mut v_inst_5738_: *mut crate::leanh::LeanObject,
    mut v_f_5739_: *mut crate::leanh::LeanObject,
    mut v_value_5740_: *mut crate::leanh::LeanObject,
    mut v_toBind_5741_: *mut crate::leanh::LeanObject,
    mut v___f_5742_: *mut crate::leanh::LeanObject,
    mut v_____r_5743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5744_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5738_, v_f_5739_, v_value_5740_);
    v___x_5745_ = crate::leanh::lean_apply_4(
        v_toBind_5741_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5744_,
        v___f_5742_,
    );
    return v___x_5745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg(
    mut v_inst_5746_: *mut crate::leanh::LeanObject,
    mut v_f_5747_: *mut crate::leanh::LeanObject,
    mut v_c_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_c_5748_) {
        0 => {
            let mut v_toBind_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5749_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5749_);
            v_decl_5750_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc_ref(v_decl_5750_);
            v_k_5751_ = crate::leanh::lean_ctor_get(v_c_5748_, 1);
            crate::leanh::lean_inc_ref(v_k_5751_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 2);
            crate::leanh::lean_inc(v_f_5747_);
            crate::leanh::lean_inc_ref(v_inst_5746_);
            v___f_5752_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5752_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5752_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5752_, 2, v_k_5751_);
            v___x_5753_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
                v_inst_5746_,
                v_f_5747_,
                v_decl_5750_,
            );
            v___x_5754_ = crate::leanh::lean_apply_4(
                v_toBind_5749_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5753_,
                v___f_5752_,
            );
            return v___x_5754_;
        }
        3 => {
            let mut v_toApplicative_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_5755_ = crate::leanh::lean_ctor_get(v_inst_5746_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_5755_);
            v_toBind_5756_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5756_);
            v_fvarId_5757_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5757_);
            v_args_5758_ = crate::leanh::lean_ctor_get(v_c_5748_, 1);
            crate::leanh::lean_inc_ref(v_args_5758_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 2);
            crate::leanh::lean_inc(v_f_5747_);
            crate::leanh::lean_inc_ref(v_inst_5746_);
            v___f_5759_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__8 as *mut core::ffi::c_void,
                4,
                2,
            );
            crate::leanh::lean_closure_set(v___f_5759_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5759_, 1, v_f_5747_);
            v___f_5760_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__4 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5760_, 0, v_args_5758_);
            crate::leanh::lean_closure_set(v___f_5760_, 1, v_toApplicative_5755_);
            crate::leanh::lean_closure_set(v___f_5760_, 2, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5760_, 3, v___f_5759_);
            v___x_5761_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5757_);
            v___x_5762_ = crate::leanh::lean_apply_4(
                v_toBind_5756_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5761_,
                v___f_5760_,
            );
            return v___x_5762_;
        }
        4 => {
            let mut v_cases_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_resultType_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_discr_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_alts_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_cases_5763_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc_ref(v_cases_5763_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 1);
            v_toApplicative_5764_ = crate::leanh::lean_ctor_get(v_inst_5746_, 0);
            v_toBind_5765_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc_n(v_toBind_5765_, 2);
            v_resultType_5766_ = crate::leanh::lean_ctor_get(v_cases_5763_, 1);
            crate::leanh::lean_inc_ref(v_resultType_5766_);
            v_discr_5767_ = crate::leanh::lean_ctor_get(v_cases_5763_, 2);
            crate::leanh::lean_inc(v_discr_5767_);
            v_alts_5768_ = crate::leanh::lean_ctor_get(v_cases_5763_, 3);
            crate::leanh::lean_inc_ref(v_alts_5768_);
            crate::leanh::lean_dec_ref(v_cases_5763_);
            crate::leanh::lean_inc_n(v_f_5747_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_5746_, 2);
            v___f_5769_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__5 as *mut core::ffi::c_void,
                4,
                2,
            );
            crate::leanh::lean_closure_set(v___f_5769_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5769_, 1, v_f_5747_);
            crate::leanh::lean_inc_ref(v_toApplicative_5764_);
            v___f_5770_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__6 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5770_, 0, v_alts_5768_);
            crate::leanh::lean_closure_set(v___f_5770_, 1, v_toApplicative_5764_);
            crate::leanh::lean_closure_set(v___f_5770_, 2, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5770_, 3, v___f_5769_);
            v___f_5771_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__7 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5771_, 0, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5771_, 1, v_discr_5767_);
            crate::leanh::lean_closure_set(v___f_5771_, 2, v_toBind_5765_);
            crate::leanh::lean_closure_set(v___f_5771_, 3, v___f_5770_);
            v___x_5772_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(
                v_inst_5746_,
                v_f_5747_,
                v_resultType_5766_,
            );
            v___x_5773_ = crate::leanh::lean_apply_4(
                v_toBind_5765_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5772_,
                v___f_5771_,
            );
            return v___x_5773_;
        }
        5 => {
            let mut v_fvarId_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_5746_);
            v_fvarId_5774_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5774_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 1);
            v___x_5775_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5774_);
            return v___x_5775_;
        }
        6 => {
            let mut v_type_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_type_5776_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc_ref(v_type_5776_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 1);
            v___x_5777_ =
                l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_5746_, v_f_5747_, v_type_5776_);
            return v___x_5777_;
        }
        7 => {
            let mut v_toBind_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5778_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc_n(v_toBind_5778_, 2);
            v_fvarId_5779_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5779_);
            v_y_5780_ = crate::leanh::lean_ctor_get(v_c_5748_, 2);
            crate::leanh::lean_inc(v_y_5780_);
            v_k_5781_ = crate::leanh::lean_ctor_get(v_c_5748_, 3);
            crate::leanh::lean_inc_ref(v_k_5781_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 4);
            crate::leanh::lean_inc_n(v_f_5747_, 2);
            crate::leanh::lean_inc_ref(v_inst_5746_);
            v___f_5782_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5782_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5782_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5782_, 2, v_k_5781_);
            v___f_5783_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__10 as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_5783_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5783_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5783_, 2, v_y_5780_);
            crate::leanh::lean_closure_set(v___f_5783_, 3, v_toBind_5778_);
            crate::leanh::lean_closure_set(v___f_5783_, 4, v___f_5782_);
            v___x_5784_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5779_);
            v___x_5785_ = crate::leanh::lean_apply_4(
                v_toBind_5778_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5784_,
                v___f_5783_,
            );
            return v___x_5785_;
        }
        8 => {
            let mut v_toBind_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5786_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc_n(v_toBind_5786_, 2);
            v_fvarId_5787_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5787_);
            v_y_5788_ = crate::leanh::lean_ctor_get(v_c_5748_, 2);
            crate::leanh::lean_inc(v_y_5788_);
            v_k_5789_ = crate::leanh::lean_ctor_get(v_c_5748_, 3);
            crate::leanh::lean_inc_ref(v_k_5789_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 4);
            crate::leanh::lean_inc_n(v_f_5747_, 2);
            v___f_5790_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5790_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5790_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5790_, 2, v_k_5789_);
            v___f_5791_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5791_, 0, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5791_, 1, v_y_5788_);
            crate::leanh::lean_closure_set(v___f_5791_, 2, v_toBind_5786_);
            crate::leanh::lean_closure_set(v___f_5791_, 3, v___f_5790_);
            v___x_5792_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5787_);
            v___x_5793_ = crate::leanh::lean_apply_4(
                v_toBind_5786_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5792_,
                v___f_5791_,
            );
            return v___x_5793_;
        }
        9 => {
            let mut v_toBind_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5794_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc_n(v_toBind_5794_, 3);
            v_fvarId_5795_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5795_);
            v_y_5796_ = crate::leanh::lean_ctor_get(v_c_5748_, 3);
            crate::leanh::lean_inc(v_y_5796_);
            v_ty_5797_ = crate::leanh::lean_ctor_get(v_c_5748_, 4);
            crate::leanh::lean_inc_ref(v_ty_5797_);
            v_k_5798_ = crate::leanh::lean_ctor_get(v_c_5748_, 5);
            crate::leanh::lean_inc_ref(v_k_5798_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 6);
            crate::leanh::lean_inc_n(v_f_5747_, 3);
            crate::leanh::lean_inc_ref(v_inst_5746_);
            v___f_5799_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5799_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5799_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5799_, 2, v_k_5798_);
            v___f_5800_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__12 as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_5800_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5800_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5800_, 2, v_ty_5797_);
            crate::leanh::lean_closure_set(v___f_5800_, 3, v_toBind_5794_);
            crate::leanh::lean_closure_set(v___f_5800_, 4, v___f_5799_);
            v___f_5801_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__11 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_5801_, 0, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5801_, 1, v_y_5796_);
            crate::leanh::lean_closure_set(v___f_5801_, 2, v_toBind_5794_);
            crate::leanh::lean_closure_set(v___f_5801_, 3, v___f_5800_);
            v___x_5802_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5795_);
            v___x_5803_ = crate::leanh::lean_apply_4(
                v_toBind_5794_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5802_,
                v___f_5801_,
            );
            return v___x_5803_;
        }
        10 => {
            let mut v_toBind_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5804_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5804_);
            v_fvarId_5805_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5805_);
            v_k_5806_ = crate::leanh::lean_ctor_get(v_c_5748_, 2);
            crate::leanh::lean_inc_ref(v_k_5806_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 3);
            crate::leanh::lean_inc(v_f_5747_);
            v___f_5807_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5807_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5807_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5807_, 2, v_k_5806_);
            v___x_5808_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5805_);
            v___x_5809_ = crate::leanh::lean_apply_4(
                v_toBind_5804_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5808_,
                v___f_5807_,
            );
            return v___x_5809_;
        }
        11 => {
            let mut v_toBind_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5810_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5810_);
            v_fvarId_5811_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5811_);
            v_k_5812_ = crate::leanh::lean_ctor_get(v_c_5748_, 2);
            crate::leanh::lean_inc_ref(v_k_5812_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 3);
            crate::leanh::lean_inc(v_f_5747_);
            v___f_5813_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5813_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5813_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5813_, 2, v_k_5812_);
            v___x_5814_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5811_);
            v___x_5815_ = crate::leanh::lean_apply_4(
                v_toBind_5810_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5814_,
                v___f_5813_,
            );
            return v___x_5815_;
        }
        12 => {
            let mut v_toBind_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5816_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5816_);
            v_fvarId_5817_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5817_);
            v_k_5818_ = crate::leanh::lean_ctor_get(v_c_5748_, 3);
            crate::leanh::lean_inc_ref(v_k_5818_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 4);
            crate::leanh::lean_inc(v_f_5747_);
            v___f_5819_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5819_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5819_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5819_, 2, v_k_5818_);
            v___x_5820_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5817_);
            v___x_5821_ = crate::leanh::lean_apply_4(
                v_toBind_5816_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5820_,
                v___f_5819_,
            );
            return v___x_5821_;
        }
        13 => {
            let mut v_toBind_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_5822_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc(v_toBind_5822_);
            v_fvarId_5823_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc(v_fvarId_5823_);
            v_k_5824_ = crate::leanh::lean_ctor_get(v_c_5748_, 1);
            crate::leanh::lean_inc_ref(v_k_5824_);
            crate::leanh::lean_dec_ref_known(v_c_5748_, 2);
            crate::leanh::lean_inc(v_f_5747_);
            v___f_5825_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5825_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5825_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5825_, 2, v_k_5824_);
            v___x_5826_ = crate::leanh::lean_apply_1(v_f_5747_, v_fvarId_5823_);
            v___x_5827_ = crate::leanh::lean_apply_4(
                v_toBind_5822_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_5826_,
                v___f_5825_,
            );
            return v___x_5827_;
        }
        _ => {
            let mut v_decl_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5841_: u8 = 0;
            v_decl_5828_ = crate::leanh::lean_ctor_get(v_c_5748_, 0);
            crate::leanh::lean_inc_ref(v_decl_5828_);
            v_toApplicative_5829_ = crate::leanh::lean_ctor_get(v_inst_5746_, 0);
            v_toBind_5830_ = crate::leanh::lean_ctor_get(v_inst_5746_, 1);
            crate::leanh::lean_inc_n(v_toBind_5830_, 3);
            v_k_5831_ = crate::leanh::lean_ctor_get(v_c_5748_, 1);
            crate::leanh::lean_inc_ref(v_k_5831_);
            crate::leanh::lean_dec_ref(v_c_5748_);
            v_params_5832_ = crate::leanh::lean_ctor_get(v_decl_5828_, 2);
            crate::leanh::lean_inc_ref(v_params_5832_);
            v_type_5833_ = crate::leanh::lean_ctor_get(v_decl_5828_, 3);
            crate::leanh::lean_inc_ref(v_type_5833_);
            v_value_5834_ = crate::leanh::lean_ctor_get(v_decl_5828_, 4);
            crate::leanh::lean_inc_ref(v_value_5834_);
            crate::leanh::lean_dec_ref(v_decl_5828_);
            crate::leanh::lean_inc_n(v_f_5747_, 3);
            crate::leanh::lean_inc_ref_n(v_inst_5746_, 3);
            v___f_5835_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5835_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5835_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5835_, 2, v_k_5831_);
            v___f_5836_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__2 as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_5836_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5836_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5836_, 2, v_value_5834_);
            crate::leanh::lean_closure_set(v___f_5836_, 3, v_toBind_5830_);
            crate::leanh::lean_closure_set(v___f_5836_, 4, v___f_5835_);
            v___f_5837_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__1 as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_5837_, 0, v_inst_5746_);
            crate::leanh::lean_closure_set(v___f_5837_, 1, v_f_5747_);
            crate::leanh::lean_closure_set(v___f_5837_, 2, v_type_5833_);
            crate::leanh::lean_closure_set(v___f_5837_, 3, v_toBind_5830_);
            crate::leanh::lean_closure_set(v___f_5837_, 4, v___f_5836_);
            v___x_5838_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5839_ = lean_array_get_size(v_params_5832_);
            v___x_5840_ = crate::leanh::lean_box(0);
            v___x_5841_ = lean_nat_dec_lt(v___x_5838_, v___x_5839_);
            if v___x_5841_ == 0 {
                let mut v_toPure_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_toApplicative_5829_);
                crate::leanh::lean_dec_ref(v_params_5832_);
                crate::leanh::lean_dec(v_f_5747_);
                crate::leanh::lean_dec_ref(v_inst_5746_);
                v_toPure_5842_ = crate::leanh::lean_ctor_get(v_toApplicative_5829_, 1);
                crate::leanh::lean_inc(v_toPure_5842_);
                crate::leanh::lean_dec_ref(v_toApplicative_5829_);
                v___x_5843_ = crate::leanh::lean_apply_2(
                    v_toPure_5842_,
                    crate::leanh::lean_box(0),
                    v___x_5840_,
                );
                v___x_5844_ = crate::leanh::lean_apply_4(
                    v_toBind_5830_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5843_,
                    v___f_5837_,
                );
                return v___x_5844_;
            } else {
                let mut v___f_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5846_: u8 = 0;
                crate::leanh::lean_inc_ref(v_inst_5746_);
                v___f_5845_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__3 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_5845_, 0, v_inst_5746_);
                crate::leanh::lean_closure_set(v___f_5845_, 1, v_f_5747_);
                v___x_5846_ = lean_nat_dec_le(v___x_5839_, v___x_5839_);
                if v___x_5846_ == 0 {
                    if v___x_5841_ == 0 {
                        let mut v_toPure_5847_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_inc_ref(v_toApplicative_5829_);
                        crate::leanh::lean_dec_ref(v___f_5845_);
                        crate::leanh::lean_dec_ref(v_params_5832_);
                        crate::leanh::lean_dec_ref(v_inst_5746_);
                        v_toPure_5847_ = crate::leanh::lean_ctor_get(v_toApplicative_5829_, 1);
                        crate::leanh::lean_inc(v_toPure_5847_);
                        crate::leanh::lean_dec_ref(v_toApplicative_5829_);
                        v___x_5848_ = crate::leanh::lean_apply_2(
                            v_toPure_5847_,
                            crate::leanh::lean_box(0),
                            v___x_5840_,
                        );
                        v___x_5849_ = crate::leanh::lean_apply_4(
                            v_toBind_5830_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5848_,
                            v___f_5837_,
                        );
                        return v___x_5849_;
                    } else {
                        let mut v___x_5850_: usize = 0;
                        let mut v___x_5851_: usize = 0;
                        let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5850_ = 0usize;
                        v___x_5851_ = lean_usize_of_nat(v___x_5839_);
                        v___x_5852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_5746_,
                            v___f_5845_,
                            v_params_5832_,
                            v___x_5850_,
                            v___x_5851_,
                            v___x_5840_,
                        );
                        v___x_5853_ = crate::leanh::lean_apply_4(
                            v_toBind_5830_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_5852_,
                            v___f_5837_,
                        );
                        return v___x_5853_;
                    }
                } else {
                    let mut v___x_5854_: usize = 0;
                    let mut v___x_5855_: usize = 0;
                    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5854_ = 0usize;
                    v___x_5855_ = lean_usize_of_nat(v___x_5839_);
                    v___x_5856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_5746_,
                        v___f_5845_,
                        v_params_5832_,
                        v___x_5854_,
                        v___x_5855_,
                        v___x_5840_,
                    );
                    v___x_5857_ = crate::leanh::lean_apply_4(
                        v_toBind_5830_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5856_,
                        v___f_5837_,
                    );
                    return v___x_5857_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___redArg___lam__0(
    mut v_inst_5858_: *mut crate::leanh::LeanObject,
    mut v_f_5859_: *mut crate::leanh::LeanObject,
    mut v_k_5860_: *mut crate::leanh::LeanObject,
    mut v_____r_5861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5862_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5858_, v_f_5859_, v_k_5860_);
    return v___x_5862_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM(
    mut v_m_5863_: *mut crate::leanh::LeanObject,
    mut v_pu_5864_: u8,
    mut v_inst_5865_: *mut crate::leanh::LeanObject,
    mut v_f_5866_: *mut crate::leanh::LeanObject,
    mut v_c_5867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5868_ = l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5865_, v_f_5866_, v_c_5867_);
    return v___x_5868_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___boxed(
    mut v_m_5869_: *mut crate::leanh::LeanObject,
    mut v_pu_5870_: *mut crate::leanh::LeanObject,
    mut v_inst_5871_: *mut crate::leanh::LeanObject,
    mut v_f_5872_: *mut crate::leanh::LeanObject,
    mut v_c_5873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5874_: u8 = 0;
    let mut v_res_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5874_ = (crate::leanh::lean_unbox(v_pu_5870_) as u8);
    v_res_5875_ = l_Lean_Compiler_LCNF_Code_forFVarM(
        v_m_5869_,
        v_pu_boxed_5874_,
        v_inst_5871_,
        v_f_5872_,
        v_c_5873_,
    );
    return v_res_5875_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(
    mut v_pu_5876_: u8,
    mut v_m_5877_: *mut crate::leanh::LeanObject,
    mut v_inst_5878_: *mut crate::leanh::LeanObject,
    mut v_inst_5879_: *mut crate::leanh::LeanObject,
    mut v___y_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5882_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5876_,
        v_inst_5878_,
        v_inst_5879_,
        v___y_5880_,
        v___y_5881_,
    );
    return v___x_5882_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed(
    mut v_pu_5883_: *mut crate::leanh::LeanObject,
    mut v_m_5884_: *mut crate::leanh::LeanObject,
    mut v_inst_5885_: *mut crate::leanh::LeanObject,
    mut v_inst_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5889_: u8 = 0;
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5889_ = (crate::leanh::lean_unbox(v_pu_5883_) as u8);
    v_res_5890_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0(
        v_pu_boxed_5889_,
        v_m_5884_,
        v_inst_5885_,
        v_inst_5886_,
        v___y_5887_,
        v___y_5888_,
    );
    return v_res_5890_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__1(
    mut v_m_5891_: *mut crate::leanh::LeanObject,
    mut v_inst_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5895_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_5892_, v___y_5893_, v___y_5894_);
    return v___x_5895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode(
    mut v_pu_5897_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5898_ = crate::leanh::lean_box((v_pu_5897_) as usize);
    v___f_5899_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCode___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5899_, 0, v___x_5898_);
    v___f_5900_ = l_Lean_Compiler_LCNF_instTraverseFVarCode___closed__0;
    v___x_5901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5901_, 0, v___f_5899_);
    crate::leanh::lean_ctor_set(v___x_5901_, 1, v___f_5900_);
    return v___x_5901_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCode___boxed(
    mut v_pu_5902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5903_: u8 = 0;
    let mut v_res_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5903_ = (crate::leanh::lean_unbox(v_pu_5902_) as u8);
    v_res_5904_ = l_Lean_Compiler_LCNF_instTraverseFVarCode(v_pu_boxed_5903_);
    return v_res_5904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(
    mut v_pu_5905_: u8,
    mut v_decl_5906_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5907_: *mut crate::leanh::LeanObject,
    mut v_params_5908_: *mut crate::leanh::LeanObject,
    mut v_inst_5909_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5911_ = crate::leanh::lean_box((v_pu_5905_) as usize);
    v___x_5912_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___x_5912_, 0, v___x_5911_);
    crate::leanh::lean_closure_set(v___x_5912_, 1, v_decl_5906_);
    crate::leanh::lean_closure_set(v___x_5912_, 2, v_____do__lift_5907_);
    crate::leanh::lean_closure_set(v___x_5912_, 3, v_params_5908_);
    crate::leanh::lean_closure_set(v___x_5912_, 4, v_____do__lift_5910_);
    v___x_5913_ = crate::leanh::lean_apply_2(v_inst_5909_, crate::leanh::lean_box(0), v___x_5912_);
    return v___x_5913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed(
    mut v_pu_5914_: *mut crate::leanh::LeanObject,
    mut v_decl_5915_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5916_: *mut crate::leanh::LeanObject,
    mut v_params_5917_: *mut crate::leanh::LeanObject,
    mut v_inst_5918_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5920_: u8 = 0;
    let mut v_res_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5920_ = (crate::leanh::lean_unbox(v_pu_5914_) as u8);
    v_res_5921_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0(
        v_pu_boxed_5920_,
        v_decl_5915_,
        v_____do__lift_5916_,
        v_params_5917_,
        v_inst_5918_,
        v_____do__lift_5919_,
    );
    return v_res_5921_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(
    mut v_pu_5922_: u8,
    mut v_decl_5923_: *mut crate::leanh::LeanObject,
    mut v_params_5924_: *mut crate::leanh::LeanObject,
    mut v_inst_5925_: *mut crate::leanh::LeanObject,
    mut v_inst_5926_: *mut crate::leanh::LeanObject,
    mut v_f_5927_: *mut crate::leanh::LeanObject,
    mut v_value_5928_: *mut crate::leanh::LeanObject,
    mut v_toBind_5929_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5931_ = crate::leanh::lean_box((v_pu_5922_) as usize);
    crate::leanh::lean_inc(v_inst_5925_);
    v___f_5932_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5932_, 0, v___x_5931_);
    crate::leanh::lean_closure_set(v___f_5932_, 1, v_decl_5923_);
    crate::leanh::lean_closure_set(v___f_5932_, 2, v_____do__lift_5930_);
    crate::leanh::lean_closure_set(v___f_5932_, 3, v_params_5924_);
    crate::leanh::lean_closure_set(v___f_5932_, 4, v_inst_5925_);
    v___x_5933_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_5922_,
        v_inst_5925_,
        v_inst_5926_,
        v_f_5927_,
        v_value_5928_,
    );
    v___x_5934_ = crate::leanh::lean_apply_4(
        v_toBind_5929_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5933_,
        v___f_5932_,
    );
    return v___x_5934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed(
    mut v_pu_5935_: *mut crate::leanh::LeanObject,
    mut v_decl_5936_: *mut crate::leanh::LeanObject,
    mut v_params_5937_: *mut crate::leanh::LeanObject,
    mut v_inst_5938_: *mut crate::leanh::LeanObject,
    mut v_inst_5939_: *mut crate::leanh::LeanObject,
    mut v_f_5940_: *mut crate::leanh::LeanObject,
    mut v_value_5941_: *mut crate::leanh::LeanObject,
    mut v_toBind_5942_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5944_: u8 = 0;
    let mut v_res_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5944_ = (crate::leanh::lean_unbox(v_pu_5935_) as u8);
    v_res_5945_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1(
        v_pu_boxed_5944_,
        v_decl_5936_,
        v_params_5937_,
        v_inst_5938_,
        v_inst_5939_,
        v_f_5940_,
        v_value_5941_,
        v_toBind_5942_,
        v_____do__lift_5943_,
    );
    return v_res_5945_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(
    mut v_pu_5946_: u8,
    mut v_decl_5947_: *mut crate::leanh::LeanObject,
    mut v_inst_5948_: *mut crate::leanh::LeanObject,
    mut v_inst_5949_: *mut crate::leanh::LeanObject,
    mut v_f_5950_: *mut crate::leanh::LeanObject,
    mut v_value_5951_: *mut crate::leanh::LeanObject,
    mut v_toBind_5952_: *mut crate::leanh::LeanObject,
    mut v_type_5953_: *mut crate::leanh::LeanObject,
    mut v_params_5954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5955_ = crate::leanh::lean_box((v_pu_5946_) as usize);
    crate::leanh::lean_inc(v_toBind_5952_);
    crate::leanh::lean_inc(v_f_5950_);
    crate::leanh::lean_inc_ref(v_inst_5949_);
    v___f_5956_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5956_, 0, v___x_5955_);
    crate::leanh::lean_closure_set(v___f_5956_, 1, v_decl_5947_);
    crate::leanh::lean_closure_set(v___f_5956_, 2, v_params_5954_);
    crate::leanh::lean_closure_set(v___f_5956_, 3, v_inst_5948_);
    crate::leanh::lean_closure_set(v___f_5956_, 4, v_inst_5949_);
    crate::leanh::lean_closure_set(v___f_5956_, 5, v_f_5950_);
    crate::leanh::lean_closure_set(v___f_5956_, 6, v_value_5951_);
    crate::leanh::lean_closure_set(v___f_5956_, 7, v_toBind_5952_);
    v___x_5957_ =
        l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_5949_, v_f_5950_, v_type_5953_);
    v___x_5958_ = crate::leanh::lean_apply_4(
        v_toBind_5952_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5957_,
        v___f_5956_,
    );
    return v___x_5958_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed(
    mut v_pu_5959_: *mut crate::leanh::LeanObject,
    mut v_decl_5960_: *mut crate::leanh::LeanObject,
    mut v_inst_5961_: *mut crate::leanh::LeanObject,
    mut v_inst_5962_: *mut crate::leanh::LeanObject,
    mut v_f_5963_: *mut crate::leanh::LeanObject,
    mut v_value_5964_: *mut crate::leanh::LeanObject,
    mut v_toBind_5965_: *mut crate::leanh::LeanObject,
    mut v_type_5966_: *mut crate::leanh::LeanObject,
    mut v_params_5967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5968_: u8 = 0;
    let mut v_res_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5968_ = (crate::leanh::lean_unbox(v_pu_5959_) as u8);
    v_res_5969_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2(
        v_pu_boxed_5968_,
        v_decl_5960_,
        v_inst_5961_,
        v_inst_5962_,
        v_f_5963_,
        v_value_5964_,
        v_toBind_5965_,
        v_type_5966_,
        v_params_5967_,
    );
    return v_res_5969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
    mut v_pu_5970_: u8,
    mut v_inst_5971_: *mut crate::leanh::LeanObject,
    mut v_inst_5972_: *mut crate::leanh::LeanObject,
    mut v_f_5973_: *mut crate::leanh::LeanObject,
    mut v_decl_5974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5983_: usize = 0;
    let mut v___x_5984_: usize = 0;
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_5975_ = crate::leanh::lean_ctor_get(v_inst_5972_, 1);
    crate::leanh::lean_inc_n(v_toBind_5975_, 2);
    v_params_5976_ = crate::leanh::lean_ctor_get(v_decl_5974_, 2);
    crate::leanh::lean_inc_ref(v_params_5976_);
    v_type_5977_ = crate::leanh::lean_ctor_get(v_decl_5974_, 3);
    crate::leanh::lean_inc_ref(v_type_5977_);
    v_value_5978_ = crate::leanh::lean_ctor_get(v_decl_5974_, 4);
    crate::leanh::lean_inc_ref(v_value_5978_);
    v___x_5979_ = crate::leanh::lean_box((v_pu_5970_) as usize);
    crate::leanh::lean_inc(v_f_5973_);
    crate::leanh::lean_inc_ref_n(v_inst_5972_, 2);
    crate::leanh::lean_inc(v_inst_5971_);
    v___f_5980_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5980_, 0, v___x_5979_);
    crate::leanh::lean_closure_set(v___f_5980_, 1, v_decl_5974_);
    crate::leanh::lean_closure_set(v___f_5980_, 2, v_inst_5971_);
    crate::leanh::lean_closure_set(v___f_5980_, 3, v_inst_5972_);
    crate::leanh::lean_closure_set(v___f_5980_, 4, v_f_5973_);
    crate::leanh::lean_closure_set(v___f_5980_, 5, v_value_5978_);
    crate::leanh::lean_closure_set(v___f_5980_, 6, v_toBind_5975_);
    crate::leanh::lean_closure_set(v___f_5980_, 7, v_type_5977_);
    v___x_5981_ = crate::leanh::lean_box((v_pu_5970_) as usize);
    v___x_5982_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_5982_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5982_, 1, v___x_5981_);
    crate::leanh::lean_closure_set(v___x_5982_, 2, v_inst_5971_);
    crate::leanh::lean_closure_set(v___x_5982_, 3, v_inst_5972_);
    crate::leanh::lean_closure_set(v___x_5982_, 4, v_f_5973_);
    v_sz_5983_ = lean_array_size(v_params_5976_);
    v___x_5984_ = 0usize;
    v___x_5985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5972_,
        v___x_5982_,
        v_sz_5983_,
        v___x_5984_,
        v_params_5976_,
    );
    v___x_5986_ = crate::leanh::lean_apply_4(
        v_toBind_5975_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5985_,
        v___f_5980_,
    );
    return v___x_5986_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg___boxed(
    mut v_pu_5987_: *mut crate::leanh::LeanObject,
    mut v_inst_5988_: *mut crate::leanh::LeanObject,
    mut v_inst_5989_: *mut crate::leanh::LeanObject,
    mut v_f_5990_: *mut crate::leanh::LeanObject,
    mut v_decl_5991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5992_: u8 = 0;
    let mut v_res_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5992_ = (crate::leanh::lean_unbox(v_pu_5987_) as u8);
    v_res_5993_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_boxed_5992_,
        v_inst_5988_,
        v_inst_5989_,
        v_f_5990_,
        v_decl_5991_,
    );
    return v_res_5993_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM(
    mut v_m_5994_: *mut crate::leanh::LeanObject,
    mut v_pu_5995_: u8,
    mut v_inst_5996_: *mut crate::leanh::LeanObject,
    mut v_inst_5997_: *mut crate::leanh::LeanObject,
    mut v_f_5998_: *mut crate::leanh::LeanObject,
    mut v_decl_5999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6000_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_5995_,
        v_inst_5996_,
        v_inst_5997_,
        v_f_5998_,
        v_decl_5999_,
    );
    return v___x_6000_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_mapFVarM___boxed(
    mut v_m_6001_: *mut crate::leanh::LeanObject,
    mut v_pu_6002_: *mut crate::leanh::LeanObject,
    mut v_inst_6003_: *mut crate::leanh::LeanObject,
    mut v_inst_6004_: *mut crate::leanh::LeanObject,
    mut v_f_6005_: *mut crate::leanh::LeanObject,
    mut v_decl_6006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6007_: u8 = 0;
    let mut v_res_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6007_ = (crate::leanh::lean_unbox(v_pu_6002_) as u8);
    v_res_6008_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM(
        v_m_6001_,
        v_pu_boxed_6007_,
        v_inst_6003_,
        v_inst_6004_,
        v_f_6005_,
        v_decl_6006_,
    );
    return v_res_6008_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0(
    mut v_inst_6009_: *mut crate::leanh::LeanObject,
    mut v_f_6010_: *mut crate::leanh::LeanObject,
    mut v_value_6011_: *mut crate::leanh::LeanObject,
    mut v_____r_6012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6013_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6009_, v_f_6010_, v_value_6011_);
    return v___x_6013_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1(
    mut v_inst_6014_: *mut crate::leanh::LeanObject,
    mut v_f_6015_: *mut crate::leanh::LeanObject,
    mut v_type_6016_: *mut crate::leanh::LeanObject,
    mut v_toBind_6017_: *mut crate::leanh::LeanObject,
    mut v___f_6018_: *mut crate::leanh::LeanObject,
    mut v_____r_6019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6020_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_6014_, v_f_6015_, v_type_6016_);
    v___x_6021_ = crate::leanh::lean_apply_4(
        v_toBind_6017_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6020_,
        v___f_6018_,
    );
    return v___x_6021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2(
    mut v_inst_6022_: *mut crate::leanh::LeanObject,
    mut v_f_6023_: *mut crate::leanh::LeanObject,
    mut v_x_6024_: *mut crate::leanh::LeanObject,
    mut v___y_6025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6026_ =
        l_Lean_Compiler_LCNF_Param_forFVarM___redArg(v_inst_6022_, v_f_6023_, v___y_6025_);
    return v___x_6026_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
    mut v_inst_6027_: *mut crate::leanh::LeanObject,
    mut v_f_6028_: *mut crate::leanh::LeanObject,
    mut v_decl_6029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: u8 = 0;
    v_toApplicative_6030_ = crate::leanh::lean_ctor_get(v_inst_6027_, 0);
    v_toBind_6031_ = crate::leanh::lean_ctor_get(v_inst_6027_, 1);
    crate::leanh::lean_inc_n(v_toBind_6031_, 2);
    v_params_6032_ = crate::leanh::lean_ctor_get(v_decl_6029_, 2);
    crate::leanh::lean_inc_ref(v_params_6032_);
    v_type_6033_ = crate::leanh::lean_ctor_get(v_decl_6029_, 3);
    crate::leanh::lean_inc_ref(v_type_6033_);
    v_value_6034_ = crate::leanh::lean_ctor_get(v_decl_6029_, 4);
    crate::leanh::lean_inc_ref(v_value_6034_);
    crate::leanh::lean_dec_ref(v_decl_6029_);
    crate::leanh::lean_inc_n(v_f_6028_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_6027_, 2);
    v___f_6035_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6035_, 0, v_inst_6027_);
    crate::leanh::lean_closure_set(v___f_6035_, 1, v_f_6028_);
    crate::leanh::lean_closure_set(v___f_6035_, 2, v_value_6034_);
    v___f_6036_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6036_, 0, v_inst_6027_);
    crate::leanh::lean_closure_set(v___f_6036_, 1, v_f_6028_);
    crate::leanh::lean_closure_set(v___f_6036_, 2, v_type_6033_);
    crate::leanh::lean_closure_set(v___f_6036_, 3, v_toBind_6031_);
    crate::leanh::lean_closure_set(v___f_6036_, 4, v___f_6035_);
    v___x_6037_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6038_ = lean_array_get_size(v_params_6032_);
    v___x_6039_ = crate::leanh::lean_box(0);
    v___x_6040_ = lean_nat_dec_lt(v___x_6037_, v___x_6038_);
    if v___x_6040_ == 0 {
        let mut v_toPure_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_toApplicative_6030_);
        crate::leanh::lean_dec_ref(v_params_6032_);
        crate::leanh::lean_dec(v_f_6028_);
        crate::leanh::lean_dec_ref(v_inst_6027_);
        v_toPure_6041_ = crate::leanh::lean_ctor_get(v_toApplicative_6030_, 1);
        crate::leanh::lean_inc(v_toPure_6041_);
        crate::leanh::lean_dec_ref(v_toApplicative_6030_);
        v___x_6042_ =
            crate::leanh::lean_apply_2(v_toPure_6041_, crate::leanh::lean_box(0), v___x_6039_);
        v___x_6043_ = crate::leanh::lean_apply_4(
            v_toBind_6031_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_6042_,
            v___f_6036_,
        );
        return v___x_6043_;
    } else {
        let mut v___f_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6045_: u8 = 0;
        crate::leanh::lean_inc_ref(v_inst_6027_);
        v___f_6044_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            2,
        );
        crate::leanh::lean_closure_set(v___f_6044_, 0, v_inst_6027_);
        crate::leanh::lean_closure_set(v___f_6044_, 1, v_f_6028_);
        v___x_6045_ = lean_nat_dec_le(v___x_6038_, v___x_6038_);
        if v___x_6045_ == 0 {
            if v___x_6040_ == 0 {
                let mut v_toPure_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_toApplicative_6030_);
                crate::leanh::lean_dec_ref(v___f_6044_);
                crate::leanh::lean_dec_ref(v_params_6032_);
                crate::leanh::lean_dec_ref(v_inst_6027_);
                v_toPure_6046_ = crate::leanh::lean_ctor_get(v_toApplicative_6030_, 1);
                crate::leanh::lean_inc(v_toPure_6046_);
                crate::leanh::lean_dec_ref(v_toApplicative_6030_);
                v___x_6047_ = crate::leanh::lean_apply_2(
                    v_toPure_6046_,
                    crate::leanh::lean_box(0),
                    v___x_6039_,
                );
                v___x_6048_ = crate::leanh::lean_apply_4(
                    v_toBind_6031_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6047_,
                    v___f_6036_,
                );
                return v___x_6048_;
            } else {
                let mut v___x_6049_: usize = 0;
                let mut v___x_6050_: usize = 0;
                let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6049_ = 0usize;
                v___x_6050_ = lean_usize_of_nat(v___x_6038_);
                v___x_6051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_6027_,
                    v___f_6044_,
                    v_params_6032_,
                    v___x_6049_,
                    v___x_6050_,
                    v___x_6039_,
                );
                v___x_6052_ = crate::leanh::lean_apply_4(
                    v_toBind_6031_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6051_,
                    v___f_6036_,
                );
                return v___x_6052_;
            }
        } else {
            let mut v___x_6053_: usize = 0;
            let mut v___x_6054_: usize = 0;
            let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6053_ = 0usize;
            v___x_6054_ = lean_usize_of_nat(v___x_6038_);
            v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_6027_,
                v___f_6044_,
                v_params_6032_,
                v___x_6053_,
                v___x_6054_,
                v___x_6039_,
            );
            v___x_6056_ = crate::leanh::lean_apply_4(
                v_toBind_6031_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6055_,
                v___f_6036_,
            );
            return v___x_6056_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM(
    mut v_m_6057_: *mut crate::leanh::LeanObject,
    mut v_pu_6058_: u8,
    mut v_inst_6059_: *mut crate::leanh::LeanObject,
    mut v_f_6060_: *mut crate::leanh::LeanObject,
    mut v_decl_6061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6062_ =
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_6059_, v_f_6060_, v_decl_6061_);
    return v___x_6062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___boxed(
    mut v_m_6063_: *mut crate::leanh::LeanObject,
    mut v_pu_6064_: *mut crate::leanh::LeanObject,
    mut v_inst_6065_: *mut crate::leanh::LeanObject,
    mut v_f_6066_: *mut crate::leanh::LeanObject,
    mut v_decl_6067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6068_: u8 = 0;
    let mut v_res_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6068_ = (crate::leanh::lean_unbox(v_pu_6064_) as u8);
    v_res_6069_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM(
        v_m_6063_,
        v_pu_boxed_6068_,
        v_inst_6065_,
        v_f_6066_,
        v_decl_6067_,
    );
    return v_res_6069_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(
    mut v_pu_6070_: u8,
    mut v_m_6071_: *mut crate::leanh::LeanObject,
    mut v_inst_6072_: *mut crate::leanh::LeanObject,
    mut v_inst_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6076_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
        v_pu_6070_,
        v_inst_6072_,
        v_inst_6073_,
        v___y_6074_,
        v___y_6075_,
    );
    return v___x_6076_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed(
    mut v_pu_6077_: *mut crate::leanh::LeanObject,
    mut v_m_6078_: *mut crate::leanh::LeanObject,
    mut v_inst_6079_: *mut crate::leanh::LeanObject,
    mut v_inst_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6083_: u8 = 0;
    let mut v_res_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6083_ = (crate::leanh::lean_unbox(v_pu_6077_) as u8);
    v_res_6084_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0(
        v_pu_boxed_6083_,
        v_m_6078_,
        v_inst_6079_,
        v_inst_6080_,
        v___y_6081_,
        v___y_6082_,
    );
    return v_res_6084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__1(
    mut v_m_6085_: *mut crate::leanh::LeanObject,
    mut v_inst_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6089_ =
        l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(v_inst_6086_, v___y_6087_, v___y_6088_);
    return v___x_6089_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(
    mut v_pu_6091_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6092_ = crate::leanh::lean_box((v_pu_6091_) as usize);
    v___f_6093_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6093_, 0, v___x_6092_);
    v___f_6094_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___closed__0;
    v___x_6095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6095_, 0, v___f_6093_);
    crate::leanh::lean_ctor_set(v___x_6095_, 1, v___f_6094_);
    return v___x_6095_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarFunDecl___boxed(
    mut v_pu_6096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6097_: u8 = 0;
    let mut v_res_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6097_ = (crate::leanh::lean_unbox(v_pu_6096_) as u8);
    v_res_6098_ = l_Lean_Compiler_LCNF_instTraverseFVarFunDecl(v_pu_boxed_6097_);
    return v_res_6098_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0(
    mut v_toPure_6099_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6101_, 0, v_____do__lift_6100_);
    v___x_6102_ =
        crate::leanh::lean_apply_2(v_toPure_6099_, crate::leanh::lean_box(0), v___x_6101_);
    return v___x_6102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1(
    mut v_toPure_6103_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6105_, 0, v_____do__lift_6104_);
    v___x_6106_ =
        crate::leanh::lean_apply_2(v_toPure_6103_, crate::leanh::lean_box(0), v___x_6105_);
    return v___x_6106_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2(
    mut v_toPure_6107_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6109_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6109_, 0, v_____do__lift_6108_);
    v___x_6110_ =
        crate::leanh::lean_apply_2(v_toPure_6107_, crate::leanh::lean_box(0), v___x_6109_);
    return v___x_6110_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3(
    mut v_____do__lift_6111_: *mut crate::leanh::LeanObject,
    mut v_i_6112_: *mut crate::leanh::LeanObject,
    mut v_toPure_6113_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6115_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6115_, 0, v_____do__lift_6111_);
    crate::leanh::lean_ctor_set(v___x_6115_, 1, v_i_6112_);
    crate::leanh::lean_ctor_set(v___x_6115_, 2, v_____do__lift_6114_);
    v___x_6116_ =
        crate::leanh::lean_apply_2(v_toPure_6113_, crate::leanh::lean_box(0), v___x_6115_);
    return v___x_6116_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(
    mut v_i_6117_: *mut crate::leanh::LeanObject,
    mut v_toPure_6118_: *mut crate::leanh::LeanObject,
    mut v_pu_6119_: u8,
    mut v_inst_6120_: *mut crate::leanh::LeanObject,
    mut v_f_6121_: *mut crate::leanh::LeanObject,
    mut v_y_6122_: *mut crate::leanh::LeanObject,
    mut v_toBind_6123_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6125_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__3 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6125_, 0, v_____do__lift_6124_);
    crate::leanh::lean_closure_set(v___f_6125_, 1, v_i_6117_);
    crate::leanh::lean_closure_set(v___f_6125_, 2, v_toPure_6118_);
    v___x_6126_ =
        l_Lean_Compiler_LCNF_Arg_mapFVarM___redArg(v_pu_6119_, v_inst_6120_, v_f_6121_, v_y_6122_);
    v___x_6127_ = crate::leanh::lean_apply_4(
        v_toBind_6123_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6126_,
        v___f_6125_,
    );
    return v___x_6127_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed(
    mut v_i_6128_: *mut crate::leanh::LeanObject,
    mut v_toPure_6129_: *mut crate::leanh::LeanObject,
    mut v_pu_6130_: *mut crate::leanh::LeanObject,
    mut v_inst_6131_: *mut crate::leanh::LeanObject,
    mut v_f_6132_: *mut crate::leanh::LeanObject,
    mut v_y_6133_: *mut crate::leanh::LeanObject,
    mut v_toBind_6134_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6136_: u8 = 0;
    let mut v_res_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6136_ = (crate::leanh::lean_unbox(v_pu_6130_) as u8);
    v_res_6137_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4(
        v_i_6128_,
        v_toPure_6129_,
        v_pu_boxed_6136_,
        v_inst_6131_,
        v_f_6132_,
        v_y_6133_,
        v_toBind_6134_,
        v_____do__lift_6135_,
    );
    return v_res_6137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5(
    mut v_____do__lift_6138_: *mut crate::leanh::LeanObject,
    mut v_i_6139_: *mut crate::leanh::LeanObject,
    mut v_toPure_6140_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6142_ = crate::leanh::lean_alloc_ctor(4, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6142_, 0, v_____do__lift_6138_);
    crate::leanh::lean_ctor_set(v___x_6142_, 1, v_i_6139_);
    crate::leanh::lean_ctor_set(v___x_6142_, 2, v_____do__lift_6141_);
    v___x_6143_ =
        crate::leanh::lean_apply_2(v_toPure_6140_, crate::leanh::lean_box(0), v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6(
    mut v_i_6144_: *mut crate::leanh::LeanObject,
    mut v_toPure_6145_: *mut crate::leanh::LeanObject,
    mut v_f_6146_: *mut crate::leanh::LeanObject,
    mut v_y_6147_: *mut crate::leanh::LeanObject,
    mut v_toBind_6148_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6150_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6150_, 0, v_____do__lift_6149_);
    crate::leanh::lean_closure_set(v___f_6150_, 1, v_i_6144_);
    crate::leanh::lean_closure_set(v___f_6150_, 2, v_toPure_6145_);
    v___x_6151_ = crate::leanh::lean_apply_1(v_f_6146_, v_y_6147_);
    v___x_6152_ = crate::leanh::lean_apply_4(
        v_toBind_6148_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6151_,
        v___f_6150_,
    );
    return v___x_6152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7(
    mut v_____do__lift_6153_: *mut crate::leanh::LeanObject,
    mut v_i_6154_: *mut crate::leanh::LeanObject,
    mut v_offset_6155_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6156_: *mut crate::leanh::LeanObject,
    mut v_toPure_6157_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6159_ = crate::leanh::lean_alloc_ctor(5, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6159_, 0, v_____do__lift_6153_);
    crate::leanh::lean_ctor_set(v___x_6159_, 1, v_i_6154_);
    crate::leanh::lean_ctor_set(v___x_6159_, 2, v_offset_6155_);
    crate::leanh::lean_ctor_set(v___x_6159_, 3, v_____do__lift_6156_);
    crate::leanh::lean_ctor_set(v___x_6159_, 4, v_____do__lift_6158_);
    v___x_6160_ =
        crate::leanh::lean_apply_2(v_toPure_6157_, crate::leanh::lean_box(0), v___x_6159_);
    return v___x_6160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8(
    mut v_____do__lift_6161_: *mut crate::leanh::LeanObject,
    mut v_i_6162_: *mut crate::leanh::LeanObject,
    mut v_offset_6163_: *mut crate::leanh::LeanObject,
    mut v_toPure_6164_: *mut crate::leanh::LeanObject,
    mut v_inst_6165_: *mut crate::leanh::LeanObject,
    mut v_f_6166_: *mut crate::leanh::LeanObject,
    mut v_ty_6167_: *mut crate::leanh::LeanObject,
    mut v_toBind_6168_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6170_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__7 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6170_, 0, v_____do__lift_6161_);
    crate::leanh::lean_closure_set(v___f_6170_, 1, v_i_6162_);
    crate::leanh::lean_closure_set(v___f_6170_, 2, v_offset_6163_);
    crate::leanh::lean_closure_set(v___f_6170_, 3, v_____do__lift_6169_);
    crate::leanh::lean_closure_set(v___f_6170_, 4, v_toPure_6164_);
    v___x_6171_ = l_Lean_Compiler_LCNF_Expr_mapFVarM___redArg(v_inst_6165_, v_f_6166_, v_ty_6167_);
    v___x_6172_ = crate::leanh::lean_apply_4(
        v_toBind_6168_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6171_,
        v___f_6170_,
    );
    return v___x_6172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9(
    mut v_i_6173_: *mut crate::leanh::LeanObject,
    mut v_offset_6174_: *mut crate::leanh::LeanObject,
    mut v_toPure_6175_: *mut crate::leanh::LeanObject,
    mut v_inst_6176_: *mut crate::leanh::LeanObject,
    mut v_f_6177_: *mut crate::leanh::LeanObject,
    mut v_ty_6178_: *mut crate::leanh::LeanObject,
    mut v_toBind_6179_: *mut crate::leanh::LeanObject,
    mut v_y_6180_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_6179_);
    crate::leanh::lean_inc(v_f_6177_);
    v___f_6182_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_6182_, 0, v_____do__lift_6181_);
    crate::leanh::lean_closure_set(v___f_6182_, 1, v_i_6173_);
    crate::leanh::lean_closure_set(v___f_6182_, 2, v_offset_6174_);
    crate::leanh::lean_closure_set(v___f_6182_, 3, v_toPure_6175_);
    crate::leanh::lean_closure_set(v___f_6182_, 4, v_inst_6176_);
    crate::leanh::lean_closure_set(v___f_6182_, 5, v_f_6177_);
    crate::leanh::lean_closure_set(v___f_6182_, 6, v_ty_6178_);
    crate::leanh::lean_closure_set(v___f_6182_, 7, v_toBind_6179_);
    v___x_6183_ = crate::leanh::lean_apply_1(v_f_6177_, v_y_6180_);
    v___x_6184_ = crate::leanh::lean_apply_4(
        v_toBind_6179_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6183_,
        v___f_6182_,
    );
    return v___x_6184_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10(
    mut v_cidx_6185_: *mut crate::leanh::LeanObject,
    mut v_toPure_6186_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6188_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6188_, 0, v_____do__lift_6187_);
    crate::leanh::lean_ctor_set(v___x_6188_, 1, v_cidx_6185_);
    v___x_6189_ =
        crate::leanh::lean_apply_2(v_toPure_6186_, crate::leanh::lean_box(0), v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(
    mut v_n_6190_: *mut crate::leanh::LeanObject,
    mut v_check_6191_: u8,
    mut v_persistent_6192_: u8,
    mut v_toPure_6193_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6195_ = crate::leanh::lean_alloc_ctor(7, 2, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_6195_, 0, v_____do__lift_6194_);
    crate::leanh::lean_ctor_set(v___x_6195_, 1, v_n_6190_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_check_6191_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        v_persistent_6192_,
    );
    v___x_6196_ =
        crate::leanh::lean_apply_2(v_toPure_6193_, crate::leanh::lean_box(0), v___x_6195_);
    return v___x_6196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed(
    mut v_n_6197_: *mut crate::leanh::LeanObject,
    mut v_check_6198_: *mut crate::leanh::LeanObject,
    mut v_persistent_6199_: *mut crate::leanh::LeanObject,
    mut v_toPure_6200_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_923__boxed_6202_: u8 = 0;
    let mut v_persistent_924__boxed_6203_: u8 = 0;
    let mut v_res_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_923__boxed_6202_ = (crate::leanh::lean_unbox(v_check_6198_) as u8);
    v_persistent_924__boxed_6203_ = (crate::leanh::lean_unbox(v_persistent_6199_) as u8);
    v_res_6204_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11(
        v_n_6197_,
        v_check_923__boxed_6202_,
        v_persistent_924__boxed_6203_,
        v_toPure_6200_,
        v_____do__lift_6201_,
    );
    return v_res_6204_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(
    mut v_n_6205_: *mut crate::leanh::LeanObject,
    mut v_check_6206_: u8,
    mut v_persistent_6207_: u8,
    mut v_objs_x3f_6208_: *mut crate::leanh::LeanObject,
    mut v_toPure_6209_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6211_ = crate::leanh::lean_alloc_ctor(8, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_6211_, 0, v_____do__lift_6210_);
    crate::leanh::lean_ctor_set(v___x_6211_, 1, v_n_6205_);
    crate::leanh::lean_ctor_set(v___x_6211_, 2, v_objs_x3f_6208_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6211_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_check_6206_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6211_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v_persistent_6207_,
    );
    v___x_6212_ =
        crate::leanh::lean_apply_2(v_toPure_6209_, crate::leanh::lean_box(0), v___x_6211_);
    return v___x_6212_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed(
    mut v_n_6213_: *mut crate::leanh::LeanObject,
    mut v_check_6214_: *mut crate::leanh::LeanObject,
    mut v_persistent_6215_: *mut crate::leanh::LeanObject,
    mut v_objs_x3f_6216_: *mut crate::leanh::LeanObject,
    mut v_toPure_6217_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_check_939__boxed_6219_: u8 = 0;
    let mut v_persistent_940__boxed_6220_: u8 = 0;
    let mut v_res_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_check_939__boxed_6219_ = (crate::leanh::lean_unbox(v_check_6214_) as u8);
    v_persistent_940__boxed_6220_ = (crate::leanh::lean_unbox(v_persistent_6215_) as u8);
    v_res_6221_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12(
        v_n_6213_,
        v_check_939__boxed_6219_,
        v_persistent_940__boxed_6220_,
        v_objs_x3f_6216_,
        v_toPure_6217_,
        v_____do__lift_6218_,
    );
    return v_res_6221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13(
    mut v_toPure_6222_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6224_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6224_, 0, v_____do__lift_6223_);
    v___x_6225_ =
        crate::leanh::lean_apply_2(v_toPure_6222_, crate::leanh::lean_box(0), v___x_6224_);
    return v___x_6225_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(
    mut v_pu_6226_: u8,
    mut v_m_6227_: *mut crate::leanh::LeanObject,
    mut v_inst_6228_: *mut crate::leanh::LeanObject,
    mut v_inst_6229_: *mut crate::leanh::LeanObject,
    mut v_f_6230_: *mut crate::leanh::LeanObject,
    mut v_decl_6231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_decl_6231_) {
        0 => {
            let mut v_toApplicative_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6232_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6233_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6233_);
            v_toPure_6234_ = crate::leanh::lean_ctor_get(v_toApplicative_6232_, 1);
            v_decl_6235_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc_ref(v_decl_6235_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_toPure_6234_);
            v___f_6236_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__0 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_6236_, 0, v_toPure_6234_);
            v___x_6237_ = l_Lean_Compiler_LCNF_LetDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6235_,
            );
            v___x_6238_ = crate::leanh::lean_apply_4(
                v_toBind_6233_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6237_,
                v___f_6236_,
            );
            return v___x_6238_;
        }
        1 => {
            let mut v_toApplicative_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6239_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6240_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6240_);
            v_toPure_6241_ = crate::leanh::lean_ctor_get(v_toApplicative_6239_, 1);
            v_decl_6242_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc_ref(v_decl_6242_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_toPure_6241_);
            v___f_6243_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__1 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_6243_, 0, v_toPure_6241_);
            v___x_6244_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6242_,
            );
            v___x_6245_ = crate::leanh::lean_apply_4(
                v_toBind_6240_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6244_,
                v___f_6243_,
            );
            return v___x_6245_;
        }
        2 => {
            let mut v_toApplicative_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_decl_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6246_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            v_toBind_6247_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6247_);
            v_toPure_6248_ = crate::leanh::lean_ctor_get(v_toApplicative_6246_, 1);
            v_decl_6249_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc_ref(v_decl_6249_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_toPure_6248_);
            v___f_6250_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__2 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_6250_, 0, v_toPure_6248_);
            v___x_6251_ = l_Lean_Compiler_LCNF_FunDecl_mapFVarM___redArg(
                v_pu_6226_,
                v_inst_6228_,
                v_inst_6229_,
                v_f_6230_,
                v_decl_6249_,
            );
            v___x_6252_ = crate::leanh::lean_apply_4(
                v_toBind_6247_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6251_,
                v___f_6250_,
            );
            return v___x_6252_;
        }
        3 => {
            let mut v_toApplicative_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6253_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6254_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc_n(v_toBind_6254_, 2);
            v_toPure_6255_ = crate::leanh::lean_ctor_get(v_toApplicative_6253_, 1);
            crate::leanh::lean_inc(v_toPure_6255_);
            v_fvarId_6256_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6256_);
            v_i_6257_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_i_6257_);
            v_y_6258_ = crate::leanh::lean_ctor_get(v_decl_6231_, 2);
            crate::leanh::lean_inc(v_y_6258_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 3);
            v___x_6259_ = crate::leanh::lean_box((v_pu_6226_) as usize);
            crate::leanh::lean_inc(v_f_6230_);
            v___f_6260_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__4___boxed
                    as *mut core::ffi::c_void,
                8,
                7,
            );
            crate::leanh::lean_closure_set(v___f_6260_, 0, v_i_6257_);
            crate::leanh::lean_closure_set(v___f_6260_, 1, v_toPure_6255_);
            crate::leanh::lean_closure_set(v___f_6260_, 2, v___x_6259_);
            crate::leanh::lean_closure_set(v___f_6260_, 3, v_inst_6229_);
            crate::leanh::lean_closure_set(v___f_6260_, 4, v_f_6230_);
            crate::leanh::lean_closure_set(v___f_6260_, 5, v_y_6258_);
            crate::leanh::lean_closure_set(v___f_6260_, 6, v_toBind_6254_);
            v___x_6261_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6256_);
            v___x_6262_ = crate::leanh::lean_apply_4(
                v_toBind_6254_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6261_,
                v___f_6260_,
            );
            return v___x_6262_;
        }
        4 => {
            let mut v_toApplicative_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6263_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_6263_);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6264_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc_n(v_toBind_6264_, 2);
            crate::leanh::lean_dec_ref(v_inst_6229_);
            v_toPure_6265_ = crate::leanh::lean_ctor_get(v_toApplicative_6263_, 1);
            crate::leanh::lean_inc(v_toPure_6265_);
            crate::leanh::lean_dec_ref(v_toApplicative_6263_);
            v_fvarId_6266_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6266_);
            v_i_6267_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_i_6267_);
            v_y_6268_ = crate::leanh::lean_ctor_get(v_decl_6231_, 2);
            crate::leanh::lean_inc(v_y_6268_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 3);
            crate::leanh::lean_inc(v_f_6230_);
            v___f_6269_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__6 as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_6269_, 0, v_i_6267_);
            crate::leanh::lean_closure_set(v___f_6269_, 1, v_toPure_6265_);
            crate::leanh::lean_closure_set(v___f_6269_, 2, v_f_6230_);
            crate::leanh::lean_closure_set(v___f_6269_, 3, v_y_6268_);
            crate::leanh::lean_closure_set(v___f_6269_, 4, v_toBind_6264_);
            v___x_6270_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6266_);
            v___x_6271_ = crate::leanh::lean_apply_4(
                v_toBind_6264_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6270_,
                v___f_6269_,
            );
            return v___x_6271_;
        }
        5 => {
            let mut v_toApplicative_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_offset_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6272_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6273_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc_n(v_toBind_6273_, 2);
            v_toPure_6274_ = crate::leanh::lean_ctor_get(v_toApplicative_6272_, 1);
            crate::leanh::lean_inc(v_toPure_6274_);
            v_fvarId_6275_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6275_);
            v_i_6276_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_i_6276_);
            v_offset_6277_ = crate::leanh::lean_ctor_get(v_decl_6231_, 2);
            crate::leanh::lean_inc(v_offset_6277_);
            v_y_6278_ = crate::leanh::lean_ctor_get(v_decl_6231_, 3);
            crate::leanh::lean_inc(v_y_6278_);
            v_ty_6279_ = crate::leanh::lean_ctor_get(v_decl_6231_, 4);
            crate::leanh::lean_inc_ref(v_ty_6279_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 5);
            crate::leanh::lean_inc(v_f_6230_);
            v___f_6280_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__9 as *mut core::ffi::c_void,
                9,
                8,
            );
            crate::leanh::lean_closure_set(v___f_6280_, 0, v_i_6276_);
            crate::leanh::lean_closure_set(v___f_6280_, 1, v_offset_6277_);
            crate::leanh::lean_closure_set(v___f_6280_, 2, v_toPure_6274_);
            crate::leanh::lean_closure_set(v___f_6280_, 3, v_inst_6229_);
            crate::leanh::lean_closure_set(v___f_6280_, 4, v_f_6230_);
            crate::leanh::lean_closure_set(v___f_6280_, 5, v_ty_6279_);
            crate::leanh::lean_closure_set(v___f_6280_, 6, v_toBind_6273_);
            crate::leanh::lean_closure_set(v___f_6280_, 7, v_y_6278_);
            v___x_6281_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6275_);
            v___x_6282_ = crate::leanh::lean_apply_4(
                v_toBind_6273_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6281_,
                v___f_6280_,
            );
            return v___x_6282_;
        }
        6 => {
            let mut v_toApplicative_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cidx_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6283_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_6283_);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6284_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6284_);
            crate::leanh::lean_dec_ref(v_inst_6229_);
            v_toPure_6285_ = crate::leanh::lean_ctor_get(v_toApplicative_6283_, 1);
            crate::leanh::lean_inc(v_toPure_6285_);
            crate::leanh::lean_dec_ref(v_toApplicative_6283_);
            v_fvarId_6286_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6286_);
            v_cidx_6287_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_cidx_6287_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 2);
            v___f_6288_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__10 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_6288_, 0, v_cidx_6287_);
            crate::leanh::lean_closure_set(v___f_6288_, 1, v_toPure_6285_);
            v___x_6289_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6286_);
            v___x_6290_ = crate::leanh::lean_apply_4(
                v_toBind_6284_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6289_,
                v___f_6288_,
            );
            return v___x_6290_;
        }
        7 => {
            let mut v_toApplicative_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_check_6296_: u8 = 0;
            let mut v_persistent_6297_: u8 = 0;
            let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6291_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_6291_);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6292_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6292_);
            crate::leanh::lean_dec_ref(v_inst_6229_);
            v_toPure_6293_ = crate::leanh::lean_ctor_get(v_toApplicative_6291_, 1);
            crate::leanh::lean_inc(v_toPure_6293_);
            crate::leanh::lean_dec_ref(v_toApplicative_6291_);
            v_fvarId_6294_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6294_);
            v_n_6295_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_n_6295_);
            v_check_6296_ = crate::leanh::lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            v_persistent_6297_ = crate::leanh::lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 2);
            v___x_6298_ = crate::leanh::lean_box((v_check_6296_) as usize);
            v___x_6299_ = crate::leanh::lean_box((v_persistent_6297_) as usize);
            v___f_6300_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__11___boxed
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_6300_, 0, v_n_6295_);
            crate::leanh::lean_closure_set(v___f_6300_, 1, v___x_6298_);
            crate::leanh::lean_closure_set(v___f_6300_, 2, v___x_6299_);
            crate::leanh::lean_closure_set(v___f_6300_, 3, v_toPure_6293_);
            v___x_6301_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6294_);
            v___x_6302_ = crate::leanh::lean_apply_4(
                v_toBind_6292_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6301_,
                v___f_6300_,
            );
            return v___x_6302_;
        }
        8 => {
            let mut v_toApplicative_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_check_6308_: u8 = 0;
            let mut v_persistent_6309_: u8 = 0;
            let mut v_objs_x3f_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6303_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_6303_);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6304_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6304_);
            crate::leanh::lean_dec_ref(v_inst_6229_);
            v_toPure_6305_ = crate::leanh::lean_ctor_get(v_toApplicative_6303_, 1);
            crate::leanh::lean_inc(v_toPure_6305_);
            crate::leanh::lean_dec_ref(v_toApplicative_6303_);
            v_fvarId_6306_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6306_);
            v_n_6307_ = crate::leanh::lean_ctor_get(v_decl_6231_, 1);
            crate::leanh::lean_inc(v_n_6307_);
            v_check_6308_ = crate::leanh::lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_persistent_6309_ = crate::leanh::lean_ctor_get_uint8(
                v_decl_6231_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
            );
            v_objs_x3f_6310_ = crate::leanh::lean_ctor_get(v_decl_6231_, 2);
            crate::leanh::lean_inc(v_objs_x3f_6310_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 3);
            v___x_6311_ = crate::leanh::lean_box((v_check_6308_) as usize);
            v___x_6312_ = crate::leanh::lean_box((v_persistent_6309_) as usize);
            v___f_6313_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__12___boxed
                    as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_6313_, 0, v_n_6307_);
            crate::leanh::lean_closure_set(v___f_6313_, 1, v___x_6311_);
            crate::leanh::lean_closure_set(v___f_6313_, 2, v___x_6312_);
            crate::leanh::lean_closure_set(v___f_6313_, 3, v_objs_x3f_6310_);
            crate::leanh::lean_closure_set(v___f_6313_, 4, v_toPure_6305_);
            v___x_6314_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6306_);
            v___x_6315_ = crate::leanh::lean_apply_4(
                v_toBind_6304_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6314_,
                v___f_6313_,
            );
            return v___x_6315_;
        }
        _ => {
            let mut v_toApplicative_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6316_ = crate::leanh::lean_ctor_get(v_inst_6229_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_6316_);
            crate::leanh::lean_dec(v_inst_6228_);
            v_toBind_6317_ = crate::leanh::lean_ctor_get(v_inst_6229_, 1);
            crate::leanh::lean_inc(v_toBind_6317_);
            crate::leanh::lean_dec_ref(v_inst_6229_);
            v_toPure_6318_ = crate::leanh::lean_ctor_get(v_toApplicative_6316_, 1);
            crate::leanh::lean_inc(v_toPure_6318_);
            crate::leanh::lean_dec_ref(v_toApplicative_6316_);
            v_fvarId_6319_ = crate::leanh::lean_ctor_get(v_decl_6231_, 0);
            crate::leanh::lean_inc(v_fvarId_6319_);
            crate::leanh::lean_dec_ref_known(v_decl_6231_, 1);
            v___f_6320_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__13 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_6320_, 0, v_toPure_6318_);
            v___x_6321_ = crate::leanh::lean_apply_1(v_f_6230_, v_fvarId_6319_);
            v___x_6322_ = crate::leanh::lean_apply_4(
                v_toBind_6317_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6321_,
                v___f_6320_,
            );
            return v___x_6322_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed(
    mut v_pu_6323_: *mut crate::leanh::LeanObject,
    mut v_m_6324_: *mut crate::leanh::LeanObject,
    mut v_inst_6325_: *mut crate::leanh::LeanObject,
    mut v_inst_6326_: *mut crate::leanh::LeanObject,
    mut v_f_6327_: *mut crate::leanh::LeanObject,
    mut v_decl_6328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6329_: u8 = 0;
    let mut v_res_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6329_ = (crate::leanh::lean_unbox(v_pu_6323_) as u8);
    v_res_6330_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14(
        v_pu_boxed_6329_,
        v_m_6324_,
        v_inst_6325_,
        v_inst_6326_,
        v_f_6327_,
        v_decl_6328_,
    );
    return v_res_6330_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15(
    mut v_inst_6331_: *mut crate::leanh::LeanObject,
    mut v_f_6332_: *mut crate::leanh::LeanObject,
    mut v_y_6333_: *mut crate::leanh::LeanObject,
    mut v_____r_6334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6335_ = l_Lean_Compiler_LCNF_Arg_forFVarM___redArg(v_inst_6331_, v_f_6332_, v_y_6333_);
    return v___x_6335_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16(
    mut v_f_6336_: *mut crate::leanh::LeanObject,
    mut v_y_6337_: *mut crate::leanh::LeanObject,
    mut v_____r_6338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6339_ = crate::leanh::lean_apply_1(v_f_6336_, v_y_6337_);
    return v___x_6339_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17(
    mut v_inst_6340_: *mut crate::leanh::LeanObject,
    mut v_f_6341_: *mut crate::leanh::LeanObject,
    mut v_ty_6342_: *mut crate::leanh::LeanObject,
    mut v_____r_6343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6344_ = l_Lean_Compiler_LCNF_Expr_forFVarM___redArg(v_inst_6340_, v_f_6341_, v_ty_6342_);
    return v___x_6344_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18(
    mut v_f_6345_: *mut crate::leanh::LeanObject,
    mut v_y_6346_: *mut crate::leanh::LeanObject,
    mut v_toBind_6347_: *mut crate::leanh::LeanObject,
    mut v___f_6348_: *mut crate::leanh::LeanObject,
    mut v_____r_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6350_ = crate::leanh::lean_apply_1(v_f_6345_, v_y_6346_);
    v___x_6351_ = crate::leanh::lean_apply_4(
        v_toBind_6347_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6350_,
        v___f_6348_,
    );
    return v___x_6351_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__19(
    mut v_m_6352_: *mut crate::leanh::LeanObject,
    mut v_inst_6353_: *mut crate::leanh::LeanObject,
    mut v_f_6354_: *mut crate::leanh::LeanObject,
    mut v_decl_6355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_decl_6355_) {
        0 => {
            let mut v_decl_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6356_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc_ref(v_decl_6356_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6357_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6356_,
            );
            return v___x_6357_;
        }
        1 => {
            let mut v_decl_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6358_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc_ref(v_decl_6358_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6359_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6358_,
            );
            return v___x_6359_;
        }
        2 => {
            let mut v_decl_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6360_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc_ref(v_decl_6360_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 1);
            v___x_6361_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg(
                v_inst_6353_,
                v_f_6354_,
                v_decl_6360_,
            );
            return v___x_6361_;
        }
        3 => {
            let mut v_toBind_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_6362_ = crate::leanh::lean_ctor_get(v_inst_6353_, 1);
            crate::leanh::lean_inc(v_toBind_6362_);
            v_fvarId_6363_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc(v_fvarId_6363_);
            v_y_6364_ = crate::leanh::lean_ctor_get(v_decl_6355_, 2);
            crate::leanh::lean_inc(v_y_6364_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 3);
            crate::leanh::lean_inc(v_f_6354_);
            v___f_6365_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__15 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_6365_, 0, v_inst_6353_);
            crate::leanh::lean_closure_set(v___f_6365_, 1, v_f_6354_);
            crate::leanh::lean_closure_set(v___f_6365_, 2, v_y_6364_);
            v___x_6366_ = crate::leanh::lean_apply_1(v_f_6354_, v_fvarId_6363_);
            v___x_6367_ = crate::leanh::lean_apply_4(
                v_toBind_6362_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6366_,
                v___f_6365_,
            );
            return v___x_6367_;
        }
        4 => {
            let mut v_toBind_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_6368_ = crate::leanh::lean_ctor_get(v_inst_6353_, 1);
            crate::leanh::lean_inc(v_toBind_6368_);
            crate::leanh::lean_dec_ref(v_inst_6353_);
            v_fvarId_6369_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc(v_fvarId_6369_);
            v_y_6370_ = crate::leanh::lean_ctor_get(v_decl_6355_, 2);
            crate::leanh::lean_inc(v_y_6370_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 3);
            crate::leanh::lean_inc(v_f_6354_);
            v___f_6371_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__16 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_6371_, 0, v_f_6354_);
            crate::leanh::lean_closure_set(v___f_6371_, 1, v_y_6370_);
            v___x_6372_ = crate::leanh::lean_apply_1(v_f_6354_, v_fvarId_6369_);
            v___x_6373_ = crate::leanh::lean_apply_4(
                v_toBind_6368_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6372_,
                v___f_6371_,
            );
            return v___x_6373_;
        }
        5 => {
            let mut v_toBind_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fvarId_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_6374_ = crate::leanh::lean_ctor_get(v_inst_6353_, 1);
            crate::leanh::lean_inc_n(v_toBind_6374_, 2);
            v_fvarId_6375_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc(v_fvarId_6375_);
            v_y_6376_ = crate::leanh::lean_ctor_get(v_decl_6355_, 3);
            crate::leanh::lean_inc(v_y_6376_);
            v_ty_6377_ = crate::leanh::lean_ctor_get(v_decl_6355_, 4);
            crate::leanh::lean_inc_ref(v_ty_6377_);
            crate::leanh::lean_dec_ref_known(v_decl_6355_, 5);
            crate::leanh::lean_inc_n(v_f_6354_, 2);
            v___f_6378_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__17 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_6378_, 0, v_inst_6353_);
            crate::leanh::lean_closure_set(v___f_6378_, 1, v_f_6354_);
            crate::leanh::lean_closure_set(v___f_6378_, 2, v_ty_6377_);
            v___f_6379_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__18 as *mut core::ffi::c_void,
                5,
                4,
            );
            crate::leanh::lean_closure_set(v___f_6379_, 0, v_f_6354_);
            crate::leanh::lean_closure_set(v___f_6379_, 1, v_y_6376_);
            crate::leanh::lean_closure_set(v___f_6379_, 2, v_toBind_6374_);
            crate::leanh::lean_closure_set(v___f_6379_, 3, v___f_6378_);
            v___x_6380_ = crate::leanh::lean_apply_1(v_f_6354_, v_fvarId_6375_);
            v___x_6381_ = crate::leanh::lean_apply_4(
                v_toBind_6374_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6380_,
                v___f_6379_,
            );
            return v___x_6381_;
        }
        _ => {
            let mut v_fvarId_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_6353_);
            v_fvarId_6382_ = crate::leanh::lean_ctor_get(v_decl_6355_, 0);
            crate::leanh::lean_inc(v_fvarId_6382_);
            crate::leanh::lean_dec_ref(v_decl_6355_);
            v___x_6383_ = crate::leanh::lean_apply_1(v_f_6354_, v_fvarId_6382_);
            return v___x_6383_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(
    mut v_pu_6385_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6386_ = crate::leanh::lean_box((v_pu_6385_) as usize);
    v___f_6387_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___lam__14___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6387_, 0, v___x_6386_);
    v___f_6388_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___closed__0;
    v___x_6389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6389_, 0, v___f_6387_);
    crate::leanh::lean_ctor_set(v___x_6389_, 1, v___f_6388_);
    return v___x_6389_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl___boxed(
    mut v_pu_6390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6391_: u8 = 0;
    let mut v_res_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6391_ = (crate::leanh::lean_unbox(v_pu_6390_) as u8);
    v_res_6392_ = l_Lean_Compiler_LCNF_instTraverseFVarCodeDecl(v_pu_boxed_6391_);
    return v_res_6392_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0(
    mut v_ctorName_6393_: *mut crate::leanh::LeanObject,
    mut v_params_6394_: *mut crate::leanh::LeanObject,
    mut v_toPure_6395_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6397_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6397_, 0, v_ctorName_6393_);
    crate::leanh::lean_ctor_set(v___x_6397_, 1, v_params_6394_);
    crate::leanh::lean_ctor_set(v___x_6397_, 2, v_____do__lift_6396_);
    v___x_6398_ =
        crate::leanh::lean_apply_2(v_toPure_6395_, crate::leanh::lean_box(0), v___x_6397_);
    return v___x_6398_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(
    mut v_ctorName_6399_: *mut crate::leanh::LeanObject,
    mut v_toPure_6400_: *mut crate::leanh::LeanObject,
    mut v_pu_6401_: u8,
    mut v_inst_6402_: *mut crate::leanh::LeanObject,
    mut v_inst_6403_: *mut crate::leanh::LeanObject,
    mut v_f_6404_: *mut crate::leanh::LeanObject,
    mut v_code_6405_: *mut crate::leanh::LeanObject,
    mut v_toBind_6406_: *mut crate::leanh::LeanObject,
    mut v_params_6407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6408_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6408_, 0, v_ctorName_6399_);
    crate::leanh::lean_closure_set(v___f_6408_, 1, v_params_6407_);
    crate::leanh::lean_closure_set(v___f_6408_, 2, v_toPure_6400_);
    v___x_6409_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
        v_pu_6401_,
        v_inst_6402_,
        v_inst_6403_,
        v_f_6404_,
        v_code_6405_,
    );
    v___x_6410_ = crate::leanh::lean_apply_4(
        v_toBind_6406_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6409_,
        v___f_6408_,
    );
    return v___x_6410_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed(
    mut v_ctorName_6411_: *mut crate::leanh::LeanObject,
    mut v_toPure_6412_: *mut crate::leanh::LeanObject,
    mut v_pu_6413_: *mut crate::leanh::LeanObject,
    mut v_inst_6414_: *mut crate::leanh::LeanObject,
    mut v_inst_6415_: *mut crate::leanh::LeanObject,
    mut v_f_6416_: *mut crate::leanh::LeanObject,
    mut v_code_6417_: *mut crate::leanh::LeanObject,
    mut v_toBind_6418_: *mut crate::leanh::LeanObject,
    mut v_params_6419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6420_: u8 = 0;
    let mut v_res_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6420_ = (crate::leanh::lean_unbox(v_pu_6413_) as u8);
    v_res_6421_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1(
        v_ctorName_6411_,
        v_toPure_6412_,
        v_pu_boxed_6420_,
        v_inst_6414_,
        v_inst_6415_,
        v_f_6416_,
        v_code_6417_,
        v_toBind_6418_,
        v_params_6419_,
    );
    return v_res_6421_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2(
    mut v_info_6422_: *mut crate::leanh::LeanObject,
    mut v_toPure_6423_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6425_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6425_, 0, v_info_6422_);
    crate::leanh::lean_ctor_set(v___x_6425_, 1, v_____do__lift_6424_);
    v___x_6426_ =
        crate::leanh::lean_apply_2(v_toPure_6423_, crate::leanh::lean_box(0), v___x_6425_);
    return v___x_6426_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3(
    mut v_toPure_6427_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6429_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6429_, 0, v_____do__lift_6428_);
    v___x_6430_ =
        crate::leanh::lean_apply_2(v_toPure_6427_, crate::leanh::lean_box(0), v___x_6429_);
    return v___x_6430_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(
    mut v_pu_6431_: u8,
    mut v_m_6432_: *mut crate::leanh::LeanObject,
    mut v_inst_6433_: *mut crate::leanh::LeanObject,
    mut v_inst_6434_: *mut crate::leanh::LeanObject,
    mut v_f_6435_: *mut crate::leanh::LeanObject,
    mut v_alt_6436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_alt_6436_) {
        0 => {
            let mut v_toApplicative_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ctorName_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_code_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_6447_: usize = 0;
            let mut v___x_6448_: usize = 0;
            let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6437_ = crate::leanh::lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6438_ = crate::leanh::lean_ctor_get(v_inst_6434_, 1);
            crate::leanh::lean_inc_n(v_toBind_6438_, 2);
            v_toPure_6439_ = crate::leanh::lean_ctor_get(v_toApplicative_6437_, 1);
            v_ctorName_6440_ = crate::leanh::lean_ctor_get(v_alt_6436_, 0);
            crate::leanh::lean_inc(v_ctorName_6440_);
            v_params_6441_ = crate::leanh::lean_ctor_get(v_alt_6436_, 1);
            crate::leanh::lean_inc_ref(v_params_6441_);
            v_code_6442_ = crate::leanh::lean_ctor_get(v_alt_6436_, 2);
            crate::leanh::lean_inc_ref(v_code_6442_);
            crate::leanh::lean_dec_ref_known(v_alt_6436_, 3);
            v___x_6443_ = crate::leanh::lean_box((v_pu_6431_) as usize);
            crate::leanh::lean_inc(v_f_6435_);
            crate::leanh::lean_inc_ref_n(v_inst_6434_, 2);
            crate::leanh::lean_inc(v_inst_6433_);
            crate::leanh::lean_inc(v_toPure_6439_);
            v___f_6444_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__1___boxed as *mut core::ffi::c_void,
                9,
                8,
            );
            crate::leanh::lean_closure_set(v___f_6444_, 0, v_ctorName_6440_);
            crate::leanh::lean_closure_set(v___f_6444_, 1, v_toPure_6439_);
            crate::leanh::lean_closure_set(v___f_6444_, 2, v___x_6443_);
            crate::leanh::lean_closure_set(v___f_6444_, 3, v_inst_6433_);
            crate::leanh::lean_closure_set(v___f_6444_, 4, v_inst_6434_);
            crate::leanh::lean_closure_set(v___f_6444_, 5, v_f_6435_);
            crate::leanh::lean_closure_set(v___f_6444_, 6, v_code_6442_);
            crate::leanh::lean_closure_set(v___f_6444_, 7, v_toBind_6438_);
            v___x_6445_ = crate::leanh::lean_box((v_pu_6431_) as usize);
            v___x_6446_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_Param_mapFVarM___boxed as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___x_6446_, 0, crate::leanh::lean_box(0));
            crate::leanh::lean_closure_set(v___x_6446_, 1, v___x_6445_);
            crate::leanh::lean_closure_set(v___x_6446_, 2, v_inst_6433_);
            crate::leanh::lean_closure_set(v___x_6446_, 3, v_inst_6434_);
            crate::leanh::lean_closure_set(v___x_6446_, 4, v_f_6435_);
            v_sz_6447_ = lean_array_size(v_params_6441_);
            v___x_6448_ = 0usize;
            v___x_6449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_6434_,
                v___x_6446_,
                v_sz_6447_,
                v___x_6448_,
                v_params_6441_,
            );
            v___x_6450_ = crate::leanh::lean_apply_4(
                v_toBind_6438_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6449_,
                v___f_6444_,
            );
            return v___x_6450_;
        }
        1 => {
            let mut v_toApplicative_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_info_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_code_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6451_ = crate::leanh::lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6452_ = crate::leanh::lean_ctor_get(v_inst_6434_, 1);
            crate::leanh::lean_inc(v_toBind_6452_);
            v_toPure_6453_ = crate::leanh::lean_ctor_get(v_toApplicative_6451_, 1);
            v_info_6454_ = crate::leanh::lean_ctor_get(v_alt_6436_, 0);
            crate::leanh::lean_inc_ref(v_info_6454_);
            v_code_6455_ = crate::leanh::lean_ctor_get(v_alt_6436_, 1);
            crate::leanh::lean_inc_ref(v_code_6455_);
            crate::leanh::lean_dec_ref_known(v_alt_6436_, 2);
            crate::leanh::lean_inc(v_toPure_6453_);
            v___f_6456_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__2 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_6456_, 0, v_info_6454_);
            crate::leanh::lean_closure_set(v___f_6456_, 1, v_toPure_6453_);
            v___x_6457_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
                v_pu_6431_,
                v_inst_6433_,
                v_inst_6434_,
                v_f_6435_,
                v_code_6455_,
            );
            v___x_6458_ = crate::leanh::lean_apply_4(
                v_toBind_6452_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6457_,
                v___f_6456_,
            );
            return v___x_6458_;
        }
        _ => {
            let mut v_toApplicative_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_code_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_6459_ = crate::leanh::lean_ctor_get(v_inst_6434_, 0);
            v_toBind_6460_ = crate::leanh::lean_ctor_get(v_inst_6434_, 1);
            crate::leanh::lean_inc(v_toBind_6460_);
            v_toPure_6461_ = crate::leanh::lean_ctor_get(v_toApplicative_6459_, 1);
            v_code_6462_ = crate::leanh::lean_ctor_get(v_alt_6436_, 0);
            crate::leanh::lean_inc_ref(v_code_6462_);
            crate::leanh::lean_dec_ref_known(v_alt_6436_, 1);
            crate::leanh::lean_inc(v_toPure_6461_);
            v___f_6463_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__3 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_6463_, 0, v_toPure_6461_);
            v___x_6464_ = l_Lean_Compiler_LCNF_Code_mapFVarM___redArg(
                v_pu_6431_,
                v_inst_6433_,
                v_inst_6434_,
                v_f_6435_,
                v_code_6462_,
            );
            v___x_6465_ = crate::leanh::lean_apply_4(
                v_toBind_6460_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_6464_,
                v___f_6463_,
            );
            return v___x_6465_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed(
    mut v_pu_6466_: *mut crate::leanh::LeanObject,
    mut v_m_6467_: *mut crate::leanh::LeanObject,
    mut v_inst_6468_: *mut crate::leanh::LeanObject,
    mut v_inst_6469_: *mut crate::leanh::LeanObject,
    mut v_f_6470_: *mut crate::leanh::LeanObject,
    mut v_alt_6471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6472_: u8 = 0;
    let mut v_res_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6472_ = (crate::leanh::lean_unbox(v_pu_6466_) as u8);
    v_res_6473_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4(
        v_pu_boxed_6472_,
        v_m_6467_,
        v_inst_6468_,
        v_inst_6469_,
        v_f_6470_,
        v_alt_6471_,
    );
    return v_res_6473_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5(
    mut v_inst_6474_: *mut crate::leanh::LeanObject,
    mut v_f_6475_: *mut crate::leanh::LeanObject,
    mut v_code_6476_: *mut crate::leanh::LeanObject,
    mut v_____r_6477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6478_ =
        l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6474_, v_f_6475_, v_code_6476_);
    return v___x_6478_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__7(
    mut v_m_6479_: *mut crate::leanh::LeanObject,
    mut v_inst_6480_: *mut crate::leanh::LeanObject,
    mut v_f_6481_: *mut crate::leanh::LeanObject,
    mut v_alt_6482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_alt_6482_) {
        0 => {
            let mut v_toApplicative_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_params_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_code_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6491_: u8 = 0;
            v_toApplicative_6483_ = crate::leanh::lean_ctor_get(v_inst_6480_, 0);
            v_toBind_6484_ = crate::leanh::lean_ctor_get(v_inst_6480_, 1);
            crate::leanh::lean_inc(v_toBind_6484_);
            v_params_6485_ = crate::leanh::lean_ctor_get(v_alt_6482_, 1);
            crate::leanh::lean_inc_ref(v_params_6485_);
            v_code_6486_ = crate::leanh::lean_ctor_get(v_alt_6482_, 2);
            crate::leanh::lean_inc_ref(v_code_6486_);
            crate::leanh::lean_dec_ref_known(v_alt_6482_, 3);
            crate::leanh::lean_inc(v_f_6481_);
            crate::leanh::lean_inc_ref(v_inst_6480_);
            v___f_6487_ = crate::leanh::lean_alloc_closure(
                l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__5 as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_6487_, 0, v_inst_6480_);
            crate::leanh::lean_closure_set(v___f_6487_, 1, v_f_6481_);
            crate::leanh::lean_closure_set(v___f_6487_, 2, v_code_6486_);
            v___x_6488_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_6489_ = lean_array_get_size(v_params_6485_);
            v___x_6490_ = crate::leanh::lean_box(0);
            v___x_6491_ = lean_nat_dec_lt(v___x_6488_, v___x_6489_);
            if v___x_6491_ == 0 {
                let mut v_toPure_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc_ref(v_toApplicative_6483_);
                crate::leanh::lean_dec_ref(v_params_6485_);
                crate::leanh::lean_dec(v_f_6481_);
                crate::leanh::lean_dec_ref(v_inst_6480_);
                v_toPure_6492_ = crate::leanh::lean_ctor_get(v_toApplicative_6483_, 1);
                crate::leanh::lean_inc(v_toPure_6492_);
                crate::leanh::lean_dec_ref(v_toApplicative_6483_);
                v___x_6493_ = crate::leanh::lean_apply_2(
                    v_toPure_6492_,
                    crate::leanh::lean_box(0),
                    v___x_6490_,
                );
                v___x_6494_ = crate::leanh::lean_apply_4(
                    v_toBind_6484_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6493_,
                    v___f_6487_,
                );
                return v___x_6494_;
            } else {
                let mut v___f_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6496_: u8 = 0;
                crate::leanh::lean_inc_ref(v_inst_6480_);
                v___f_6495_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_FunDecl_forFVarM___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6495_, 0, v_inst_6480_);
                crate::leanh::lean_closure_set(v___f_6495_, 1, v_f_6481_);
                v___x_6496_ = lean_nat_dec_le(v___x_6489_, v___x_6489_);
                if v___x_6496_ == 0 {
                    if v___x_6491_ == 0 {
                        let mut v_toPure_6497_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_inc_ref(v_toApplicative_6483_);
                        crate::leanh::lean_dec_ref(v___f_6495_);
                        crate::leanh::lean_dec_ref(v_params_6485_);
                        crate::leanh::lean_dec_ref(v_inst_6480_);
                        v_toPure_6497_ = crate::leanh::lean_ctor_get(v_toApplicative_6483_, 1);
                        crate::leanh::lean_inc(v_toPure_6497_);
                        crate::leanh::lean_dec_ref(v_toApplicative_6483_);
                        v___x_6498_ = crate::leanh::lean_apply_2(
                            v_toPure_6497_,
                            crate::leanh::lean_box(0),
                            v___x_6490_,
                        );
                        v___x_6499_ = crate::leanh::lean_apply_4(
                            v_toBind_6484_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_6498_,
                            v___f_6487_,
                        );
                        return v___x_6499_;
                    } else {
                        let mut v___x_6500_: usize = 0;
                        let mut v___x_6501_: usize = 0;
                        let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_6500_ = 0usize;
                        v___x_6501_ = lean_usize_of_nat(v___x_6489_);
                        v___x_6502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_6480_,
                            v___f_6495_,
                            v_params_6485_,
                            v___x_6500_,
                            v___x_6501_,
                            v___x_6490_,
                        );
                        v___x_6503_ = crate::leanh::lean_apply_4(
                            v_toBind_6484_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_6502_,
                            v___f_6487_,
                        );
                        return v___x_6503_;
                    }
                } else {
                    let mut v___x_6504_: usize = 0;
                    let mut v___x_6505_: usize = 0;
                    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_6504_ = 0usize;
                    v___x_6505_ = lean_usize_of_nat(v___x_6489_);
                    v___x_6506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_6480_,
                        v___f_6495_,
                        v_params_6485_,
                        v___x_6504_,
                        v___x_6505_,
                        v___x_6490_,
                    );
                    v___x_6507_ = crate::leanh::lean_apply_4(
                        v_toBind_6484_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_6506_,
                        v___f_6487_,
                    );
                    return v___x_6507_;
                }
            }
        }
        1 => {
            let mut v_code_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_6508_ = crate::leanh::lean_ctor_get(v_alt_6482_, 1);
            crate::leanh::lean_inc_ref(v_code_6508_);
            crate::leanh::lean_dec_ref_known(v_alt_6482_, 2);
            v___x_6509_ =
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6480_, v_f_6481_, v_code_6508_);
            return v___x_6509_;
        }
        _ => {
            let mut v_code_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_6510_ = crate::leanh::lean_ctor_get(v_alt_6482_, 0);
            crate::leanh::lean_inc_ref(v_code_6510_);
            crate::leanh::lean_dec_ref_known(v_alt_6482_, 1);
            v___x_6511_ =
                l_Lean_Compiler_LCNF_Code_forFVarM___redArg(v_inst_6480_, v_f_6481_, v_code_6510_);
            return v___x_6511_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt(
    mut v_pu_6513_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6514_ = crate::leanh::lean_box((v_pu_6513_) as usize);
    v___f_6515_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instTraverseFVarAlt___lam__4___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6515_, 0, v___x_6514_);
    v___f_6516_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt___closed__0;
    v___x_6517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6517_, 0, v___f_6515_);
    crate::leanh::lean_ctor_set(v___x_6517_, 1, v___f_6516_);
    return v___x_6517_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instTraverseFVarAlt___boxed(
    mut v_pu_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6519_: u8 = 0;
    let mut v_res_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6519_ = (crate::leanh::lean_unbox(v_pu_6518_) as u8);
    v_res_6520_ = l_Lean_Compiler_LCNF_instTraverseFVarAlt(v_pu_boxed_6519_);
    return v_res_6520_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(
    mut v_toPure_6523_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_6524_) == 0 {
        let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6525_ = crate::leanh::lean_box(0);
        v___x_6526_ =
            crate::leanh::lean_apply_2(v_toPure_6523_, crate::leanh::lean_box(0), v___x_6525_);
        return v___x_6526_;
    } else {
        let mut v_val_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6528_: u8 = 0;
        v_val_6527_ = crate::leanh::lean_ctor_get(v_____do__lift_6524_, 0);
        v___x_6528_ = (crate::leanh::lean_unbox(v_val_6527_) as u8);
        if v___x_6528_ == 0 {
            let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6529_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0;
            v___x_6530_ =
                crate::leanh::lean_apply_2(v_toPure_6523_, crate::leanh::lean_box(0), v___x_6529_);
            return v___x_6530_;
        } else {
            let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6531_ = crate::leanh::lean_box(0);
            v___x_6532_ =
                crate::leanh::lean_apply_2(v_toPure_6523_, crate::leanh::lean_box(0), v___x_6531_);
            return v___x_6532_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed(
    mut v_toPure_6533_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6535_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0(
            v_toPure_6533_,
            v_____do__lift_6534_,
        );
    crate::leanh::lean_dec(v_____do__lift_6534_);
    return v_res_6535_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(
    mut v_toPure_6536_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6537_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6538_ = crate::leanh::lean_box((v_____do__lift_6537_) as usize);
    v___x_6539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6539_, 0, v___x_6538_);
    v___x_6540_ =
        crate::leanh::lean_apply_2(v_toPure_6536_, crate::leanh::lean_box(0), v___x_6539_);
    return v___x_6540_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed(
    mut v_toPure_6541_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_405__boxed_6543_: u8 = 0;
    let mut v_res_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_405__boxed_6543_ = (crate::leanh::lean_unbox(v_____do__lift_6542_) as u8);
    v_res_6544_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1(
            v_toPure_6541_,
            v_____do__lift_405__boxed_6543_,
        );
    return v_res_6544_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(
    mut v_inst_6545_: *mut crate::leanh::LeanObject,
    mut v_f_6546_: *mut crate::leanh::LeanObject,
    mut v_fvar_6547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6548_ = crate::leanh::lean_ctor_get(v_inst_6545_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6548_);
    v_toBind_6549_ = crate::leanh::lean_ctor_get(v_inst_6545_, 1);
    crate::leanh::lean_inc_n(v_toBind_6549_, 2);
    crate::leanh::lean_dec_ref(v_inst_6545_);
    v_toPure_6550_ = crate::leanh::lean_ctor_get(v_toApplicative_6548_, 1);
    crate::leanh::lean_inc_n(v_toPure_6550_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_6548_);
    v___x_6551_ = crate::leanh::lean_apply_1(v_f_6546_, v_fvar_6547_);
    v___f_6552_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_6552_, 0, v_toPure_6550_);
    v___f_6553_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_6553_, 0, v_toPure_6550_);
    v___x_6554_ = crate::leanh::lean_apply_4(
        v_toBind_6549_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6551_,
        v___f_6553_,
    );
    v___x_6555_ = crate::leanh::lean_apply_4(
        v_toBind_6549_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6554_,
        v___f_6552_,
    );
    return v___x_6555_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go(
    mut v_m_6556_: *mut crate::leanh::LeanObject,
    mut v_inst_6557_: *mut crate::leanh::LeanObject,
    mut v_f_6558_: *mut crate::leanh::LeanObject,
    mut v_fvar_6559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6560_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg(
            v_inst_6557_,
            v_f_6558_,
            v_fvar_6559_,
        );
    return v___x_6560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(
    mut v_toPure_6561_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_6562_) == 0 {
        let mut v___x_6563_: u8 = 0;
        let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6563_ = 1;
        v___x_6564_ = crate::leanh::lean_box((v___x_6563_) as usize);
        v___x_6565_ =
            crate::leanh::lean_apply_2(v_toPure_6561_, crate::leanh::lean_box(0), v___x_6564_);
        return v___x_6565_;
    } else {
        let mut v___x_6566_: u8 = 0;
        let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6566_ = 0;
        v___x_6567_ = crate::leanh::lean_box((v___x_6566_) as usize);
        v___x_6568_ =
            crate::leanh::lean_apply_2(v_toPure_6561_, crate::leanh::lean_box(0), v___x_6567_);
        return v___x_6568_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed(
    mut v_toPure_6569_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6571_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0(v_toPure_6569_, v_____do__lift_6570_);
    crate::leanh::lean_dec(v_____do__lift_6570_);
    return v_res_6571_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM___redArg(
    mut v_inst_6572_: *mut crate::leanh::LeanObject,
    mut v_inst_6573_: *mut crate::leanh::LeanObject,
    mut v_f_6574_: *mut crate::leanh::LeanObject,
    mut v_x_6575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forFVarM_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6581_: u8 = 0;
    let mut v___f_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_unused_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6576_ = crate::leanh::lean_ctor_get(v_inst_6572_, 0);
                v_toBind_6577_ = crate::leanh::lean_ctor_get(v_inst_6572_, 1);
                crate::leanh::lean_inc(v_toBind_6577_);
                v_forFVarM_6578_ = crate::leanh::lean_ctor_get(v_inst_6573_, 1);
                v_isSharedCheck_6599_ = (!crate::leanh::lean_is_exclusive(v_inst_6573_)) as u8;
                if v_isSharedCheck_6599_ == 0 {
                    v_unused_6600_ = crate::leanh::lean_ctor_get(v_inst_6573_, 0);
                    crate::leanh::lean_dec(v_unused_6600_);
                    v___x_6580_ = v_inst_6573_;
                    v_isShared_6581_ = v_isSharedCheck_6599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_forFVarM_6578_);
                    crate::leanh::lean_dec(v_inst_6573_);
                    v___x_6580_ = crate::leanh::lean_box(0);
                    v_isShared_6581_ = v_isSharedCheck_6599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v_inst_6572_, 5);
                v___f_6582_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6582_, 0, v_inst_6572_);
                v___f_6583_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6583_, 0, v_inst_6572_);
                v___f_6584_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6584_, 0, v_inst_6572_);
                v___f_6585_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6585_, 0, v_inst_6572_);
                v___f_6586_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6586_, 0, v_inst_6572_);
                if v_isShared_6581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6580_, 1, v___f_6583_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 0, v___f_6582_);
                    v___x_6588_ = v___x_6580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___f_6582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 1, v___f_6583_);
                    v___x_6588_ = v_reuseFailAlloc_6598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v_inst_6572_, 2);
                v___x_6589_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_pure as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_6589_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6589_, 1, v_inst_6572_);
                v___x_6590_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6590_, 0, v___x_6588_);
                crate::leanh::lean_ctor_set(v___x_6590_, 1, v___x_6589_);
                crate::leanh::lean_ctor_set(v___x_6590_, 2, v___f_6584_);
                crate::leanh::lean_ctor_set(v___x_6590_, 3, v___f_6585_);
                crate::leanh::lean_ctor_set(v___x_6590_, 4, v___f_6586_);
                v___x_6591_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_bind as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_6591_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6591_, 1, v_inst_6572_);
                v___x_6592_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6592_, 0, v___x_6590_);
                crate::leanh::lean_ctor_set(v___x_6592_, 1, v___x_6591_);
                v_toPure_6593_ = crate::leanh::lean_ctor_get(v_toApplicative_6576_, 1);
                crate::leanh::lean_inc(v_toPure_6593_);
                v___x_6594_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_6594_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6594_, 1, v_inst_6572_);
                crate::leanh::lean_closure_set(v___x_6594_, 2, v_f_6574_);
                v___x_6595_ = crate::leanh::lean_apply_4(
                    v_forFVarM_6578_,
                    crate::leanh::lean_box(0),
                    v___x_6592_,
                    v___x_6594_,
                    v_x_6575_,
                );
                v___f_6596_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_anyFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6596_, 0, v_toPure_6593_);
                v___x_6597_ = crate::leanh::lean_apply_4(
                    v_toBind_6577_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6595_,
                    v___f_6596_,
                );
                return v___x_6597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVarM(
    mut v_m_6601_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6602_: *mut crate::leanh::LeanObject,
    mut v_inst_6603_: *mut crate::leanh::LeanObject,
    mut v_inst_6604_: *mut crate::leanh::LeanObject,
    mut v_f_6605_: *mut crate::leanh::LeanObject,
    mut v_x_6606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6607_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg(v_inst_6603_, v_inst_6604_, v_f_6605_, v_x_6606_);
    return v___x_6607_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(
    mut v_toPure_6608_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_6609_) == 0 {
        let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6610_ = crate::leanh::lean_box(0);
        v___x_6611_ =
            crate::leanh::lean_apply_2(v_toPure_6608_, crate::leanh::lean_box(0), v___x_6610_);
        return v___x_6611_;
    } else {
        let mut v_val_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6613_: u8 = 0;
        v_val_6612_ = crate::leanh::lean_ctor_get(v_____do__lift_6609_, 0);
        v___x_6613_ = (crate::leanh::lean_unbox(v_val_6612_) as u8);
        if v___x_6613_ == 0 {
            let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6614_ = crate::leanh::lean_box(0);
            v___x_6615_ =
                crate::leanh::lean_apply_2(v_toPure_6608_, crate::leanh::lean_box(0), v___x_6614_);
            return v___x_6615_;
        } else {
            let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6616_ = l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__0___closed__0;
            v___x_6617_ =
                crate::leanh::lean_apply_2(v_toPure_6608_, crate::leanh::lean_box(0), v___x_6616_);
            return v___x_6617_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed(
    mut v_toPure_6618_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6620_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0(
            v_toPure_6618_,
            v_____do__lift_6619_,
        );
    crate::leanh::lean_dec(v_____do__lift_6619_);
    return v_res_6620_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(
    mut v_inst_6621_: *mut crate::leanh::LeanObject,
    mut v_f_6622_: *mut crate::leanh::LeanObject,
    mut v_fvar_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6624_ = crate::leanh::lean_ctor_get(v_inst_6621_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6624_);
    v_toBind_6625_ = crate::leanh::lean_ctor_get(v_inst_6621_, 1);
    crate::leanh::lean_inc_n(v_toBind_6625_, 2);
    crate::leanh::lean_dec_ref(v_inst_6621_);
    v_toPure_6626_ = crate::leanh::lean_ctor_get(v_toApplicative_6624_, 1);
    crate::leanh::lean_inc_n(v_toPure_6626_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_6624_);
    v___x_6627_ = crate::leanh::lean_apply_1(v_f_6622_, v_fvar_6623_);
    v___f_6628_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_6628_, 0, v_toPure_6626_);
    v___f_6629_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_anyFVarM_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_6629_, 0, v_toPure_6626_);
    v___x_6630_ = crate::leanh::lean_apply_4(
        v_toBind_6625_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6627_,
        v___f_6629_,
    );
    v___x_6631_ = crate::leanh::lean_apply_4(
        v_toBind_6625_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6630_,
        v___f_6628_,
    );
    return v___x_6631_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go(
    mut v_m_6632_: *mut crate::leanh::LeanObject,
    mut v_inst_6633_: *mut crate::leanh::LeanObject,
    mut v_f_6634_: *mut crate::leanh::LeanObject,
    mut v_fvar_6635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6636_ =
        l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go___redArg(
            v_inst_6633_,
            v_f_6634_,
            v_fvar_6635_,
        );
    return v___x_6636_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(
    mut v_toPure_6637_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_6638_) == 1 {
        let mut v___x_6639_: u8 = 0;
        let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6639_ = 1;
        v___x_6640_ = crate::leanh::lean_box((v___x_6639_) as usize);
        v___x_6641_ =
            crate::leanh::lean_apply_2(v_toPure_6637_, crate::leanh::lean_box(0), v___x_6640_);
        return v___x_6641_;
    } else {
        let mut v___x_6642_: u8 = 0;
        let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6642_ = 0;
        v___x_6643_ = crate::leanh::lean_box((v___x_6642_) as usize);
        v___x_6644_ =
            crate::leanh::lean_apply_2(v_toPure_6637_, crate::leanh::lean_box(0), v___x_6643_);
        return v___x_6644_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed(
    mut v_toPure_6645_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6647_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0(v_toPure_6645_, v_____do__lift_6646_);
    crate::leanh::lean_dec(v_____do__lift_6646_);
    return v_res_6647_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM___redArg(
    mut v_inst_6648_: *mut crate::leanh::LeanObject,
    mut v_inst_6649_: *mut crate::leanh::LeanObject,
    mut v_f_6650_: *mut crate::leanh::LeanObject,
    mut v_x_6651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forFVarM_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6657_: u8 = 0;
    let mut v___f_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6675_: u8 = 0;
    let mut v_unused_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_6652_ = crate::leanh::lean_ctor_get(v_inst_6648_, 0);
                v_toBind_6653_ = crate::leanh::lean_ctor_get(v_inst_6648_, 1);
                crate::leanh::lean_inc(v_toBind_6653_);
                v_forFVarM_6654_ = crate::leanh::lean_ctor_get(v_inst_6649_, 1);
                v_isSharedCheck_6675_ = (!crate::leanh::lean_is_exclusive(v_inst_6649_)) as u8;
                if v_isSharedCheck_6675_ == 0 {
                    v_unused_6676_ = crate::leanh::lean_ctor_get(v_inst_6649_, 0);
                    crate::leanh::lean_dec(v_unused_6676_);
                    v___x_6656_ = v_inst_6649_;
                    v_isShared_6657_ = v_isSharedCheck_6675_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_forFVarM_6654_);
                    crate::leanh::lean_dec(v_inst_6649_);
                    v___x_6656_ = crate::leanh::lean_box(0);
                    v_isShared_6657_ = v_isSharedCheck_6675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v_inst_6648_, 5);
                v___f_6658_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6658_, 0, v_inst_6648_);
                v___f_6659_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6659_, 0, v_inst_6648_);
                v___f_6660_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6660_, 0, v_inst_6648_);
                v___f_6661_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6661_, 0, v_inst_6648_);
                v___f_6662_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6662_, 0, v_inst_6648_);
                if v_isShared_6657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6656_, 1, v___f_6659_);
                    crate::leanh::lean_ctor_set(v___x_6656_, 0, v___f_6658_);
                    v___x_6664_ = v___x_6656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6674_, 0, v___f_6658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6674_, 1, v___f_6659_);
                    v___x_6664_ = v_reuseFailAlloc_6674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v_inst_6648_, 2);
                v___x_6665_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_pure as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_6665_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6665_, 1, v_inst_6648_);
                v___x_6666_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6666_, 0, v___x_6664_);
                crate::leanh::lean_ctor_set(v___x_6666_, 1, v___x_6665_);
                crate::leanh::lean_ctor_set(v___x_6666_, 2, v___f_6660_);
                crate::leanh::lean_ctor_set(v___x_6666_, 3, v___f_6661_);
                crate::leanh::lean_ctor_set(v___x_6666_, 4, v___f_6662_);
                v___x_6667_ = crate::leanh::lean_alloc_closure(
                    l_OptionT_bind as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_6667_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6667_, 1, v_inst_6648_);
                v___x_6668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6668_, 0, v___x_6666_);
                crate::leanh::lean_ctor_set(v___x_6668_, 1, v___x_6667_);
                v_toPure_6669_ = crate::leanh::lean_ctor_get(v_toApplicative_6652_, 1);
                crate::leanh::lean_inc(v_toPure_6669_);
                v___x_6670_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Compiler_LCNF_FVarUtil_0__Lean_Compiler_LCNF_allFVarM_go
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_6670_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6670_, 1, v_inst_6648_);
                crate::leanh::lean_closure_set(v___x_6670_, 2, v_f_6650_);
                v___x_6671_ = crate::leanh::lean_apply_4(
                    v_forFVarM_6654_,
                    crate::leanh::lean_box(0),
                    v___x_6668_,
                    v___x_6670_,
                    v_x_6651_,
                );
                v___f_6672_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_allFVarM___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6672_, 0, v_toPure_6669_);
                v___x_6673_ = crate::leanh::lean_apply_4(
                    v_toBind_6653_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_6671_,
                    v___f_6672_,
                );
                return v___x_6673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVarM(
    mut v_m_6677_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6678_: *mut crate::leanh::LeanObject,
    mut v_inst_6679_: *mut crate::leanh::LeanObject,
    mut v_inst_6680_: *mut crate::leanh::LeanObject,
    mut v_f_6681_: *mut crate::leanh::LeanObject,
    mut v_x_6682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6683_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg(v_inst_6679_, v_inst_6680_, v_f_6681_, v_x_6682_);
    return v___x_6683_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(
    mut v_f_6684_: *mut crate::leanh::LeanObject,
    mut v_x_6685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: u8 = 0;
    v___x_6686_ = crate::leanh::lean_apply_1(v_f_6684_, v_x_6685_);
    v___x_6687_ = (crate::leanh::lean_unbox(v___x_6686_) as u8);
    return v___x_6687_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed(
    mut v_f_6688_: *mut crate::leanh::LeanObject,
    mut v_x_6689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6690_: u8 = 0;
    let mut v_r_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6690_ = l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0(v_f_6688_, v_x_6689_);
    v_r_6691_ = crate::leanh::lean_box((v_res_6690_) as usize);
    return v_r_6691_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg(
    mut v_inst_6711_: *mut crate::leanh::LeanObject,
    mut v_f_6712_: *mut crate::leanh::LeanObject,
    mut v_x_6713_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: u8 = 0;
    v___f_6714_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6714_, 0, v_f_6712_);
    v___x_6715_ = l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9;
    v___x_6716_ =
        l_Lean_Compiler_LCNF_anyFVarM___redArg(v___x_6715_, v_inst_6711_, v___f_6714_, v_x_6713_);
    v___x_6717_ = (crate::leanh::lean_unbox(v___x_6716_) as u8);
    crate::leanh::lean_dec(v___x_6716_);
    return v___x_6717_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___redArg___boxed(
    mut v_inst_6718_: *mut crate::leanh::LeanObject,
    mut v_f_6719_: *mut crate::leanh::LeanObject,
    mut v_x_6720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6721_: u8 = 0;
    let mut v_r_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6721_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_6718_, v_f_6719_, v_x_6720_);
    v_r_6722_ = crate::leanh::lean_box((v_res_6721_) as usize);
    return v_r_6722_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar(
    mut v_00_u03b1_6723_: *mut crate::leanh::LeanObject,
    mut v_inst_6724_: *mut crate::leanh::LeanObject,
    mut v_f_6725_: *mut crate::leanh::LeanObject,
    mut v_x_6726_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6727_: u8 = 0;
    v___x_6727_ = l_Lean_Compiler_LCNF_anyFVar___redArg(v_inst_6724_, v_f_6725_, v_x_6726_);
    return v___x_6727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_anyFVar___boxed(
    mut v_00_u03b1_6728_: *mut crate::leanh::LeanObject,
    mut v_inst_6729_: *mut crate::leanh::LeanObject,
    mut v_f_6730_: *mut crate::leanh::LeanObject,
    mut v_x_6731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6732_: u8 = 0;
    let mut v_r_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6732_ =
        l_Lean_Compiler_LCNF_anyFVar(v_00_u03b1_6728_, v_inst_6729_, v_f_6730_, v_x_6731_);
    v_r_6733_ = crate::leanh::lean_box((v_res_6732_) as usize);
    return v_r_6733_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___redArg(
    mut v_inst_6734_: *mut crate::leanh::LeanObject,
    mut v_f_6735_: *mut crate::leanh::LeanObject,
    mut v_x_6736_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: u8 = 0;
    v___f_6737_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_anyFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6737_, 0, v_f_6735_);
    v___x_6738_ = l_Lean_Compiler_LCNF_anyFVar___redArg___closed__9;
    v___x_6739_ =
        l_Lean_Compiler_LCNF_allFVarM___redArg(v___x_6738_, v_inst_6734_, v___f_6737_, v_x_6736_);
    v___x_6740_ = (crate::leanh::lean_unbox(v___x_6739_) as u8);
    crate::leanh::lean_dec(v___x_6739_);
    return v___x_6740_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___redArg___boxed(
    mut v_inst_6741_: *mut crate::leanh::LeanObject,
    mut v_f_6742_: *mut crate::leanh::LeanObject,
    mut v_x_6743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6744_: u8 = 0;
    let mut v_r_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6744_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_6741_, v_f_6742_, v_x_6743_);
    v_r_6745_ = crate::leanh::lean_box((v_res_6744_) as usize);
    return v_r_6745_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar(
    mut v_00_u03b1_6746_: *mut crate::leanh::LeanObject,
    mut v_inst_6747_: *mut crate::leanh::LeanObject,
    mut v_f_6748_: *mut crate::leanh::LeanObject,
    mut v_x_6749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6750_: u8 = 0;
    v___x_6750_ = l_Lean_Compiler_LCNF_allFVar___redArg(v_inst_6747_, v_f_6748_, v_x_6749_);
    return v___x_6750_;
}
pub unsafe fn l_Lean_Compiler_LCNF_allFVar___boxed(
    mut v_00_u03b1_6751_: *mut crate::leanh::LeanObject,
    mut v_inst_6752_: *mut crate::leanh::LeanObject,
    mut v_f_6753_: *mut crate::leanh::LeanObject,
    mut v_x_6754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6755_: u8 = 0;
    let mut v_r_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6755_ =
        l_Lean_Compiler_LCNF_allFVar(v_00_u03b1_6751_, v_inst_6752_, v_f_6753_, v_x_6754_);
    v_r_6756_ = crate::leanh::lean_box((v_res_6755_) as usize);
    return v_r_6756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_FVarUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_FVarUtil(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_FVarUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
}
