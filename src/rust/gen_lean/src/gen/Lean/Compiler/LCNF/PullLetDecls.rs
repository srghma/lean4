// Lean compiler output
// Module: Lean.Compiler.LCNF.PullLetDecls
// Imports: Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.PassManager
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
    l_Array_shrink___redArg,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_instBEqArg_beq___redArg,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg;
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn,
    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn,
    runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_isClass_x3f___redArg;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::l_Lean_FVarIdSet_insert;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::ffi::lean_array_uget_borrowed;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10_value:
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
    m_fun: l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 68,
    m_capacity: 68,
    m_length: 67,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105,
        108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110,
        46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100, 97, 116,
        101, 70, 117, 110, 73, 109, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66,
        97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4342836574150310743 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullInstances___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        112, 117, 108, 108, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_pullInstances___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullInstances___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullInstances___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullInstances___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12388592875912446130 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_pullInstances___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullInstances___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_pullInstances___closed__2_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Decl_pullInstances___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_pullInstances___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullInstances___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_pullInstances___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_pullInstances___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_pullInstances: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_pullInstances___closed__0_value) as *mut crate::leanh::LeanObject,11575986503636928924 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 117, 108, 108, 76, 101, 116, 68, 101, 99, 108, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13394107196730503451 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,18052988147846580390 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16565867362502245167 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12908213613269392929 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14134937670769296004 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6078266128321250721 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8966121554685347180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,344597347119140973 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1470608546689291531 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4941529199342864566 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17711288755060849944 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(
    mut v_fvarId_1242_: *mut crate::leanh::LeanObject,
    mut v_x_1243_: *mut crate::leanh::LeanObject,
    mut v_a_1244_: *mut crate::leanh::LeanObject,
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isCandidateFn_1251_ = crate::leanh::lean_ctor_get(v_a_1244_, 0);
    v_included_1252_ = crate::leanh::lean_ctor_get(v_a_1244_, 1);
    crate::leanh::lean_inc(v_included_1252_);
    v___x_1253_ = l_Lean_FVarIdSet_insert(v_included_1252_, v_fvarId_1242_);
    crate::leanh::lean_inc_ref(v_isCandidateFn_1251_);
    v___x_1254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1254_, 0, v_isCandidateFn_1251_);
    crate::leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
    crate::leanh::lean_inc(v_a_1249_);
    crate::leanh::lean_inc_ref(v_a_1248_);
    crate::leanh::lean_inc(v_a_1247_);
    crate::leanh::lean_inc_ref(v_a_1246_);
    crate::leanh::lean_inc(v_a_1245_);
    v___x_1255_ = crate::leanh::lean_apply_7(
        v_x_1243_,
        v___x_1254_,
        v_a_1245_,
        v_a_1246_,
        v_a_1247_,
        v_a_1248_,
        v_a_1249_,
        crate::leanh::lean_box(0),
    );
    return v___x_1255_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg___boxed(
    mut v_fvarId_1256_: *mut crate::leanh::LeanObject,
    mut v_x_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar___redArg(
        v_fvarId_1256_,
        v_x_1257_,
        v_a_1258_,
        v_a_1259_,
        v_a_1260_,
        v_a_1261_,
        v_a_1262_,
        v_a_1263_,
    );
    crate::leanh::lean_dec(v_a_1263_);
    crate::leanh::lean_dec_ref(v_a_1262_);
    crate::leanh::lean_dec(v_a_1261_);
    crate::leanh::lean_dec_ref(v_a_1260_);
    crate::leanh::lean_dec(v_a_1259_);
    crate::leanh::lean_dec_ref(v_a_1258_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withFVar(
    mut v_00_u03b1_1266_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1267_: *mut crate::leanh::LeanObject,
    mut v_x_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isCandidateFn_1276_ = crate::leanh::lean_ctor_get(v_a_1269_, 0);
    v_included_1277_ = crate::leanh::lean_ctor_get(v_a_1269_, 1);
    crate::leanh::lean_inc(v_included_1277_);
    v___x_1278_ = l_Lean_FVarIdSet_insert(v_included_1277_, v_fvarId_1267_);
    crate::leanh::lean_inc_ref(v_isCandidateFn_1276_);
    v___x_1279_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1279_, 0, v_isCandidateFn_1276_);
    crate::leanh::lean_ctor_set(v___x_1279_, 1, v___x_1278_);
    crate::leanh::lean_inc(v_a_1274_);
    crate::leanh::lean_inc_ref(v_a_1273_);
    crate::leanh::lean_inc(v_a_1272_);
    crate::leanh::lean_inc_ref(v_a_1271_);
    crate::leanh::lean_inc(v_a_1270_);
    v___x_1280_ = crate::leanh::lean_apply_7(
        v_x_1268_,
        v___x_1279_,
        v_a_1270_,
        v_a_1271_,
        v_a_1272_,
        v_a_1273_,
        v_a_1274_,
        crate::leanh::lean_box(0),
    );
    return v___x_1280_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withFVar___boxed(
    mut v_00_u03b1_1281_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1282_: *mut crate::leanh::LeanObject,
    mut v_x_1283_: *mut crate::leanh::LeanObject,
    mut v_a_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_Compiler_LCNF_PullLetDecls_withFVar(
        v_00_u03b1_1281_,
        v_fvarId_1282_,
        v_x_1283_,
        v_a_1284_,
        v_a_1285_,
        v_a_1286_,
        v_a_1287_,
        v_a_1288_,
        v_a_1289_,
    );
    crate::leanh::lean_dec(v_a_1289_);
    crate::leanh::lean_dec_ref(v_a_1288_);
    crate::leanh::lean_dec(v_a_1287_);
    crate::leanh::lean_dec_ref(v_a_1286_);
    crate::leanh::lean_dec(v_a_1285_);
    crate::leanh::lean_dec_ref(v_a_1284_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___lam__0(
    mut v_x1_1292_: *mut crate::leanh::LeanObject,
    mut v_x2_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_1294_ = crate::leanh::lean_ctor_get(v_x2_1293_, 0);
    crate::leanh::lean_inc(v_fvarId_1294_);
    crate::leanh::lean_dec_ref(v_x2_1293_);
    v___x_1295_ = l_Lean_FVarIdSet_insert(v_x1_1292_, v_fvarId_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(
    mut v_ps_1316_: *mut crate::leanh::LeanObject,
    mut v_x_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    v_isCandidateFn_1325_ = crate::leanh::lean_ctor_get(v_a_1318_, 0);
    v_included_1326_ = crate::leanh::lean_ctor_get(v_a_1318_, 1);
    v___x_1327_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1328_ = lean_array_get_size(v_ps_1316_);
    v___x_1329_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9;
    v___x_1330_ = lean_nat_dec_lt(v___x_1327_, v___x_1328_);
    if v___x_1330_ == 0 {
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_ps_1316_);
        crate::leanh::lean_inc(v_a_1323_);
        crate::leanh::lean_inc_ref(v_a_1322_);
        crate::leanh::lean_inc(v_a_1321_);
        crate::leanh::lean_inc_ref(v_a_1320_);
        crate::leanh::lean_inc(v_a_1319_);
        crate::leanh::lean_inc_ref(v_a_1318_);
        v___x_1331_ = crate::leanh::lean_apply_7(
            v_x_1317_,
            v_a_1318_,
            v_a_1319_,
            v_a_1320_,
            v_a_1321_,
            v_a_1322_,
            v_a_1323_,
            crate::leanh::lean_box(0),
        );
        return v___x_1331_;
    } else {
        let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: u8 = 0;
        v___f_1332_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10;
        v___x_1333_ = lean_nat_dec_le(v___x_1328_, v___x_1328_);
        if v___x_1333_ == 0 {
            if v___x_1330_ == 0 {
                let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_ps_1316_);
                crate::leanh::lean_inc(v_a_1323_);
                crate::leanh::lean_inc_ref(v_a_1322_);
                crate::leanh::lean_inc(v_a_1321_);
                crate::leanh::lean_inc_ref(v_a_1320_);
                crate::leanh::lean_inc(v_a_1319_);
                crate::leanh::lean_inc_ref(v_a_1318_);
                v___x_1334_ = crate::leanh::lean_apply_7(
                    v_x_1317_,
                    v_a_1318_,
                    v_a_1319_,
                    v_a_1320_,
                    v_a_1321_,
                    v_a_1322_,
                    v_a_1323_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1334_;
            } else {
                let mut v___x_1335_: usize = 0;
                let mut v___x_1336_: usize = 0;
                let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1335_ = 0usize;
                v___x_1336_ = lean_usize_of_nat(v___x_1328_);
                crate::leanh::lean_inc(v_included_1326_);
                v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1329_,
                    v___f_1332_,
                    v_ps_1316_,
                    v___x_1335_,
                    v___x_1336_,
                    v_included_1326_,
                );
                crate::leanh::lean_inc_ref(v_isCandidateFn_1325_);
                v___x_1338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1338_, 0, v_isCandidateFn_1325_);
                crate::leanh::lean_ctor_set(v___x_1338_, 1, v___x_1337_);
                crate::leanh::lean_inc(v_a_1323_);
                crate::leanh::lean_inc_ref(v_a_1322_);
                crate::leanh::lean_inc(v_a_1321_);
                crate::leanh::lean_inc_ref(v_a_1320_);
                crate::leanh::lean_inc(v_a_1319_);
                v___x_1339_ = crate::leanh::lean_apply_7(
                    v_x_1317_,
                    v___x_1338_,
                    v_a_1319_,
                    v_a_1320_,
                    v_a_1321_,
                    v_a_1322_,
                    v_a_1323_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1339_;
            }
        } else {
            let mut v___x_1340_: usize = 0;
            let mut v___x_1341_: usize = 0;
            let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1340_ = 0usize;
            v___x_1341_ = lean_usize_of_nat(v___x_1328_);
            crate::leanh::lean_inc(v_included_1326_);
            v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1329_,
                v___f_1332_,
                v_ps_1316_,
                v___x_1340_,
                v___x_1341_,
                v_included_1326_,
            );
            crate::leanh::lean_inc_ref(v_isCandidateFn_1325_);
            v___x_1343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1343_, 0, v_isCandidateFn_1325_);
            crate::leanh::lean_ctor_set(v___x_1343_, 1, v___x_1342_);
            crate::leanh::lean_inc(v_a_1323_);
            crate::leanh::lean_inc_ref(v_a_1322_);
            crate::leanh::lean_inc(v_a_1321_);
            crate::leanh::lean_inc_ref(v_a_1320_);
            crate::leanh::lean_inc(v_a_1319_);
            v___x_1344_ = crate::leanh::lean_apply_7(
                v_x_1317_,
                v___x_1343_,
                v_a_1319_,
                v_a_1320_,
                v_a_1321_,
                v_a_1322_,
                v_a_1323_,
                crate::leanh::lean_box(0),
            );
            return v___x_1344_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___boxed(
    mut v_ps_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_a_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
    mut v_a_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg(
        v_ps_1345_, v_x_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_,
    );
    crate::leanh::lean_dec(v_a_1352_);
    crate::leanh::lean_dec_ref(v_a_1351_);
    crate::leanh::lean_dec(v_a_1350_);
    crate::leanh::lean_dec_ref(v_a_1349_);
    crate::leanh::lean_dec(v_a_1348_);
    crate::leanh::lean_dec_ref(v_a_1347_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withParams(
    mut v_00_u03b1_1355_: *mut crate::leanh::LeanObject,
    mut v_ps_1356_: *mut crate::leanh::LeanObject,
    mut v_x_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: u8 = 0;
    v_isCandidateFn_1365_ = crate::leanh::lean_ctor_get(v_a_1358_, 0);
    v_included_1366_ = crate::leanh::lean_ctor_get(v_a_1358_, 1);
    v___x_1367_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1368_ = lean_array_get_size(v_ps_1356_);
    v___x_1369_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__9;
    v___x_1370_ = lean_nat_dec_lt(v___x_1367_, v___x_1368_);
    if v___x_1370_ == 0 {
        let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_ps_1356_);
        crate::leanh::lean_inc(v_a_1363_);
        crate::leanh::lean_inc_ref(v_a_1362_);
        crate::leanh::lean_inc(v_a_1361_);
        crate::leanh::lean_inc_ref(v_a_1360_);
        crate::leanh::lean_inc(v_a_1359_);
        crate::leanh::lean_inc_ref(v_a_1358_);
        v___x_1371_ = crate::leanh::lean_apply_7(
            v_x_1357_,
            v_a_1358_,
            v_a_1359_,
            v_a_1360_,
            v_a_1361_,
            v_a_1362_,
            v_a_1363_,
            crate::leanh::lean_box(0),
        );
        return v___x_1371_;
    } else {
        let mut v___f_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: u8 = 0;
        v___f_1372_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams___redArg___closed__10;
        v___x_1373_ = lean_nat_dec_le(v___x_1368_, v___x_1368_);
        if v___x_1373_ == 0 {
            if v___x_1370_ == 0 {
                let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_ps_1356_);
                crate::leanh::lean_inc(v_a_1363_);
                crate::leanh::lean_inc_ref(v_a_1362_);
                crate::leanh::lean_inc(v_a_1361_);
                crate::leanh::lean_inc_ref(v_a_1360_);
                crate::leanh::lean_inc(v_a_1359_);
                crate::leanh::lean_inc_ref(v_a_1358_);
                v___x_1374_ = crate::leanh::lean_apply_7(
                    v_x_1357_,
                    v_a_1358_,
                    v_a_1359_,
                    v_a_1360_,
                    v_a_1361_,
                    v_a_1362_,
                    v_a_1363_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1374_;
            } else {
                let mut v___x_1375_: usize = 0;
                let mut v___x_1376_: usize = 0;
                let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1375_ = 0usize;
                v___x_1376_ = lean_usize_of_nat(v___x_1368_);
                crate::leanh::lean_inc(v_included_1366_);
                v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1369_,
                    v___f_1372_,
                    v_ps_1356_,
                    v___x_1375_,
                    v___x_1376_,
                    v_included_1366_,
                );
                crate::leanh::lean_inc_ref(v_isCandidateFn_1365_);
                v___x_1378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1378_, 0, v_isCandidateFn_1365_);
                crate::leanh::lean_ctor_set(v___x_1378_, 1, v___x_1377_);
                crate::leanh::lean_inc(v_a_1363_);
                crate::leanh::lean_inc_ref(v_a_1362_);
                crate::leanh::lean_inc(v_a_1361_);
                crate::leanh::lean_inc_ref(v_a_1360_);
                crate::leanh::lean_inc(v_a_1359_);
                v___x_1379_ = crate::leanh::lean_apply_7(
                    v_x_1357_,
                    v___x_1378_,
                    v_a_1359_,
                    v_a_1360_,
                    v_a_1361_,
                    v_a_1362_,
                    v_a_1363_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1379_;
            }
        } else {
            let mut v___x_1380_: usize = 0;
            let mut v___x_1381_: usize = 0;
            let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1380_ = 0usize;
            v___x_1381_ = lean_usize_of_nat(v___x_1368_);
            crate::leanh::lean_inc(v_included_1366_);
            v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1369_,
                v___f_1372_,
                v_ps_1356_,
                v___x_1380_,
                v___x_1381_,
                v_included_1366_,
            );
            crate::leanh::lean_inc_ref(v_isCandidateFn_1365_);
            v___x_1383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1383_, 0, v_isCandidateFn_1365_);
            crate::leanh::lean_ctor_set(v___x_1383_, 1, v___x_1382_);
            crate::leanh::lean_inc(v_a_1363_);
            crate::leanh::lean_inc_ref(v_a_1362_);
            crate::leanh::lean_inc(v_a_1361_);
            crate::leanh::lean_inc_ref(v_a_1360_);
            crate::leanh::lean_inc(v_a_1359_);
            v___x_1384_ = crate::leanh::lean_apply_7(
                v_x_1357_,
                v___x_1383_,
                v_a_1359_,
                v_a_1360_,
                v_a_1361_,
                v_a_1362_,
                v_a_1363_,
                crate::leanh::lean_box(0),
            );
            return v___x_1384_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withParams___boxed(
    mut v_00_u03b1_1385_: *mut crate::leanh::LeanObject,
    mut v_ps_1386_: *mut crate::leanh::LeanObject,
    mut v_x_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1395_ = l_Lean_Compiler_LCNF_PullLetDecls_withParams(
        v_00_u03b1_1385_,
        v_ps_1386_,
        v_x_1387_,
        v_a_1388_,
        v_a_1389_,
        v_a_1390_,
        v_a_1391_,
        v_a_1392_,
        v_a_1393_,
    );
    crate::leanh::lean_dec(v_a_1393_);
    crate::leanh::lean_dec_ref(v_a_1392_);
    crate::leanh::lean_dec(v_a_1391_);
    crate::leanh::lean_dec_ref(v_a_1390_);
    crate::leanh::lean_dec(v_a_1389_);
    crate::leanh::lean_dec_ref(v_a_1388_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(
    mut v_x_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isCandidateFn_1404_ = crate::leanh::lean_ctor_get(v_a_1397_, 0);
    v___x_1405_ = crate::leanh::lean_box(1);
    crate::leanh::lean_inc_ref(v_isCandidateFn_1404_);
    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v_isCandidateFn_1404_);
    crate::leanh::lean_ctor_set(v___x_1406_, 1, v___x_1405_);
    crate::leanh::lean_inc(v_a_1402_);
    crate::leanh::lean_inc_ref(v_a_1401_);
    crate::leanh::lean_inc(v_a_1400_);
    crate::leanh::lean_inc_ref(v_a_1399_);
    crate::leanh::lean_inc(v_a_1398_);
    v___x_1407_ = crate::leanh::lean_apply_7(
        v_x_1396_,
        v___x_1406_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
        v_a_1401_,
        v_a_1402_,
        crate::leanh::lean_box(0),
    );
    return v___x_1407_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg___boxed(
    mut v_x_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
    mut v_a_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___redArg(
        v_x_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_,
    );
    crate::leanh::lean_dec(v_a_1414_);
    crate::leanh::lean_dec_ref(v_a_1413_);
    crate::leanh::lean_dec(v_a_1412_);
    crate::leanh::lean_dec_ref(v_a_1411_);
    crate::leanh::lean_dec(v_a_1410_);
    crate::leanh::lean_dec_ref(v_a_1409_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(
    mut v_00_u03b1_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isCandidateFn_1426_ = crate::leanh::lean_ctor_get(v_a_1419_, 0);
    v___x_1427_ = crate::leanh::lean_box(1);
    crate::leanh::lean_inc_ref(v_isCandidateFn_1426_);
    v___x_1428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1428_, 0, v_isCandidateFn_1426_);
    crate::leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
    crate::leanh::lean_inc(v_a_1424_);
    crate::leanh::lean_inc_ref(v_a_1423_);
    crate::leanh::lean_inc(v_a_1422_);
    crate::leanh::lean_inc_ref(v_a_1421_);
    crate::leanh::lean_inc(v_a_1420_);
    v___x_1429_ = crate::leanh::lean_apply_7(
        v_x_1418_,
        v___x_1428_,
        v_a_1420_,
        v_a_1421_,
        v_a_1422_,
        v_a_1423_,
        v_a_1424_,
        crate::leanh::lean_box(0),
    );
    return v___x_1429_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withNewScope___boxed(
    mut v_00_u03b1_1430_: *mut crate::leanh::LeanObject,
    mut v_x_1431_: *mut crate::leanh::LeanObject,
    mut v_a_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
    mut v_a_1435_: *mut crate::leanh::LeanObject,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Lean_Compiler_LCNF_PullLetDecls_withNewScope(
        v_00_u03b1_1430_,
        v_x_1431_,
        v_a_1432_,
        v_a_1433_,
        v_a_1434_,
        v_a_1435_,
        v_a_1436_,
        v_a_1437_,
    );
    crate::leanh::lean_dec(v_a_1437_);
    crate::leanh::lean_dec_ref(v_a_1436_);
    crate::leanh::lean_dec(v_a_1435_);
    crate::leanh::lean_dec_ref(v_a_1434_);
    crate::leanh::lean_dec(v_a_1433_);
    crate::leanh::lean_dec_ref(v_a_1432_);
    return v_res_1439_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(
    mut v_c_1440_: *mut crate::leanh::LeanObject,
    mut v_toPull_1441_: *mut crate::leanh::LeanObject,
    mut v_i_1442_: *mut crate::leanh::LeanObject,
    mut v_included_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDecl_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1445_ = lean_array_get_size(v_toPull_1441_);
                v___x_1446_ = lean_nat_dec_lt(v_i_1442_, v___x_1445_);
                if v___x_1446_ == 0 {
                    crate::leanh::lean_dec(v_included_1443_);
                    crate::leanh::lean_dec(v_i_1442_);
                    v___x_1447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v_c_1440_);
                    crate::leanh::lean_ctor_set(v___x_1447_, 1, v_a_1444_);
                    return v___x_1447_;
                } else {
                    v_letDecl_1448_ = lean_array_fget_borrowed(v_toPull_1441_, v_i_1442_);
                    v___x_1449_ = 0;
                    v___x_1450_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v___x_1449_, v_letDecl_1448_, v_included_1443_);
                    if v___x_1450_ == 0 {
                        crate::leanh::lean_inc(v_letDecl_1448_);
                        v___x_1451_ = lean_array_push(v_a_1444_, v_letDecl_1448_);
                        v___x_1452_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1453_ = lean_nat_add(v_i_1442_, v___x_1452_);
                        crate::leanh::lean_dec(v_i_1442_);
                        v_i_1442_ = v___x_1453_;
                        v_a_1444_ = v___x_1451_;
                        state = 0;
                        continue;
                    } else {
                        v_fvarId_1455_ = crate::leanh::lean_ctor_get(v_letDecl_1448_, 0);
                        v___x_1456_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1457_ = lean_nat_add(v_i_1442_, v___x_1456_);
                        crate::leanh::lean_dec(v_i_1442_);
                        crate::leanh::lean_inc(v_fvarId_1455_);
                        v___x_1458_ = l_Lean_FVarIdSet_insert(v_included_1443_, v_fvarId_1455_);
                        v___x_1459_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_1440_, v_toPull_1441_, v___x_1457_, v___x_1458_, v_a_1444_);
                        v_fst_1460_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
                        v_snd_1461_ = crate::leanh::lean_ctor_get(v___x_1459_, 1);
                        v_isSharedCheck_1469_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1459_)) as u8;
                        if v_isSharedCheck_1469_ == 0 {
                            v___x_1463_ = v___x_1459_;
                            v_isShared_1464_ = v_isSharedCheck_1469_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1461_);
                            crate::leanh::lean_inc(v_fst_1460_);
                            crate::leanh::lean_dec(v___x_1459_);
                            v___x_1463_ = crate::leanh::lean_box(0);
                            v_isShared_1464_ = v_isSharedCheck_1469_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_letDecl_1448_);
                v___x_1465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1465_, 0, v_letDecl_1448_);
                crate::leanh::lean_ctor_set(v___x_1465_, 1, v_fst_1460_);
                if v_isShared_1464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1465_);
                    v___x_1467_ = v___x_1463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_snd_1461_);
                    v___x_1467_ = v_reuseFailAlloc_1468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go___boxed(
    mut v_c_1470_: *mut crate::leanh::LeanObject,
    mut v_toPull_1471_: *mut crate::leanh::LeanObject,
    mut v_i_1472_: *mut crate::leanh::LeanObject,
    mut v_included_1473_: *mut crate::leanh::LeanObject,
    mut v_a_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_c_1470_, v_toPull_1471_, v_i_1472_, v_included_1473_, v_a_1474_);
    crate::leanh::lean_dec_ref(v_toPull_1471_);
    return v_res_1475_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(
    mut v_x_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1486_ = lean_st_ref_get(v_a_1480_);
                v_isCandidateFn_1487_ = crate::leanh::lean_ctor_get(v_a_1479_, 0);
                v_included_1488_ = crate::leanh::lean_ctor_get(v_a_1479_, 1);
                v___x_1489_ = crate::leanh::lean_box(1);
                crate::leanh::lean_inc_ref(v_isCandidateFn_1487_);
                v___x_1490_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1490_, 0, v_isCandidateFn_1487_);
                crate::leanh::lean_ctor_set(v___x_1490_, 1, v___x_1489_);
                crate::leanh::lean_inc(v_a_1484_);
                crate::leanh::lean_inc_ref(v_a_1483_);
                crate::leanh::lean_inc(v_a_1482_);
                crate::leanh::lean_inc_ref(v_a_1481_);
                crate::leanh::lean_inc(v_a_1480_);
                v___x_1491_ = crate::leanh::lean_apply_7(
                    v_x_1478_,
                    v___x_1490_,
                    v_a_1480_,
                    v_a_1481_,
                    v_a_1482_,
                    v_a_1483_,
                    v_a_1484_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1491_) == 0 {
                    v_a_1492_ = crate::leanh::lean_ctor_get(v___x_1491_, 0);
                    v_isSharedCheck_1509_ = (!crate::leanh::lean_is_exclusive(v___x_1491_)) as u8;
                    if v_isSharedCheck_1509_ == 0 {
                        v___x_1494_ = v___x_1491_;
                        v_isShared_1495_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1492_);
                        crate::leanh::lean_dec(v___x_1491_);
                        v___x_1494_ = crate::leanh::lean_box(0);
                        v_isShared_1495_ = v_isSharedCheck_1509_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1486_);
                    return v___x_1491_;
                }
            }
            1 => {
                v___x_1496_ = lean_st_ref_get(v_a_1480_);
                v___x_1497_ = lean_array_get_size(v___x_1486_);
                crate::leanh::lean_dec(v___x_1486_);
                v___x_1498_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0;
                crate::leanh::lean_inc(v_included_1488_);
                v___x_1499_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_PullLetDecls_withCheckpoint_go(v_a_1492_, v___x_1496_, v___x_1497_, v_included_1488_, v___x_1498_);
                crate::leanh::lean_dec(v___x_1496_);
                v_fst_1500_ = crate::leanh::lean_ctor_get(v___x_1499_, 0);
                crate::leanh::lean_inc(v_fst_1500_);
                v_snd_1501_ = crate::leanh::lean_ctor_get(v___x_1499_, 1);
                crate::leanh::lean_inc(v_snd_1501_);
                crate::leanh::lean_dec_ref(v___x_1499_);
                v___x_1502_ = lean_st_ref_take(v_a_1480_);
                v___x_1503_ = l_Array_shrink___redArg(v___x_1502_, v___x_1497_);
                v___x_1504_ = l_Array_append___redArg(v___x_1503_, v_snd_1501_);
                crate::leanh::lean_dec(v_snd_1501_);
                v___x_1505_ = lean_st_ref_set(v_a_1480_, v___x_1504_);
                if v_isShared_1495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1494_, 0, v_fst_1500_);
                    v___x_1507_ = v___x_1494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_fst_1500_);
                    v___x_1507_ = v_reuseFailAlloc_1508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___boxed(
    mut v_x_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_a_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(
        v_x_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_,
    );
    crate::leanh::lean_dec(v_a_1516_);
    crate::leanh::lean_dec_ref(v_a_1515_);
    crate::leanh::lean_dec(v_a_1514_);
    crate::leanh::lean_dec_ref(v_a_1513_);
    crate::leanh::lean_dec(v_a_1512_);
    crate::leanh::lean_dec_ref(v_a_1511_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(
    mut v_as_1519_: *mut crate::leanh::LeanObject,
    mut v_i_1520_: usize,
    mut v_stop_1521_: usize,
    mut v_b_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1524_: usize = 0;
    let mut v___x_1525_: usize = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1523_ = lean_usize_dec_eq(v_i_1520_, v_stop_1521_);
                if v___x_1523_ == 0 {
                    v___x_1524_ = 1usize;
                    v___x_1525_ = lean_usize_sub(v_i_1520_, v___x_1524_);
                    v___x_1526_ = lean_array_uget_borrowed(v_as_1519_, v___x_1525_);
                    crate::leanh::lean_inc(v___x_1526_);
                    v___x_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                    crate::leanh::lean_ctor_set(v___x_1527_, 1, v_b_1522_);
                    v_i_1520_ = v___x_1525_;
                    v_b_1522_ = v___x_1527_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1522_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0___boxed(
    mut v_as_1529_: *mut crate::leanh::LeanObject,
    mut v_i_1530_: *mut crate::leanh::LeanObject,
    mut v_stop_1531_: *mut crate::leanh::LeanObject,
    mut v_b_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1533_: usize = 0;
    let mut v_stop_boxed_1534_: usize = 0;
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1533_ = crate::leanh::lean_unbox_usize(v_i_1530_);
    crate::leanh::lean_dec(v_i_1530_);
    v_stop_boxed_1534_ = crate::leanh::lean_unbox_usize(v_stop_1531_);
    crate::leanh::lean_dec(v_stop_1531_);
    v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v_as_1529_, v_i_boxed_1533_, v_stop_boxed_1534_, v_b_1532_);
    crate::leanh::lean_dec_ref(v_as_1529_);
    return v_res_1535_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(
    mut v_c_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    v___x_1539_ = lean_st_ref_get(v_a_1537_);
    v___x_1540_ = lean_array_get_size(v___x_1539_);
    v___x_1541_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1542_ = lean_nat_dec_lt(v___x_1541_, v___x_1540_);
    if v___x_1542_ == 0 {
        let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1539_);
        v___x_1543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1543_, 0, v_c_1536_);
        return v___x_1543_;
    } else {
        let mut v___x_1544_: usize = 0;
        let mut v___x_1545_: usize = 0;
        let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1544_ = lean_usize_of_nat(v___x_1540_);
        v___x_1545_ = 0usize;
        v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_attachToPull_spec__0(v___x_1539_, v___x_1544_, v___x_1545_, v_c_1536_);
        crate::leanh::lean_dec(v___x_1539_);
        v___x_1547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1546_);
        return v___x_1547_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg___boxed(
    mut v_c_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_1548_, v_a_1549_);
    crate::leanh::lean_dec(v_a_1549_);
    return v_res_1551_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(
    mut v_c_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___redArg(v_c_1552_, v_a_1554_);
    return v___x_1560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_attachToPull___boxed(
    mut v_c_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1569_ = l_Lean_Compiler_LCNF_PullLetDecls_attachToPull(
        v_c_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_,
    );
    crate::leanh::lean_dec(v_a_1567_);
    crate::leanh::lean_dec_ref(v_a_1566_);
    crate::leanh::lean_dec(v_a_1565_);
    crate::leanh::lean_dec_ref(v_a_1564_);
    crate::leanh::lean_dec(v_a_1563_);
    crate::leanh::lean_dec_ref(v_a_1562_);
    return v_res_1569_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(
    mut v_decl_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isCandidateFn_1582_ = crate::leanh::lean_ctor_get(v_a_1571_, 0);
                v_included_1583_ = crate::leanh::lean_ctor_get(v_a_1571_, 1);
                v___x_1584_ = 0;
                v___x_1585_ =
                    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
                        v___x_1584_,
                        v_decl_1570_,
                        v_included_1583_,
                    );
                if v___x_1585_ == 0 {
                    crate::leanh::lean_inc_ref(v_isCandidateFn_1582_);
                    crate::leanh::lean_inc(v_a_1576_);
                    crate::leanh::lean_inc_ref(v_a_1575_);
                    crate::leanh::lean_inc(v_a_1574_);
                    crate::leanh::lean_inc_ref(v_a_1573_);
                    crate::leanh::lean_inc(v_included_1583_);
                    crate::leanh::lean_inc_ref(v_decl_1570_);
                    v___x_1586_ = crate::leanh::lean_apply_7(
                        v_isCandidateFn_1582_,
                        v_decl_1570_,
                        v_included_1583_,
                        v_a_1573_,
                        v_a_1574_,
                        v_a_1575_,
                        v_a_1576_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1586_) == 0 {
                        v_a_1587_ = crate::leanh::lean_ctor_get(v___x_1586_, 0);
                        v_isSharedCheck_1598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1586_)) as u8;
                        if v_isSharedCheck_1598_ == 0 {
                            v___x_1589_ = v___x_1586_;
                            v_isShared_1590_ = v_isSharedCheck_1598_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1587_);
                            crate::leanh::lean_dec(v___x_1586_);
                            v___x_1589_ = crate::leanh::lean_box(0);
                            v_isShared_1590_ = v_isSharedCheck_1598_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_decl_1570_);
                        return v___x_1586_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_1570_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1579_ = 0;
                v___x_1580_ = crate::leanh::lean_box((v___x_1579_) as usize);
                v___x_1581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1580_);
                return v___x_1581_;
            }
            2 => {
                v___x_1591_ = (crate::leanh::lean_unbox(v_a_1587_) as u8);
                if v___x_1591_ == 0 {
                    crate::leanh::lean_del_object(v___x_1589_);
                    crate::leanh::lean_dec(v_a_1587_);
                    crate::leanh::lean_dec_ref(v_decl_1570_);
                    state = 1;
                    continue;
                } else {
                    v___x_1592_ = lean_st_ref_take(v_a_1572_);
                    v___x_1593_ = lean_array_push(v___x_1592_, v_decl_1570_);
                    v___x_1594_ = lean_st_ref_set(v_a_1572_, v___x_1593_);
                    if v_isShared_1590_ == 0 {
                        v___x_1596_ = v___x_1589_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1587_);
                        v___x_1596_ = v_reuseFailAlloc_1597_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_shouldPull___boxed(
    mut v_decl_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
    mut v_a_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(
        v_decl_1599_,
        v_a_1600_,
        v_a_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
    );
    crate::leanh::lean_dec(v_a_1605_);
    crate::leanh::lean_dec_ref(v_a_1604_);
    crate::leanh::lean_dec(v_a_1603_);
    crate::leanh::lean_dec_ref(v_a_1602_);
    crate::leanh::lean_dec(v_a_1601_);
    crate::leanh::lean_dec_ref(v_a_1600_);
    return v_res_1607_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(
    mut v_as_1608_: *mut crate::leanh::LeanObject,
    mut v_i_1609_: usize,
    mut v_stop_1610_: usize,
    mut v_b_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: usize = 0;
    let mut v___x_1617_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1612_ = lean_usize_dec_eq(v_i_1609_, v_stop_1610_);
                if v___x_1612_ == 0 {
                    v___x_1613_ = lean_array_uget_borrowed(v_as_1608_, v_i_1609_);
                    v_fvarId_1614_ = crate::leanh::lean_ctor_get(v___x_1613_, 0);
                    crate::leanh::lean_inc(v_fvarId_1614_);
                    v___x_1615_ = l_Lean_FVarIdSet_insert(v_b_1611_, v_fvarId_1614_);
                    v___x_1616_ = 1usize;
                    v___x_1617_ = lean_usize_add(v_i_1609_, v___x_1616_);
                    v_i_1609_ = v___x_1617_;
                    v_b_1611_ = v___x_1615_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1611_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0___boxed(
    mut v_as_1619_: *mut crate::leanh::LeanObject,
    mut v_i_1620_: *mut crate::leanh::LeanObject,
    mut v_stop_1621_: *mut crate::leanh::LeanObject,
    mut v_b_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1623_: usize = 0;
    let mut v_stop_boxed_1624_: usize = 0;
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1623_ = crate::leanh::lean_unbox_usize(v_i_1620_);
    crate::leanh::lean_dec(v_i_1620_);
    v_stop_boxed_1624_ = crate::leanh::lean_unbox_usize(v_stop_1621_);
    crate::leanh::lean_dec(v_stop_1621_);
    v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_as_1619_, v_i_boxed_1623_, v_stop_boxed_1624_, v_b_1622_);
    crate::leanh::lean_dec_ref(v_as_1619_);
    return v_res_1625_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = 0;
    v___x_1627_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1626_);
    return v___x_1627_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(
    mut v_msg_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2___closed__0,
    );
    v___x_1630_ = lean_panic_fn_borrowed(v___x_1629_, v_msg_1628_);
    return v___x_1630_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__2;
    v___x_1635_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1636_ = crate::leanh::lean_unsigned_to_nat(641);
    v___x_1637_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__1;
    v___x_1638_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__0;
    v___x_1639_ = l_mkPanicMessageWithDecl(
        v___x_1638_,
        v___x_1637_,
        v___x_1636_,
        v___x_1635_,
        v___x_1634_,
    );
    return v___x_1639_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(
    mut v_code_1640_: *mut crate::leanh::LeanObject,
    mut v___x_1641_: u8,
    mut v_decl_1642_: *mut crate::leanh::LeanObject,
    mut v_type_1643_: *mut crate::leanh::LeanObject,
    mut v_params_1644_: *mut crate::leanh::LeanObject,
    mut v_k_1645_: *mut crate::leanh::LeanObject,
    mut v_value_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: u8 = 0;
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: usize = 0;
    let mut v___x_1683_: usize = 0;
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: usize = 0;
    let mut v___x_1686_: usize = 0;
    let mut v___x_1687_: u8 = 0;
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: usize = 0;
    let mut v___x_1692_: usize = 0;
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: usize = 0;
    let mut v___x_1695_: usize = 0;
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1705_: u8 = 0;
    let mut v_unused_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1710_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isCandidateFn_1668_ = crate::leanh::lean_ctor_get(v___y_1647_, 0);
                v_included_1669_ = crate::leanh::lean_ctor_get(v___y_1647_, 1);
                v___x_1715_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1716_ = lean_array_get_size(v_params_1644_);
                v___x_1717_ = lean_nat_dec_lt(v___x_1715_, v___x_1716_);
                if v___x_1717_ == 0 {
                    crate::leanh::lean_inc(v_included_1669_);
                    crate::leanh::lean_inc_ref(v_isCandidateFn_1668_);
                    v___x_1718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v_isCandidateFn_1668_);
                    crate::leanh::lean_ctor_set(v___x_1718_, 1, v_included_1669_);
                    v___x_1719_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                        v_value_1646_,
                        v___x_1718_,
                        v___y_1648_,
                        v___y_1649_,
                        v___y_1650_,
                        v___y_1651_,
                        v___y_1652_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_1718_, 2);
                    v___y_1671_ = v___x_1719_;
                    state = 3;
                    continue;
                } else {
                    v___x_1720_ = lean_nat_dec_le(v___x_1716_, v___x_1716_);
                    if v___x_1720_ == 0 {
                        if v___x_1717_ == 0 {
                            crate::leanh::lean_inc(v_included_1669_);
                            crate::leanh::lean_inc_ref(v_isCandidateFn_1668_);
                            v___x_1721_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1721_, 0, v_isCandidateFn_1668_);
                            crate::leanh::lean_ctor_set(v___x_1721_, 1, v_included_1669_);
                            v___x_1722_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                v_value_1646_,
                                v___x_1721_,
                                v___y_1648_,
                                v___y_1649_,
                                v___y_1650_,
                                v___y_1651_,
                                v___y_1652_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1721_, 2);
                            v___y_1671_ = v___x_1722_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1723_ = 0usize;
                            v___x_1724_ = lean_usize_of_nat(v___x_1716_);
                            crate::leanh::lean_inc(v_included_1669_);
                            v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1644_, v___x_1723_, v___x_1724_, v_included_1669_);
                            crate::leanh::lean_inc_ref(v_isCandidateFn_1668_);
                            v___x_1726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1726_, 0, v_isCandidateFn_1668_);
                            crate::leanh::lean_ctor_set(v___x_1726_, 1, v___x_1725_);
                            v___x_1727_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                v_value_1646_,
                                v___x_1726_,
                                v___y_1648_,
                                v___y_1649_,
                                v___y_1650_,
                                v___y_1651_,
                                v___y_1652_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1726_, 2);
                            v___y_1671_ = v___x_1727_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1728_ = 0usize;
                        v___x_1729_ = lean_usize_of_nat(v___x_1716_);
                        crate::leanh::lean_inc(v_included_1669_);
                        v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1644_, v___x_1728_, v___x_1729_, v_included_1669_);
                        crate::leanh::lean_inc_ref(v_isCandidateFn_1668_);
                        v___x_1731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1731_, 0, v_isCandidateFn_1668_);
                        crate::leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                        v___x_1732_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                            v_value_1646_,
                            v___x_1731_,
                            v___y_1648_,
                            v___y_1649_,
                            v___y_1650_,
                            v___y_1651_,
                            v___y_1652_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_1731_, 2);
                        v___y_1671_ = v___x_1732_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1657_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_1640_);
                    v___x_1658_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1658_, 0, v___y_1656_);
                    crate::leanh::lean_ctor_set(v___x_1658_, 1, v___y_1655_);
                    v___x_1659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1659_, 0, v___x_1658_);
                    return v___x_1659_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1656_);
                    crate::leanh::lean_dec_ref(v___y_1655_);
                    v___x_1660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1660_, 0, v_code_1640_);
                    return v___x_1660_;
                }
            }
            2 => {
                if v___y_1664_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_1640_);
                    v___x_1665_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___y_1663_);
                    crate::leanh::lean_ctor_set(v___x_1665_, 1, v___y_1662_);
                    v___x_1666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
                    return v___x_1666_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1663_);
                    crate::leanh::lean_dec_ref(v___y_1662_);
                    v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1667_, 0, v_code_1640_);
                    return v___x_1667_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_1671_) == 0 {
                    v_a_1672_ = crate::leanh::lean_ctor_get(v___y_1671_, 0);
                    crate::leanh::lean_inc(v_a_1672_);
                    crate::leanh::lean_dec_ref_known(v___y_1671_, 1);
                    v___x_1673_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1641_, v_decl_1642_, v_type_1643_, v_params_1644_, v_a_1672_, v___y_1650_);
                    if crate::leanh::lean_obj_tag(v___x_1673_) == 0 {
                        v_a_1674_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                        crate::leanh::lean_inc(v_a_1674_);
                        crate::leanh::lean_dec_ref_known(v___x_1673_, 1);
                        v_fvarId_1675_ = crate::leanh::lean_ctor_get(v_a_1674_, 0);
                        crate::leanh::lean_inc(v_fvarId_1675_);
                        crate::leanh::lean_inc(v_included_1669_);
                        v___x_1676_ = l_Lean_FVarIdSet_insert(v_included_1669_, v_fvarId_1675_);
                        crate::leanh::lean_inc_ref(v_isCandidateFn_1668_);
                        v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1677_, 0, v_isCandidateFn_1668_);
                        crate::leanh::lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                        v___x_1678_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                            v_k_1645_,
                            v___x_1677_,
                            v___y_1648_,
                            v___y_1649_,
                            v___y_1650_,
                            v___y_1651_,
                            v___y_1652_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_1677_, 2);
                        if crate::leanh::lean_obj_tag(v___x_1678_) == 0 {
                            match crate::leanh::lean_obj_tag(v_code_1640_) {
                                1 => {
                                    v_a_1679_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                                    crate::leanh::lean_inc(v_a_1679_);
                                    crate::leanh::lean_dec_ref_known(v___x_1678_, 1);
                                    v_decl_1680_ = crate::leanh::lean_ctor_get(v_code_1640_, 0);
                                    v_k_1681_ = crate::leanh::lean_ctor_get(v_code_1640_, 1);
                                    v___x_1682_ = lean_ptr_addr(v_k_1681_);
                                    v___x_1683_ = lean_ptr_addr(v_a_1679_);
                                    v___x_1684_ = lean_usize_dec_eq(v___x_1682_, v___x_1683_);
                                    if v___x_1684_ == 0 {
                                        v___y_1655_ = v_a_1679_;
                                        v___y_1656_ = v_a_1674_;
                                        v___y_1657_ = v___x_1684_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1685_ = lean_ptr_addr(v_decl_1680_);
                                        v___x_1686_ = lean_ptr_addr(v_a_1674_);
                                        v___x_1687_ = lean_usize_dec_eq(v___x_1685_, v___x_1686_);
                                        v___y_1655_ = v_a_1679_;
                                        v___y_1656_ = v_a_1674_;
                                        v___y_1657_ = v___x_1687_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                2 => {
                                    v_a_1688_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                                    crate::leanh::lean_inc(v_a_1688_);
                                    crate::leanh::lean_dec_ref_known(v___x_1678_, 1);
                                    v_decl_1689_ = crate::leanh::lean_ctor_get(v_code_1640_, 0);
                                    v_k_1690_ = crate::leanh::lean_ctor_get(v_code_1640_, 1);
                                    v___x_1691_ = lean_ptr_addr(v_k_1690_);
                                    v___x_1692_ = lean_ptr_addr(v_a_1688_);
                                    v___x_1693_ = lean_usize_dec_eq(v___x_1691_, v___x_1692_);
                                    if v___x_1693_ == 0 {
                                        v___y_1662_ = v_a_1688_;
                                        v___y_1663_ = v_a_1674_;
                                        v___y_1664_ = v___x_1693_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1694_ = lean_ptr_addr(v_decl_1689_);
                                        v___x_1695_ = lean_ptr_addr(v_a_1674_);
                                        v___x_1696_ = lean_usize_dec_eq(v___x_1694_, v___x_1695_);
                                        v___y_1662_ = v_a_1688_;
                                        v___y_1663_ = v_a_1674_;
                                        v___y_1664_ = v___x_1696_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                _ => {
                                    crate::leanh::lean_dec(v_a_1674_);
                                    crate::leanh::lean_dec_ref(v_code_1640_);
                                    v_isSharedCheck_1705_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1678_)) as u8;
                                    if v_isSharedCheck_1705_ == 0 {
                                        v_unused_1706_ =
                                            crate::leanh::lean_ctor_get(v___x_1678_, 0);
                                        crate::leanh::lean_dec(v_unused_1706_);
                                        v___x_1698_ = v___x_1678_;
                                        v_isShared_1699_ = v_isSharedCheck_1705_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1678_);
                                        v___x_1698_ = crate::leanh::lean_box(0);
                                        v_isShared_1699_ = v_isSharedCheck_1705_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1674_);
                            crate::leanh::lean_dec_ref(v_code_1640_);
                            return v___x_1678_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_1645_);
                        crate::leanh::lean_dec_ref(v_code_1640_);
                        v_a_1707_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                        v_isSharedCheck_1714_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1673_)) as u8;
                        if v_isSharedCheck_1714_ == 0 {
                            v___x_1709_ = v___x_1673_;
                            v_isShared_1710_ = v_isSharedCheck_1714_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1707_);
                            crate::leanh::lean_dec(v___x_1673_);
                            v___x_1709_ = crate::leanh::lean_box(0);
                            v_isShared_1710_ = v_isSharedCheck_1714_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_1645_);
                    crate::leanh::lean_dec_ref(v_params_1644_);
                    crate::leanh::lean_dec_ref(v_type_1643_);
                    crate::leanh::lean_dec_ref(v_decl_1642_);
                    crate::leanh::lean_dec_ref(v_code_1640_);
                    return v___y_1671_;
                }
            }
            4 => {
                v___x_1700_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___closed__3,
                );
                v___x_1701_ =
                    l_panic___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__2(v___x_1700_);
                if v_isShared_1699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1698_, 0, v___x_1701_);
                    v___x_1703_ = v___x_1698_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
                    v___x_1703_ = v_reuseFailAlloc_1704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1703_;
            }
            6 => {
                if v_isShared_1710_ == 0 {
                    v___x_1712_ = v___x_1709_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed(
    mut v_code_1733_: *mut crate::leanh::LeanObject,
    mut v___x_1734_: *mut crate::leanh::LeanObject,
    mut v_decl_1735_: *mut crate::leanh::LeanObject,
    mut v_type_1736_: *mut crate::leanh::LeanObject,
    mut v_params_1737_: *mut crate::leanh::LeanObject,
    mut v_k_1738_: *mut crate::leanh::LeanObject,
    mut v_value_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4729__boxed_1747_: u8 = 0;
    let mut v_res_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4729__boxed_1747_ = (crate::leanh::lean_unbox(v___x_1734_) as u8);
    v_res_1748_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0(
        v_code_1733_,
        v___x_4729__boxed_1747_,
        v_decl_1735_,
        v_type_1736_,
        v_params_1737_,
        v_k_1738_,
        v_value_1739_,
        v___y_1740_,
        v___y_1741_,
        v___y_1742_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
    );
    crate::leanh::lean_dec(v___y_1745_);
    crate::leanh::lean_dec_ref(v___y_1744_);
    crate::leanh::lean_dec(v___y_1743_);
    crate::leanh::lean_dec_ref(v___y_1742_);
    crate::leanh::lean_dec(v___y_1741_);
    crate::leanh::lean_dec_ref(v___y_1740_);
    return v_res_1748_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed(
    mut v___x_1752_: *mut crate::leanh::LeanObject,
    mut v_alts_1753_: *mut crate::leanh::LeanObject,
    mut v_typeName_1754_: *mut crate::leanh::LeanObject,
    mut v_resultType_1755_: *mut crate::leanh::LeanObject,
    mut v_discr_1756_: *mut crate::leanh::LeanObject,
    mut v_code_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
    mut v___y_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1765_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(
        v___x_1752_,
        v_alts_1753_,
        v_typeName_1754_,
        v_resultType_1755_,
        v_discr_1756_,
        v_code_1757_,
        v___y_1758_,
        v___y_1759_,
        v___y_1760_,
        v___y_1761_,
        v___y_1762_,
        v___y_1763_,
    );
    crate::leanh::lean_dec(v___y_1763_);
    crate::leanh::lean_dec_ref(v___y_1762_);
    crate::leanh::lean_dec(v___y_1761_);
    crate::leanh::lean_dec_ref(v___y_1760_);
    crate::leanh::lean_dec(v___y_1759_);
    crate::leanh::lean_dec_ref(v___y_1758_);
    return v_res_1765_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
    mut v_code_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v_fvarId_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1816_: usize = 0;
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_unused_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_a_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1839_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_decl_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_1766_) {
                4 => {
                    v_cases_1790_ = crate::leanh::lean_ctor_get(v_code_1766_, 0);
                    v_typeName_1791_ = crate::leanh::lean_ctor_get(v_cases_1790_, 0);
                    v_resultType_1792_ = crate::leanh::lean_ctor_get(v_cases_1790_, 1);
                    v_discr_1793_ = crate::leanh::lean_ctor_get(v_cases_1790_, 2);
                    v_alts_1794_ = crate::leanh::lean_ctor_get(v_cases_1790_, 3);
                    v___x_1795_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___closed__1;
                    v___x_1796_ = lean_name_eq(v_typeName_1791_, v___x_1795_);
                    if v___x_1796_ == 0 {
                        crate::leanh::lean_inc_ref(v_alts_1794_);
                        crate::leanh::lean_inc(v_discr_1793_);
                        crate::leanh::lean_inc_ref(v_resultType_1792_);
                        crate::leanh::lean_inc(v_typeName_1791_);
                        v___x_1797_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___f_1798_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1___boxed
                                as *mut core::ffi::c_void,
                            13,
                            6,
                        );
                        crate::leanh::lean_closure_set(v___f_1798_, 0, v___x_1797_);
                        crate::leanh::lean_closure_set(v___f_1798_, 1, v_alts_1794_);
                        crate::leanh::lean_closure_set(v___f_1798_, 2, v_typeName_1791_);
                        crate::leanh::lean_closure_set(v___f_1798_, 3, v_resultType_1792_);
                        crate::leanh::lean_closure_set(v___f_1798_, 4, v_discr_1793_);
                        crate::leanh::lean_closure_set(v___f_1798_, 5, v_code_1766_);
                        v___x_1799_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(
                            v___f_1798_,
                            v_a_1767_,
                            v_a_1768_,
                            v_a_1769_,
                            v_a_1770_,
                            v_a_1771_,
                            v_a_1772_,
                        );
                        return v___x_1799_;
                    } else {
                        v___x_1800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1800_, 0, v_code_1766_);
                        return v___x_1800_;
                    }
                }
                0 => {
                    v_decl_1801_ = crate::leanh::lean_ctor_get(v_code_1766_, 0);
                    v_k_1802_ = crate::leanh::lean_ctor_get(v_code_1766_, 1);
                    crate::leanh::lean_inc_ref(v_decl_1801_);
                    v___x_1803_ = l_Lean_Compiler_LCNF_PullLetDecls_shouldPull(
                        v_decl_1801_,
                        v_a_1767_,
                        v_a_1768_,
                        v_a_1769_,
                        v_a_1770_,
                        v_a_1771_,
                        v_a_1772_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1803_) == 0 {
                        v_a_1804_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                        crate::leanh::lean_inc(v_a_1804_);
                        crate::leanh::lean_dec_ref_known(v___x_1803_, 1);
                        v___x_1805_ = (crate::leanh::lean_unbox(v_a_1804_) as u8);
                        crate::leanh::lean_dec(v_a_1804_);
                        if v___x_1805_ == 0 {
                            v_fvarId_1806_ = crate::leanh::lean_ctor_get(v_decl_1801_, 0);
                            v_isCandidateFn_1807_ = crate::leanh::lean_ctor_get(v_a_1767_, 0);
                            v_included_1808_ = crate::leanh::lean_ctor_get(v_a_1767_, 1);
                            crate::leanh::lean_inc(v_fvarId_1806_);
                            crate::leanh::lean_inc(v_included_1808_);
                            v___x_1809_ = l_Lean_FVarIdSet_insert(v_included_1808_, v_fvarId_1806_);
                            crate::leanh::lean_inc_ref(v_isCandidateFn_1807_);
                            v___x_1810_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1810_, 0, v_isCandidateFn_1807_);
                            crate::leanh::lean_ctor_set(v___x_1810_, 1, v___x_1809_);
                            crate::leanh::lean_inc_ref(v_k_1802_);
                            v___x_1811_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                v_k_1802_,
                                v___x_1810_,
                                v_a_1768_,
                                v_a_1769_,
                                v_a_1770_,
                                v_a_1771_,
                                v_a_1772_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1810_, 2);
                            if crate::leanh::lean_obj_tag(v___x_1811_) == 0 {
                                v_a_1812_ = crate::leanh::lean_ctor_get(v___x_1811_, 0);
                                v_isSharedCheck_1834_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1811_)) as u8;
                                if v_isSharedCheck_1834_ == 0 {
                                    v___x_1814_ = v___x_1811_;
                                    v_isShared_1815_ = v_isSharedCheck_1834_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1812_);
                                    crate::leanh::lean_dec(v___x_1811_);
                                    v___x_1814_ = crate::leanh::lean_box(0);
                                    v_isShared_1815_ = v_isSharedCheck_1834_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_code_1766_, 2);
                                return v___x_1811_;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_k_1802_);
                            crate::leanh::lean_dec_ref_known(v_code_1766_, 2);
                            v_code_1766_ = v_k_1802_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_1766_, 2);
                        v_a_1836_ = crate::leanh::lean_ctor_get(v___x_1803_, 0);
                        v_isSharedCheck_1843_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1803_)) as u8;
                        if v_isSharedCheck_1843_ == 0 {
                            v___x_1838_ = v___x_1803_;
                            v_isShared_1839_ = v_isSharedCheck_1843_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1836_);
                            crate::leanh::lean_dec(v___x_1803_);
                            v___x_1838_ = crate::leanh::lean_box(0);
                            v_isShared_1839_ = v_isSharedCheck_1843_;
                            state = 7;
                            continue;
                        }
                    }
                }
                1 => {
                    v_decl_1844_ = crate::leanh::lean_ctor_get(v_code_1766_, 0);
                    v_k_1845_ = crate::leanh::lean_ctor_get(v_code_1766_, 1);
                    crate::leanh::lean_inc_ref(v_k_1845_);
                    crate::leanh::lean_inc_ref(v_decl_1844_);
                    v_decl_1775_ = v_decl_1844_;
                    v_k_1776_ = v_k_1845_;
                    v___y_1777_ = v_a_1767_;
                    v___y_1778_ = v_a_1768_;
                    v___y_1779_ = v_a_1769_;
                    v___y_1780_ = v_a_1770_;
                    v___y_1781_ = v_a_1771_;
                    v___y_1782_ = v_a_1772_;
                    state = 1;
                    continue;
                }
                2 => {
                    v_decl_1846_ = crate::leanh::lean_ctor_get(v_code_1766_, 0);
                    v_k_1847_ = crate::leanh::lean_ctor_get(v_code_1766_, 1);
                    crate::leanh::lean_inc_ref(v_k_1847_);
                    crate::leanh::lean_inc_ref(v_decl_1846_);
                    v_decl_1775_ = v_decl_1846_;
                    v_k_1776_ = v_k_1847_;
                    v___y_1777_ = v_a_1767_;
                    v___y_1778_ = v_a_1768_;
                    v___y_1779_ = v_a_1769_;
                    v___y_1780_ = v_a_1770_;
                    v___y_1781_ = v_a_1771_;
                    v___y_1782_ = v_a_1772_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___x_1848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1848_, 0, v_code_1766_);
                    return v___x_1848_;
                }
            },
            1 => {
                v_params_1783_ = crate::leanh::lean_ctor_get(v_decl_1775_, 2);
                crate::leanh::lean_inc_ref(v_params_1783_);
                v_type_1784_ = crate::leanh::lean_ctor_get(v_decl_1775_, 3);
                crate::leanh::lean_inc_ref(v_type_1784_);
                v_value_1785_ = crate::leanh::lean_ctor_get(v_decl_1775_, 4);
                crate::leanh::lean_inc_ref(v_value_1785_);
                v___x_1786_ = 0;
                v___x_1787_ = crate::leanh::lean_box((v___x_1786_) as usize);
                v___f_1788_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__0___boxed
                        as *mut core::ffi::c_void,
                    14,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_1788_, 0, v_code_1766_);
                crate::leanh::lean_closure_set(v___f_1788_, 1, v___x_1787_);
                crate::leanh::lean_closure_set(v___f_1788_, 2, v_decl_1775_);
                crate::leanh::lean_closure_set(v___f_1788_, 3, v_type_1784_);
                crate::leanh::lean_closure_set(v___f_1788_, 4, v_params_1783_);
                crate::leanh::lean_closure_set(v___f_1788_, 5, v_k_1776_);
                crate::leanh::lean_closure_set(v___f_1788_, 6, v_value_1785_);
                v___x_1789_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint(
                    v___f_1788_,
                    v___y_1777_,
                    v___y_1778_,
                    v___y_1779_,
                    v___y_1780_,
                    v___y_1781_,
                    v___y_1782_,
                );
                return v___x_1789_;
            }
            2 => {
                v___x_1816_ = lean_ptr_addr(v_k_1802_);
                v___x_1817_ = lean_ptr_addr(v_a_1812_);
                v___x_1818_ = lean_usize_dec_eq(v___x_1816_, v___x_1817_);
                if v___x_1818_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_1801_);
                    v_isSharedCheck_1828_ = (!crate::leanh::lean_is_exclusive(v_code_1766_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v_unused_1829_ = crate::leanh::lean_ctor_get(v_code_1766_, 1);
                        crate::leanh::lean_dec(v_unused_1829_);
                        v_unused_1830_ = crate::leanh::lean_ctor_get(v_code_1766_, 0);
                        crate::leanh::lean_dec(v_unused_1830_);
                        v___x_1820_ = v_code_1766_;
                        v_isShared_1821_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_1766_);
                        v___x_1820_ = crate::leanh::lean_box(0);
                        v_isShared_1821_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1812_);
                    if v_isShared_1815_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1814_, 0, v_code_1766_);
                        v___x_1832_ = v___x_1814_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_code_1766_);
                        v___x_1832_ = v_reuseFailAlloc_1833_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_a_1812_);
                    v___x_1823_ = v___x_1820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_decl_1801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_a_1812_);
                    v___x_1823_ = v_reuseFailAlloc_1827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1815_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1814_, 0, v___x_1823_);
                    v___x_1825_ = v___x_1814_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1825_;
            }
            6 => {
                return v___x_1832_;
            }
            7 => {
                if v_isShared_1839_ == 0 {
                    v___x_1841_ = v___x_1838_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
                    v___x_1841_ = v_reuseFailAlloc_1842_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(
    mut v_alt_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut v_a_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1871_: u8 = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut v_params_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: usize = 0;
    let mut v___x_1889_: usize = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: usize = 0;
    let mut v___x_1894_: usize = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isCandidateFn_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_alt_1849_) == 0 {
                    v_params_1876_ = crate::leanh::lean_ctor_get(v_alt_1849_, 1);
                    v_code_1877_ = crate::leanh::lean_ctor_get(v_alt_1849_, 2);
                    v_isCandidateFn_1878_ = crate::leanh::lean_ctor_get(v_a_1850_, 0);
                    v___x_1879_ = crate::leanh::lean_box(1);
                    v___x_1880_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1881_ = lean_array_get_size(v_params_1876_);
                    v___x_1882_ = lean_nat_dec_lt(v___x_1880_, v___x_1881_);
                    if v___x_1882_ == 0 {
                        crate::leanh::lean_inc_ref(v_isCandidateFn_1878_);
                        v___x_1883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1883_, 0, v_isCandidateFn_1878_);
                        crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1879_);
                        crate::leanh::lean_inc_ref(v_code_1877_);
                        v___x_1884_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                            v_code_1877_,
                            v___x_1883_,
                            v_a_1851_,
                            v_a_1852_,
                            v_a_1853_,
                            v_a_1854_,
                            v_a_1855_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_1883_, 2);
                        v___y_1858_ = v___x_1884_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1885_ = lean_nat_dec_le(v___x_1881_, v___x_1881_);
                        if v___x_1885_ == 0 {
                            if v___x_1882_ == 0 {
                                crate::leanh::lean_inc_ref(v_isCandidateFn_1878_);
                                v___x_1886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1886_, 0, v_isCandidateFn_1878_);
                                crate::leanh::lean_ctor_set(v___x_1886_, 1, v___x_1879_);
                                crate::leanh::lean_inc_ref(v_code_1877_);
                                v___x_1887_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                    v_code_1877_,
                                    v___x_1886_,
                                    v_a_1851_,
                                    v_a_1852_,
                                    v_a_1853_,
                                    v_a_1854_,
                                    v_a_1855_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_1886_, 2);
                                v___y_1858_ = v___x_1887_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1888_ = 0usize;
                                v___x_1889_ = lean_usize_of_nat(v___x_1881_);
                                v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1876_, v___x_1888_, v___x_1889_, v___x_1879_);
                                crate::leanh::lean_inc_ref(v_isCandidateFn_1878_);
                                v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1891_, 0, v_isCandidateFn_1878_);
                                crate::leanh::lean_ctor_set(v___x_1891_, 1, v___x_1890_);
                                crate::leanh::lean_inc_ref(v_code_1877_);
                                v___x_1892_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                    v_code_1877_,
                                    v___x_1891_,
                                    v_a_1851_,
                                    v_a_1852_,
                                    v_a_1853_,
                                    v_a_1854_,
                                    v_a_1855_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_1891_, 2);
                                v___y_1858_ = v___x_1892_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1893_ = 0usize;
                            v___x_1894_ = lean_usize_of_nat(v___x_1881_);
                            v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_1876_, v___x_1893_, v___x_1894_, v___x_1879_);
                            crate::leanh::lean_inc_ref(v_isCandidateFn_1878_);
                            v___x_1896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1896_, 0, v_isCandidateFn_1878_);
                            crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
                            crate::leanh::lean_inc_ref(v_code_1877_);
                            v___x_1897_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                                v_code_1877_,
                                v___x_1896_,
                                v_a_1851_,
                                v_a_1852_,
                                v_a_1853_,
                                v_a_1854_,
                                v_a_1855_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1896_, 2);
                            v___y_1858_ = v___x_1897_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_code_1898_ = crate::leanh::lean_ctor_get(v_alt_1849_, 0);
                    v_isCandidateFn_1899_ = crate::leanh::lean_ctor_get(v_a_1850_, 0);
                    v___x_1900_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc_ref(v_isCandidateFn_1899_);
                    v___x_1901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v_isCandidateFn_1899_);
                    crate::leanh::lean_ctor_set(v___x_1901_, 1, v___x_1900_);
                    crate::leanh::lean_inc_ref(v_code_1898_);
                    v___x_1902_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
                        v_code_1898_,
                        v___x_1901_,
                        v_a_1851_,
                        v_a_1852_,
                        v_a_1853_,
                        v_a_1854_,
                        v_a_1855_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_1901_, 2);
                    if crate::leanh::lean_obj_tag(v___x_1902_) == 0 {
                        v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1902_, 0);
                        v_isSharedCheck_1911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1902_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1905_ = v___x_1902_;
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1903_);
                            crate::leanh::lean_dec(v___x_1902_);
                            v___x_1905_ = crate::leanh::lean_box(0);
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_alt_1849_, 1);
                        v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1902_, 0);
                        v_isSharedCheck_1919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1902_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1902_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1912_);
                            crate::leanh::lean_dec(v___x_1902_);
                            v___x_1914_ = crate::leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1858_) == 0 {
                    v_a_1859_ = crate::leanh::lean_ctor_get(v___y_1858_, 0);
                    v_isSharedCheck_1867_ = (!crate::leanh::lean_is_exclusive(v___y_1858_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v___x_1861_ = v___y_1858_;
                        v_isShared_1862_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1859_);
                        crate::leanh::lean_dec(v___y_1858_);
                        v___x_1861_ = crate::leanh::lean_box(0);
                        v_isShared_1862_ = v_isSharedCheck_1867_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alt_1849_);
                    v_a_1868_ = crate::leanh::lean_ctor_get(v___y_1858_, 0);
                    v_isSharedCheck_1875_ = (!crate::leanh::lean_is_exclusive(v___y_1858_)) as u8;
                    if v_isSharedCheck_1875_ == 0 {
                        v___x_1870_ = v___y_1858_;
                        v_isShared_1871_ = v_isSharedCheck_1875_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1868_);
                        crate::leanh::lean_dec(v___y_1858_);
                        v___x_1870_ = crate::leanh::lean_box(0);
                        v_isShared_1871_ = v_isSharedCheck_1875_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1863_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1849_, v_a_1859_);
                if v_isShared_1862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1863_);
                    v___x_1865_ = v___x_1861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
                    v___x_1865_ = v_reuseFailAlloc_1866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1865_;
            }
            4 => {
                if v_isShared_1871_ == 0 {
                    v___x_1873_ = v___x_1870_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
                    v___x_1873_ = v_reuseFailAlloc_1874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1873_;
            }
            6 => {
                v___x_1907_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1849_, v_a_1903_);
                if v_isShared_1906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1907_);
                    v___x_1909_ = v___x_1905_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
                    v___x_1909_ = v_reuseFailAlloc_1910_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1909_;
            }
            8 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(
    mut v_i_1920_: *mut crate::leanh::LeanObject,
    mut v_as_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u8 = 0;
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: usize = 0;
    let mut v___x_1936_: usize = 0;
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1929_ = lean_array_get_size(v_as_1921_);
                v___x_1930_ = lean_nat_dec_lt(v_i_1920_, v___x_1929_);
                if v___x_1930_ == 0 {
                    crate::leanh::lean_dec(v_i_1920_);
                    v___x_1931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1931_, 0, v_as_1921_);
                    return v___x_1931_;
                } else {
                    v_a_1932_ = lean_array_fget_borrowed(v_as_1921_, v_i_1920_);
                    crate::leanh::lean_inc(v_a_1932_);
                    v___x_1933_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(
                        v_a_1932_,
                        v___y_1922_,
                        v___y_1923_,
                        v___y_1924_,
                        v___y_1925_,
                        v___y_1926_,
                        v___y_1927_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                        v_a_1934_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                        crate::leanh::lean_inc(v_a_1934_);
                        crate::leanh::lean_dec_ref_known(v___x_1933_, 1);
                        v___x_1935_ = lean_ptr_addr(v_a_1932_);
                        v___x_1936_ = lean_ptr_addr(v_a_1934_);
                        v___x_1937_ = lean_usize_dec_eq(v___x_1935_, v___x_1936_);
                        if v___x_1937_ == 0 {
                            v___x_1938_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1939_ = lean_nat_add(v_i_1920_, v___x_1938_);
                            v___x_1940_ = lean_array_fset(v_as_1921_, v_i_1920_, v_a_1934_);
                            crate::leanh::lean_dec(v_i_1920_);
                            v_i_1920_ = v___x_1939_;
                            v_as_1921_ = v___x_1940_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1934_);
                            v___x_1942_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1943_ = lean_nat_add(v_i_1920_, v___x_1942_);
                            crate::leanh::lean_dec(v_i_1920_);
                            v_i_1920_ = v___x_1943_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_1921_);
                        crate::leanh::lean_dec(v_i_1920_);
                        v_a_1945_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                        v_isSharedCheck_1952_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                        if v_isSharedCheck_1952_ == 0 {
                            v___x_1947_ = v___x_1933_;
                            v_isShared_1948_ = v_isSharedCheck_1952_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1945_);
                            crate::leanh::lean_dec(v___x_1933_);
                            v___x_1947_ = crate::leanh::lean_box(0);
                            v_isShared_1948_ = v_isSharedCheck_1952_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___lam__1(
    mut v___x_1953_: *mut crate::leanh::LeanObject,
    mut v_alts_1954_: *mut crate::leanh::LeanObject,
    mut v_typeName_1955_: *mut crate::leanh::LeanObject,
    mut v_resultType_1956_: *mut crate::leanh::LeanObject,
    mut v_discr_1957_: *mut crate::leanh::LeanObject,
    mut v_code_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1970_: u8 = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_alts_1954_);
                v___x_1966_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v___x_1953_, v_alts_1954_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
                if crate::leanh::lean_obj_tag(v___x_1966_) == 0 {
                    v_a_1967_ = crate::leanh::lean_ctor_get(v___x_1966_, 0);
                    v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v___x_1966_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1969_ = v___x_1966_;
                        v_isShared_1970_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1967_);
                        crate::leanh::lean_dec(v___x_1966_);
                        v___x_1969_ = crate::leanh::lean_box(0);
                        v_isShared_1970_ = v_isSharedCheck_1982_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_1958_);
                    crate::leanh::lean_dec(v_discr_1957_);
                    crate::leanh::lean_dec_ref(v_resultType_1956_);
                    crate::leanh::lean_dec(v_typeName_1955_);
                    crate::leanh::lean_dec_ref(v_alts_1954_);
                    v_a_1983_ = crate::leanh::lean_ctor_get(v___x_1966_, 0);
                    v_isSharedCheck_1990_ = (!crate::leanh::lean_is_exclusive(v___x_1966_)) as u8;
                    if v_isSharedCheck_1990_ == 0 {
                        v___x_1985_ = v___x_1966_;
                        v_isShared_1986_ = v_isSharedCheck_1990_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1983_);
                        crate::leanh::lean_dec(v___x_1966_);
                        v___x_1985_ = crate::leanh::lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_1990_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1971_ = lean_ptr_addr(v_alts_1954_);
                crate::leanh::lean_dec_ref(v_alts_1954_);
                v___x_1972_ = lean_ptr_addr(v_a_1967_);
                v___x_1973_ = lean_usize_dec_eq(v___x_1971_, v___x_1972_);
                if v___x_1973_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_1958_);
                    v___x_1974_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1974_, 0, v_typeName_1955_);
                    crate::leanh::lean_ctor_set(v___x_1974_, 1, v_resultType_1956_);
                    crate::leanh::lean_ctor_set(v___x_1974_, 2, v_discr_1957_);
                    crate::leanh::lean_ctor_set(v___x_1974_, 3, v_a_1967_);
                    v___x_1975_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1975_, 0, v___x_1974_);
                    if v_isShared_1970_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1969_, 0, v___x_1975_);
                        v___x_1977_ = v___x_1969_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1978_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
                        v___x_1977_ = v_reuseFailAlloc_1978_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1967_);
                    crate::leanh::lean_dec(v_discr_1957_);
                    crate::leanh::lean_dec_ref(v_resultType_1956_);
                    crate::leanh::lean_dec(v_typeName_1955_);
                    if v_isShared_1970_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1969_, 0, v_code_1958_);
                        v___x_1980_ = v___x_1969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_code_1958_);
                        v___x_1980_ = v_reuseFailAlloc_1981_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1977_;
            }
            3 => {
                return v___x_1980_;
            }
            4 => {
                if v_isShared_1986_ == 0 {
                    v___x_1988_ = v___x_1985_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3___boxed(
    mut v_i_1991_: *mut crate::leanh::LeanObject,
    mut v_as_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_PullLetDecls_pullDecls_spec__3(v_i_1991_, v_as_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
    crate::leanh::lean_dec(v___y_1998_);
    crate::leanh::lean_dec_ref(v___y_1997_);
    crate::leanh::lean_dec(v___y_1996_);
    crate::leanh::lean_dec_ref(v___y_1995_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    return v_res_2000_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullDecls___boxed(
    mut v_code_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_Compiler_LCNF_PullLetDecls_pullDecls(
        v_code_2001_,
        v_a_2002_,
        v_a_2003_,
        v_a_2004_,
        v_a_2005_,
        v_a_2006_,
        v_a_2007_,
    );
    crate::leanh::lean_dec(v_a_2007_);
    crate::leanh::lean_dec_ref(v_a_2006_);
    crate::leanh::lean_dec(v_a_2005_);
    crate::leanh::lean_dec_ref(v_a_2004_);
    crate::leanh::lean_dec(v_a_2003_);
    crate::leanh::lean_dec_ref(v_a_2002_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_pullAlt___boxed(
    mut v_alt_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
    mut v_a_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lean_Compiler_LCNF_PullLetDecls_pullAlt(
        v_alt_2010_,
        v_a_2011_,
        v_a_2012_,
        v_a_2013_,
        v_a_2014_,
        v_a_2015_,
        v_a_2016_,
    );
    crate::leanh::lean_dec(v_a_2016_);
    crate::leanh::lean_dec_ref(v_a_2015_);
    crate::leanh::lean_dec(v_a_2014_);
    crate::leanh::lean_dec_ref(v_a_2013_);
    crate::leanh::lean_dec(v_a_2012_);
    crate::leanh::lean_dec_ref(v_a_2011_);
    return v_res_2018_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(
    mut v_x_2019_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2026_ = l_Lean_Compiler_LCNF_PullLetDecls_withCheckpoint___closed__0;
                v___x_2027_ = lean_st_mk_ref(v___x_2026_);
                v___x_2028_ = crate::leanh::lean_box(1);
                v___x_2029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2029_, 0, v_isCandidateFn_2020_);
                crate::leanh::lean_ctor_set(v___x_2029_, 1, v___x_2028_);
                crate::leanh::lean_inc(v_a_2024_);
                crate::leanh::lean_inc_ref(v_a_2023_);
                crate::leanh::lean_inc(v_a_2022_);
                crate::leanh::lean_inc_ref(v_a_2021_);
                crate::leanh::lean_inc(v___x_2027_);
                v___x_2030_ = crate::leanh::lean_apply_7(
                    v_x_2019_,
                    v___x_2029_,
                    v___x_2027_,
                    v_a_2021_,
                    v_a_2022_,
                    v_a_2023_,
                    v_a_2024_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2030_) == 0 {
                    v_a_2031_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                    v_isSharedCheck_2039_ = (!crate::leanh::lean_is_exclusive(v___x_2030_)) as u8;
                    if v_isSharedCheck_2039_ == 0 {
                        v___x_2033_ = v___x_2030_;
                        v_isShared_2034_ = v_isSharedCheck_2039_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2031_);
                        crate::leanh::lean_dec(v___x_2030_);
                        v___x_2033_ = crate::leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2039_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2027_);
                    return v___x_2030_;
                }
            }
            1 => {
                v___x_2035_ = lean_st_ref_get(v___x_2027_);
                crate::leanh::lean_dec(v___x_2027_);
                crate::leanh::lean_dec(v___x_2035_);
                if v_isShared_2034_ == 0 {
                    v___x_2037_ = v___x_2033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2031_);
                    v___x_2037_ = v_reuseFailAlloc_2038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg___boxed(
    mut v_x_2040_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(
        v_x_2040_,
        v_isCandidateFn_2041_,
        v_a_2042_,
        v_a_2043_,
        v_a_2044_,
        v_a_2045_,
    );
    crate::leanh::lean_dec(v_a_2045_);
    crate::leanh::lean_dec_ref(v_a_2044_);
    crate::leanh::lean_dec(v_a_2043_);
    crate::leanh::lean_dec_ref(v_a_2042_);
    return v_res_2047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(
    mut v_00_u03b1_2048_: *mut crate::leanh::LeanObject,
    mut v_x_2049_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
    mut v_a_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(
        v_x_2049_,
        v_isCandidateFn_2050_,
        v_a_2051_,
        v_a_2052_,
        v_a_2053_,
        v_a_2054_,
    );
    return v___x_2056_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___boxed(
    mut v_00_u03b1_2057_: *mut crate::leanh::LeanObject,
    mut v_x_2058_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2065_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run(
        v_00_u03b1_2057_,
        v_x_2058_,
        v_isCandidateFn_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
    );
    crate::leanh::lean_dec(v_a_2063_);
    crate::leanh::lean_dec_ref(v_a_2062_);
    crate::leanh::lean_dec(v_a_2061_);
    crate::leanh::lean_dec_ref(v_a_2060_);
    return v_res_2065_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(
    mut v_f_2066_: *mut crate::leanh::LeanObject,
    mut v_v_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_a_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2067_) == 0 {
                    v_code_2075_ = crate::leanh::lean_ctor_get(v_v_2067_, 0);
                    v_isSharedCheck_2099_ = (!crate::leanh::lean_is_exclusive(v_v_2067_)) as u8;
                    if v_isSharedCheck_2099_ == 0 {
                        v___x_2077_ = v_v_2067_;
                        v_isShared_2078_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_2075_);
                        crate::leanh::lean_dec(v_v_2067_);
                        v___x_2077_ = crate::leanh::lean_box(0);
                        v_isShared_2078_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2066_);
                    v___x_2100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2100_, 0, v_v_2067_);
                    return v___x_2100_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2073_);
                crate::leanh::lean_inc_ref(v___y_2072_);
                crate::leanh::lean_inc(v___y_2071_);
                crate::leanh::lean_inc_ref(v___y_2070_);
                crate::leanh::lean_inc(v___y_2069_);
                crate::leanh::lean_inc_ref(v___y_2068_);
                v___x_2079_ = crate::leanh::lean_apply_8(
                    v_f_2066_,
                    v_code_2075_,
                    v___y_2068_,
                    v___y_2069_,
                    v___y_2070_,
                    v___y_2071_,
                    v___y_2072_,
                    v___y_2073_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2079_) == 0 {
                    v_a_2080_ = crate::leanh::lean_ctor_get(v___x_2079_, 0);
                    v_isSharedCheck_2090_ = (!crate::leanh::lean_is_exclusive(v___x_2079_)) as u8;
                    if v_isSharedCheck_2090_ == 0 {
                        v___x_2082_ = v___x_2079_;
                        v_isShared_2083_ = v_isSharedCheck_2090_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2080_);
                        crate::leanh::lean_dec(v___x_2079_);
                        v___x_2082_ = crate::leanh::lean_box(0);
                        v_isShared_2083_ = v_isSharedCheck_2090_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2077_);
                    v_a_2091_ = crate::leanh::lean_ctor_get(v___x_2079_, 0);
                    v_isSharedCheck_2098_ = (!crate::leanh::lean_is_exclusive(v___x_2079_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_2093_ = v___x_2079_;
                        v_isShared_2094_ = v_isSharedCheck_2098_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2091_);
                        crate::leanh::lean_dec(v___x_2079_);
                        v___x_2093_ = crate::leanh::lean_box(0);
                        v_isShared_2094_ = v_isSharedCheck_2098_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2077_, 0, v_a_2080_);
                    v___x_2085_ = v___x_2077_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2080_);
                    v___x_2085_ = v_reuseFailAlloc_2089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2085_);
                    v___x_2087_ = v___x_2082_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2087_;
            }
            5 => {
                if v_isShared_2094_ == 0 {
                    v___x_2096_ = v___x_2093_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
                    v___x_2096_ = v_reuseFailAlloc_2097_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg___boxed(
    mut v_f_2101_: *mut crate::leanh::LeanObject,
    mut v_v_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2110_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_2101_, v_v_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
    crate::leanh::lean_dec(v___y_2108_);
    crate::leanh::lean_dec_ref(v___y_2107_);
    crate::leanh::lean_dec(v___y_2106_);
    crate::leanh::lean_dec_ref(v___y_2105_);
    crate::leanh::lean_dec(v___y_2104_);
    crate::leanh::lean_dec_ref(v___y_2103_);
    return v_res_2110_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(
    mut v_pu_2111_: u8,
    mut v_f_2112_: *mut crate::leanh::LeanObject,
    mut v_v_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v_f_2112_, v_v_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
    return v___x_2121_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___boxed(
    mut v_pu_2122_: *mut crate::leanh::LeanObject,
    mut v_f_2123_: *mut crate::leanh::LeanObject,
    mut v_v_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2132_: u8 = 0;
    let mut v_res_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2132_ = (crate::leanh::lean_unbox(v_pu_2122_) as u8);
    v_res_2133_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0(v_pu_boxed_2132_, v_f_2123_, v_v_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
    crate::leanh::lean_dec(v___y_2130_);
    crate::leanh::lean_dec_ref(v___y_2129_);
    crate::leanh::lean_dec(v___y_2128_);
    crate::leanh::lean_dec_ref(v___y_2127_);
    crate::leanh::lean_dec(v___y_2126_);
    crate::leanh::lean_dec_ref(v___y_2125_);
    return v_res_2133_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(
    mut v___x_2135_: *mut crate::leanh::LeanObject,
    mut v_value_2136_: *mut crate::leanh::LeanObject,
    mut v_toSignature_2137_: *mut crate::leanh::LeanObject,
    mut v_recursive_2138_: u8,
    mut v_inlineAttr_x3f_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2147_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_2135_, v_value_2136_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
                if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                    v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                    crate::leanh::lean_inc(v_a_2148_);
                    crate::leanh::lean_dec_ref_known(v___x_2147_, 1);
                    v___x_2149_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___closed__0;
                    v___x_2150_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_pullLetDecls_spec__0___redArg(v___x_2149_, v_a_2148_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
                    if crate::leanh::lean_obj_tag(v___x_2150_) == 0 {
                        v_a_2151_ = crate::leanh::lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2159_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2159_ == 0 {
                            v___x_2153_ = v___x_2150_;
                            v_isShared_2154_ = v_isSharedCheck_2159_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2151_);
                            crate::leanh::lean_dec(v___x_2150_);
                            v___x_2153_ = crate::leanh::lean_box(0);
                            v_isShared_2154_ = v_isSharedCheck_2159_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_inlineAttr_x3f_2139_);
                        crate::leanh::lean_dec_ref(v_toSignature_2137_);
                        v_a_2160_ = crate::leanh::lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2167_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2167_ == 0 {
                            v___x_2162_ = v___x_2150_;
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2160_);
                            crate::leanh::lean_dec(v___x_2150_);
                            v___x_2162_ = crate::leanh::lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2167_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_inlineAttr_x3f_2139_);
                    crate::leanh::lean_dec_ref(v_toSignature_2137_);
                    v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                    v_isSharedCheck_2175_ = (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2170_ = v___x_2147_;
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2168_);
                        crate::leanh::lean_dec(v___x_2147_);
                        v___x_2170_ = crate::leanh::lean_box(0);
                        v_isShared_2171_ = v_isSharedCheck_2175_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v_toSignature_2137_);
                crate::leanh::lean_ctor_set(v___x_2155_, 1, v_a_2151_);
                crate::leanh::lean_ctor_set(v___x_2155_, 2, v_inlineAttr_x3f_2139_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2155_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_recursive_2138_,
                );
                if v_isShared_2154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2155_);
                    v___x_2157_ = v___x_2153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
                    v___x_2157_ = v_reuseFailAlloc_2158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2157_;
            }
            3 => {
                if v_isShared_2163_ == 0 {
                    v___x_2165_ = v___x_2162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
                    v___x_2165_ = v_reuseFailAlloc_2166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2165_;
            }
            5 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed(
    mut v___x_2176_: *mut crate::leanh::LeanObject,
    mut v_value_2177_: *mut crate::leanh::LeanObject,
    mut v_toSignature_2178_: *mut crate::leanh::LeanObject,
    mut v_recursive_2179_: *mut crate::leanh::LeanObject,
    mut v_inlineAttr_x3f_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recursive_boxed_2188_: u8 = 0;
    let mut v_res_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_recursive_boxed_2188_ = (crate::leanh::lean_unbox(v_recursive_2179_) as u8);
    v_res_2189_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0(
        v___x_2176_,
        v_value_2177_,
        v_toSignature_2178_,
        v_recursive_boxed_2188_,
        v_inlineAttr_x3f_2180_,
        v___y_2181_,
        v___y_2182_,
        v___y_2183_,
        v___y_2184_,
        v___y_2185_,
        v___y_2186_,
    );
    crate::leanh::lean_dec(v___y_2186_);
    crate::leanh::lean_dec_ref(v___y_2185_);
    crate::leanh::lean_dec(v___y_2184_);
    crate::leanh::lean_dec_ref(v___y_2183_);
    crate::leanh::lean_dec(v___y_2182_);
    crate::leanh::lean_dec_ref(v___y_2181_);
    return v_res_2189_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(
    mut v_params_2190_: *mut crate::leanh::LeanObject,
    mut v___f_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isCandidateFn_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_included_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2209_: u8 = 0;
    let mut v___x_2210_: usize = 0;
    let mut v___x_2211_: usize = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_unused_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isCandidateFn_2199_ = crate::leanh::lean_ctor_get(v___y_2192_, 0);
                v_included_2200_ = crate::leanh::lean_ctor_get(v___y_2192_, 1);
                v___x_2201_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2202_ = lean_array_get_size(v_params_2190_);
                v___x_2203_ = lean_nat_dec_lt(v___x_2201_, v___x_2202_);
                if v___x_2203_ == 0 {
                    v___x_2204_ = crate::leanh::lean_apply_7(
                        v___f_2191_,
                        v___y_2192_,
                        v___y_2193_,
                        v___y_2194_,
                        v___y_2195_,
                        v___y_2196_,
                        v___y_2197_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2204_;
                } else {
                    v___x_2205_ = lean_nat_dec_le(v___x_2202_, v___x_2202_);
                    if v___x_2205_ == 0 {
                        if v___x_2203_ == 0 {
                            v___x_2206_ = crate::leanh::lean_apply_7(
                                v___f_2191_,
                                v___y_2192_,
                                v___y_2193_,
                                v___y_2194_,
                                v___y_2195_,
                                v___y_2196_,
                                v___y_2197_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2206_;
                        } else {
                            crate::leanh::lean_inc(v_included_2200_);
                            crate::leanh::lean_inc_ref(v_isCandidateFn_2199_);
                            v_isSharedCheck_2217_ =
                                (!crate::leanh::lean_is_exclusive(v___y_2192_)) as u8;
                            if v_isSharedCheck_2217_ == 0 {
                                v_unused_2218_ = crate::leanh::lean_ctor_get(v___y_2192_, 1);
                                crate::leanh::lean_dec(v_unused_2218_);
                                v_unused_2219_ = crate::leanh::lean_ctor_get(v___y_2192_, 0);
                                crate::leanh::lean_dec(v_unused_2219_);
                                v___x_2208_ = v___y_2192_;
                                v_isShared_2209_ = v_isSharedCheck_2217_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_2192_);
                                v___x_2208_ = crate::leanh::lean_box(0);
                                v_isShared_2209_ = v_isSharedCheck_2217_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc(v_included_2200_);
                        crate::leanh::lean_inc_ref(v_isCandidateFn_2199_);
                        v_isSharedCheck_2230_ =
                            (!crate::leanh::lean_is_exclusive(v___y_2192_)) as u8;
                        if v_isSharedCheck_2230_ == 0 {
                            v_unused_2231_ = crate::leanh::lean_ctor_get(v___y_2192_, 1);
                            crate::leanh::lean_dec(v_unused_2231_);
                            v_unused_2232_ = crate::leanh::lean_ctor_get(v___y_2192_, 0);
                            crate::leanh::lean_dec(v_unused_2232_);
                            v___x_2221_ = v___y_2192_;
                            v_isShared_2222_ = v_isSharedCheck_2230_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_2192_);
                            v___x_2221_ = crate::leanh::lean_box(0);
                            v_isShared_2222_ = v_isSharedCheck_2230_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2210_ = 0usize;
                v___x_2211_ = lean_usize_of_nat(v___x_2202_);
                v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_2190_, v___x_2210_, v___x_2211_, v_included_2200_);
                if v_isShared_2209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2212_);
                    v___x_2214_ = v___x_2208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_isCandidateFn_2199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2212_);
                    v___x_2214_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2215_ = crate::leanh::lean_apply_7(
                    v___f_2191_,
                    v___x_2214_,
                    v___y_2193_,
                    v___y_2194_,
                    v___y_2195_,
                    v___y_2196_,
                    v___y_2197_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2215_;
            }
            3 => {
                v___x_2223_ = 0usize;
                v___x_2224_ = lean_usize_of_nat(v___x_2202_);
                v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_PullLetDecls_pullAlt_spec__0(v_params_2190_, v___x_2223_, v___x_2224_, v_included_2200_);
                if v_isShared_2222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2221_, 1, v___x_2225_);
                    v___x_2227_ = v___x_2221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_isCandidateFn_2199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2225_);
                    v___x_2227_ = v_reuseFailAlloc_2229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2228_ = crate::leanh::lean_apply_7(
                    v___f_2191_,
                    v___x_2227_,
                    v___y_2193_,
                    v___y_2194_,
                    v___y_2195_,
                    v___y_2196_,
                    v___y_2197_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed(
    mut v_params_2233_: *mut crate::leanh::LeanObject,
    mut v___f_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2242_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1(
        v_params_2233_,
        v___f_2234_,
        v___y_2235_,
        v___y_2236_,
        v___y_2237_,
        v___y_2238_,
        v___y_2239_,
        v___y_2240_,
    );
    crate::leanh::lean_dec_ref(v_params_2233_);
    return v_res_2242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls(
    mut v_decl_2244_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2253_: u8 = 0;
    let mut v_inlineAttr_x3f_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_2251_ = crate::leanh::lean_ctor_get(v_decl_2244_, 0);
    crate::leanh::lean_inc_ref(v_toSignature_2251_);
    v_value_2252_ = crate::leanh::lean_ctor_get(v_decl_2244_, 1);
    crate::leanh::lean_inc_ref(v_value_2252_);
    v_recursive_2253_ = crate::leanh::lean_ctor_get_uint8(
        v_decl_2244_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_inlineAttr_x3f_2254_ = crate::leanh::lean_ctor_get(v_decl_2244_, 2);
    crate::leanh::lean_inc(v_inlineAttr_x3f_2254_);
    crate::leanh::lean_dec_ref(v_decl_2244_);
    v_params_2255_ = crate::leanh::lean_ctor_get(v_toSignature_2251_, 3);
    crate::leanh::lean_inc_ref(v_params_2255_);
    v___x_2256_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls___closed__0;
    v___x_2257_ = crate::leanh::lean_box((v_recursive_2253_) as usize);
    v___f_2258_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__0___boxed as *mut core::ffi::c_void,
        12,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2258_, 0, v___x_2256_);
    crate::leanh::lean_closure_set(v___f_2258_, 1, v_value_2252_);
    crate::leanh::lean_closure_set(v___f_2258_, 2, v_toSignature_2251_);
    crate::leanh::lean_closure_set(v___f_2258_, 3, v___x_2257_);
    crate::leanh::lean_closure_set(v___f_2258_, 4, v_inlineAttr_x3f_2254_);
    v___f_2259_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_Decl_pullLetDecls___lam__1___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2259_, 0, v_params_2255_);
    crate::leanh::lean_closure_set(v___f_2259_, 1, v___f_2258_);
    v___x_2260_ = l_Lean_Compiler_LCNF_PullLetDecls_PullM_run___redArg(
        v___f_2259_,
        v_isCandidateFn_2245_,
        v_a_2246_,
        v_a_2247_,
        v_a_2248_,
        v_a_2249_,
    );
    return v___x_2260_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullLetDecls___boxed(
    mut v_decl_2261_: *mut crate::leanh::LeanObject,
    mut v_isCandidateFn_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(
        v_decl_2261_,
        v_isCandidateFn_2262_,
        v_a_2263_,
        v_a_2264_,
        v_a_2265_,
        v_a_2266_,
    );
    crate::leanh::lean_dec(v_a_2266_);
    crate::leanh::lean_dec_ref(v_a_2265_);
    crate::leanh::lean_dec(v_a_2264_);
    crate::leanh::lean_dec_ref(v_a_2263_);
    return v_res_2268_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(
    mut v_k_2269_: *mut crate::leanh::LeanObject,
    mut v_t_2270_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2270_) == 0 {
                    v_k_2271_ = crate::leanh::lean_ctor_get(v_t_2270_, 1);
                    v_l_2272_ = crate::leanh::lean_ctor_get(v_t_2270_, 3);
                    v_r_2273_ = crate::leanh::lean_ctor_get(v_t_2270_, 4);
                    v___x_2274_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2269_, v_k_2271_);
                    match v___x_2274_ {
                        0 => {
                            v_t_2270_ = v_l_2272_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2276_ = 1;
                            return v___x_2276_;
                        }
                        _ => {
                            v_t_2270_ = v_r_2273_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2278_ = 0;
                    return v___x_2278_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg___boxed(
    mut v_k_2279_: *mut crate::leanh::LeanObject,
    mut v_t_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2281_: u8 = 0;
    let mut v_r_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2281_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_2279_, v_t_2280_);
    crate::leanh::lean_dec(v_t_2280_);
    crate::leanh::lean_dec(v_k_2279_);
    v_r_2282_ = crate::leanh::lean_box((v_res_2281_) as usize);
    return v_r_2282_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(
    mut v_as_2283_: *mut crate::leanh::LeanObject,
    mut v_i_2284_: usize,
    mut v_stop_2285_: usize,
) -> u8 {
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: u8 = 0;
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2286_ = lean_usize_dec_eq(v_i_2284_, v_stop_2285_);
                if v___x_2286_ == 0 {
                    v___x_2287_ = lean_array_uget_borrowed(v_as_2283_, v_i_2284_);
                    v___x_2288_ = crate::leanh::lean_box(0);
                    v___x_2289_ =
                        l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_2287_, v___x_2288_);
                    if v___x_2289_ == 0 {
                        v___x_2290_ = 1usize;
                        v___x_2291_ = lean_usize_add(v_i_2284_, v___x_2290_);
                        v_i_2284_ = v___x_2291_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2289_;
                    }
                } else {
                    v___x_2293_ = 0;
                    return v___x_2293_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1___boxed(
    mut v_as_2294_: *mut crate::leanh::LeanObject,
    mut v_i_2295_: *mut crate::leanh::LeanObject,
    mut v_stop_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2297_: usize = 0;
    let mut v_stop_boxed_2298_: usize = 0;
    let mut v_res_2299_: u8 = 0;
    let mut v_r_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2297_ = crate::leanh::lean_unbox_usize(v_i_2295_);
    crate::leanh::lean_dec(v_i_2295_);
    v_stop_boxed_2298_ = crate::leanh::lean_unbox_usize(v_stop_2296_);
    crate::leanh::lean_dec(v_stop_2296_);
    v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_as_2294_, v_i_boxed_2297_, v_stop_boxed_2298_);
    crate::leanh::lean_dec_ref(v_as_2294_);
    v_r_2300_ = crate::leanh::lean_box((v_res_2299_) as usize);
    return v_r_2300_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(
    mut v_letDecl_2301_: *mut crate::leanh::LeanObject,
    mut v_candidates_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v_struct_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_a_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v___y_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: usize = 0;
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u8 = 0;
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: usize = 0;
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_2308_ = crate::leanh::lean_ctor_get(v_letDecl_2301_, 2);
                v_value_2309_ = crate::leanh::lean_ctor_get(v_letDecl_2301_, 3);
                if crate::leanh::lean_obj_tag(v_value_2309_) == 3 {
                    v_args_2354_ = crate::leanh::lean_ctor_get(v_value_2309_, 2);
                    v___x_2355_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2356_ = lean_array_get_size(v_args_2354_);
                    v___x_2357_ = lean_nat_dec_lt(v___x_2355_, v___x_2356_);
                    if v___x_2357_ == 0 {
                        v___y_2343_ = v___y_2306_;
                        state = 8;
                        continue;
                    } else {
                        if v___x_2357_ == 0 {
                            v___y_2343_ = v___y_2306_;
                            state = 8;
                            continue;
                        } else {
                            v___x_2358_ = 0usize;
                            v___x_2359_ = lean_usize_of_nat(v___x_2356_);
                            v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_2354_, v___x_2358_, v___x_2359_);
                            if v___x_2360_ == 0 {
                                v___y_2343_ = v___y_2306_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2361_ = 0;
                                v___x_2362_ = crate::leanh::lean_box((v___x_2361_) as usize);
                                v___x_2363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2363_, 0, v___x_2362_);
                                return v___x_2363_;
                            }
                        }
                    }
                } else {
                    v___y_2343_ = v___y_2306_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_2312_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_type_2308_, v___y_2311_);
                if crate::leanh::lean_obj_tag(v___x_2312_) == 0 {
                    v_a_2313_ = crate::leanh::lean_ctor_get(v___x_2312_, 0);
                    v_isSharedCheck_2333_ = (!crate::leanh::lean_is_exclusive(v___x_2312_)) as u8;
                    if v_isSharedCheck_2333_ == 0 {
                        v___x_2315_ = v___x_2312_;
                        v_isShared_2316_ = v_isSharedCheck_2333_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2313_);
                        crate::leanh::lean_dec(v___x_2312_);
                        v___x_2315_ = crate::leanh::lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2333_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2334_ = crate::leanh::lean_ctor_get(v___x_2312_, 0);
                    v_isSharedCheck_2341_ = (!crate::leanh::lean_is_exclusive(v___x_2312_)) as u8;
                    if v_isSharedCheck_2341_ == 0 {
                        v___x_2336_ = v___x_2312_;
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2334_);
                        crate::leanh::lean_dec(v___x_2312_);
                        v___x_2336_ = crate::leanh::lean_box(0);
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2313_) == 0 {
                    if crate::leanh::lean_obj_tag(v_value_2309_) == 2 {
                        v_struct_2317_ = crate::leanh::lean_ctor_get(v_value_2309_, 2);
                        v___x_2318_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_struct_2317_, v_candidates_2302_);
                        v___x_2319_ = crate::leanh::lean_box((v___x_2318_) as usize);
                        if v_isShared_2316_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2319_);
                            v___x_2321_ = v___x_2315_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2322_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
                            v___x_2321_ = v_reuseFailAlloc_2322_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2323_ = 0;
                        v___x_2324_ = crate::leanh::lean_box((v___x_2323_) as usize);
                        if v_isShared_2316_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2324_);
                            v___x_2326_ = v___x_2315_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2327_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
                            v___x_2326_ = v_reuseFailAlloc_2327_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_2313_, 1);
                    v___x_2328_ = 1;
                    v___x_2329_ = crate::leanh::lean_box((v___x_2328_) as usize);
                    if v_isShared_2316_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2329_);
                        v___x_2331_ = v___x_2315_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
                        v___x_2331_ = v_reuseFailAlloc_2332_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2321_;
            }
            4 => {
                return v___x_2326_;
            }
            5 => {
                return v___x_2331_;
            }
            6 => {
                if v_isShared_2337_ == 0 {
                    v___x_2339_ = v___x_2336_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2339_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_value_2309_) == 4 {
                    v_args_2344_ = crate::leanh::lean_ctor_get(v_value_2309_, 1);
                    v___x_2345_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2346_ = lean_array_get_size(v_args_2344_);
                    v___x_2347_ = lean_nat_dec_lt(v___x_2345_, v___x_2346_);
                    if v___x_2347_ == 0 {
                        v___y_2311_ = v___y_2343_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_2347_ == 0 {
                            v___y_2311_ = v___y_2343_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2348_ = 0usize;
                            v___x_2349_ = lean_usize_of_nat(v___x_2346_);
                            v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__1(v_args_2344_, v___x_2348_, v___x_2349_);
                            if v___x_2350_ == 0 {
                                v___y_2311_ = v___y_2343_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2351_ = 0;
                                v___x_2352_ = crate::leanh::lean_box((v___x_2351_) as usize);
                                v___x_2353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
                                return v___x_2353_;
                            }
                        }
                    }
                } else {
                    v___y_2311_ = v___y_2343_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0___boxed(
    mut v_letDecl_2364_: *mut crate::leanh::LeanObject,
    mut v_candidates_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Lean_Compiler_LCNF_Decl_pullInstances___lam__0(
        v_letDecl_2364_,
        v_candidates_2365_,
        v___y_2366_,
        v___y_2367_,
        v___y_2368_,
        v___y_2369_,
    );
    crate::leanh::lean_dec(v___y_2369_);
    crate::leanh::lean_dec_ref(v___y_2368_);
    crate::leanh::lean_dec(v___y_2367_);
    crate::leanh::lean_dec_ref(v___y_2366_);
    crate::leanh::lean_dec(v_candidates_2365_);
    crate::leanh::lean_dec_ref(v_letDecl_2364_);
    return v_res_2371_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullInstances(
    mut v_decl_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
    mut v_a_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2379_ = l_Lean_Compiler_LCNF_Decl_pullInstances___closed__0;
    v___x_2380_ = l_Lean_Compiler_LCNF_Decl_pullLetDecls(
        v_decl_2373_,
        v___f_2379_,
        v_a_2374_,
        v_a_2375_,
        v_a_2376_,
        v_a_2377_,
    );
    return v___x_2380_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_pullInstances___boxed(
    mut v_decl_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2387_ = l_Lean_Compiler_LCNF_Decl_pullInstances(
        v_decl_2381_,
        v_a_2382_,
        v_a_2383_,
        v_a_2384_,
        v_a_2385_,
    );
    crate::leanh::lean_dec(v_a_2385_);
    crate::leanh::lean_dec_ref(v_a_2384_);
    crate::leanh::lean_dec(v_a_2383_);
    crate::leanh::lean_dec_ref(v_a_2382_);
    return v_res_2387_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(
    mut v_00_u03b2_2388_: *mut crate::leanh::LeanObject,
    mut v_k_2389_: *mut crate::leanh::LeanObject,
    mut v_t_2390_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2391_: u8 = 0;
    v___x_2391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___redArg(v_k_2389_, v_t_2390_);
    return v___x_2391_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0___boxed(
    mut v_00_u03b2_2392_: *mut crate::leanh::LeanObject,
    mut v_k_2393_: *mut crate::leanh::LeanObject,
    mut v_t_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: u8 = 0;
    let mut v_r_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_Decl_pullInstances_spec__0(v_00_u03b2_2392_, v_k_2393_, v_t_2394_);
    crate::leanh::lean_dec(v_t_2394_);
    crate::leanh::lean_dec(v_k_2393_);
    v_r_2396_ = crate::leanh::lean_box((v_res_2395_) as usize);
    return v_r_2396_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullInstances___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2402_ = l_Lean_Compiler_LCNF_pullInstances___closed__2;
    v___x_2403_ = 0;
    v___x_2404_ = l_Lean_Compiler_LCNF_pullInstances___closed__1;
    v___x_2405_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_2404_,
        v___x_2403_,
        v___x_2402_,
        v___x_2401_,
    );
    return v___x_2405_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_pullInstances() -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullInstances___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_pullInstances___closed__3_once),
        _init_l_Lean_Compiler_LCNF_pullInstances___closed__3,
    );
    return v___x_2406_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = crate::leanh::lean_unsigned_to_nat(3825914912);
    v___x_2463_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
    v___x_2464_ = l_Lean_Name_num___override(v___x_2463_, v___x_2462_);
    return v___x_2464_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
    v___x_2467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
    v___x_2468_ = l_Lean_Name_str___override(v___x_2467_, v___x_2466_);
    return v___x_2468_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
    v___x_2471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
    v___x_2472_ = l_Lean_Name_str___override(v___x_2471_, v___x_2470_);
    return v___x_2472_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2474_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
    v___x_2475_ = l_Lean_Name_num___override(v___x_2474_, v___x_2473_);
    return v___x_2475_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_;
    v___x_2478_ = 1;
    v___x_2479_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_);
    v___x_2480_ = l_Lean_registerTraceClass(v___x_2477_, v___x_2478_, v___x_2479_);
    return v___x_2480_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2____boxed(
    mut v_a_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
    return v_res_2482_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_pullInstances = _init_l_Lean_Compiler_LCNF_pullInstances();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstances);
    res = l___private_Lean_Compiler_LCNF_PullLetDecls_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PullLetDecls_3825914912____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PullLetDecls(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PullLetDecls(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
}
