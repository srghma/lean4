// Lean compiler output
// Module: Lean.Compiler.LCNF.CompilerM
// Imports: Lean.Compiler.LCNF.LCtx Lean.Compiler.LCNF.ConfigOptions
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::BasicAux::l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_List_foldl___redArg, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_read___boxed, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::{l_instMonadEIO, l_instMonadEIO___aux__5___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp,
};
use crate::r#gen::Lean::Compiler::LCNF::ConfigOptions::{
    initialize_Lean_Compiler_LCNF_ConfigOptions,
    l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default, l_Lean_Compiler_LCNF_toConfigOptions,
    runtime_initialize_Lean_Compiler_LCNF_ConfigOptions,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::{
    initialize_Lean_Compiler_LCNF_LCtx, l_Lean_Compiler_LCNF_LCtx_addFunDecl,
    l_Lean_Compiler_LCNF_LCtx_addLetDecl, l_Lean_Compiler_LCNF_LCtx_addParam,
    l_Lean_Compiler_LCNF_LCtx_eraseCode, l_Lean_Compiler_LCNF_LCtx_eraseFunDecl,
    l_Lean_Compiler_LCNF_LCtx_eraseLetDecl, l_Lean_Compiler_LCNF_LCtx_eraseParam,
    l_Lean_Compiler_LCNF_LCtx_eraseParams, l_Lean_Compiler_LCNF_LCtx_toLocalContext,
    runtime_initialize_Lean_Compiler_LCNF_LCtx,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_erasedExpr;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_insert___redArg,
    l_Lean_PersistentHashMap_instInhabited, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_find_x3f,
    l_Lean_instInhabitedEnvExtension_default, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_hasFVar, l_Lean_Expr_headBeta, l_Lean_Expr_lam___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insert___redArg;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPhase_default: u8 = 0;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPhase: u8 = 0;
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instMonadCompilerM: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_getType___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97,
            98, 108, 101, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_getType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getType___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getParam___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_getParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getParam___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getLetDecl___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
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
            117, 110, 107, 110, 111, 119, 110, 32, 108, 101, 116, 45, 100, 101, 99, 108, 97, 114,
            97, 116, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getLetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getFunDecl___closed__0_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 108, 111, 99, 97, 108, 32, 102, 117, 110, 99,
            116, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getFunDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 109, 112, 105, 108, 101, 114, 77, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 110, 111, 114, 109, 69, 120, 112, 114, 73, 109, 112, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 109, 112, 105, 108, 101, 114, 77, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value:
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
    m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_addSubst___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value:
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
    m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_addSubst___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkParam___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [95, 121, 0],
    };
static mut l_Lean_Compiler_LCNF_mkParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkParam___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6531178163111358628 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_mkParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [95, 120, 0],
    };
static mut l_Lean_Compiler_LCNF_mkLetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7699194985028780469 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_mkLetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [95, 102, 0],
    };
static mut l_Lean_Compiler_LCNF_mkFunDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12317437071847932413 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_mkFunDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [95, 106, 112, 0],
};
static mut l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12958253247387092313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value:
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
        76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116,
        72, 97, 115, 104, 77, 97, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104,
        77, 97, 112, 46, 102, 105, 110, 100, 33, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109,
        97, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorIdx(
    mut v_x_4914_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_4914_ {
        0 => {
            let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4915_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4915_;
        }
        1 => {
            let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4916_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4916_;
        }
        _ => {
            let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4917_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4917_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(
    mut v_x_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_4919_: u8 = 0;
    let mut v_res_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4919_ = (crate::leanh::lean_unbox(v_x_4918_) as u8);
    v_res_4920_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_boxed_4919_);
    return v_res_4920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toCtorIdx(
    mut v_x_4921_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_4921_);
    return v___x_4922_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(
    mut v_x_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_4924_: u8 = 0;
    let mut v_res_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4924_ = (crate::leanh::lean_unbox(v_x_4923_) as u8);
    v_res_4925_ = l_Lean_Compiler_LCNF_Phase_toCtorIdx(v_x_4__boxed_4924_);
    return v_res_4925_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(
    mut v_k_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4926_);
    return v_k_4926_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(
    mut v_k_4927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_4927_);
    crate::leanh::lean_dec(v_k_4927_);
    return v_res_4928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim(
    mut v_motive_4929_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4930_: *mut crate::leanh::LeanObject,
    mut v_t_4931_: u8,
    mut v_h_4932_: *mut crate::leanh::LeanObject,
    mut v_k_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_4933_);
    return v_k_4933_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(
    mut v_motive_4934_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4935_: *mut crate::leanh::LeanObject,
    mut v_t_4936_: *mut crate::leanh::LeanObject,
    mut v_h_4937_: *mut crate::leanh::LeanObject,
    mut v_k_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4939_: u8 = 0;
    let mut v_res_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4939_ = (crate::leanh::lean_unbox(v_t_4936_) as u8);
    v_res_4940_ = l_Lean_Compiler_LCNF_Phase_ctorElim(
        v_motive_4934_,
        v_ctorIdx_4935_,
        v_t_boxed_4939_,
        v_h_4937_,
        v_k_4938_,
    );
    crate::leanh::lean_dec(v_k_4938_);
    crate::leanh::lean_dec(v_ctorIdx_4935_);
    return v_res_4940_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___redArg(
    mut v_base_4941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_base_4941_);
    return v_base_4941_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(
    mut v_base_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_4942_);
    crate::leanh::lean_dec(v_base_4942_);
    return v_res_4943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim(
    mut v_motive_4944_: *mut crate::leanh::LeanObject,
    mut v_t_4945_: u8,
    mut v_h_4946_: *mut crate::leanh::LeanObject,
    mut v_base_4947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_base_4947_);
    return v_base_4947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___boxed(
    mut v_motive_4948_: *mut crate::leanh::LeanObject,
    mut v_t_4949_: *mut crate::leanh::LeanObject,
    mut v_h_4950_: *mut crate::leanh::LeanObject,
    mut v_base_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4952_: u8 = 0;
    let mut v_res_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4952_ = (crate::leanh::lean_unbox(v_t_4949_) as u8);
    v_res_4953_ = l_Lean_Compiler_LCNF_Phase_base_elim(
        v_motive_4948_,
        v_t_boxed_4952_,
        v_h_4950_,
        v_base_4951_,
    );
    crate::leanh::lean_dec(v_base_4951_);
    return v_res_4953_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(
    mut v_mono_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mono_4954_);
    return v_mono_4954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(
    mut v_mono_4955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4956_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_4955_);
    crate::leanh::lean_dec(v_mono_4955_);
    return v_res_4956_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim(
    mut v_motive_4957_: *mut crate::leanh::LeanObject,
    mut v_t_4958_: u8,
    mut v_h_4959_: *mut crate::leanh::LeanObject,
    mut v_mono_4960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mono_4960_);
    return v_mono_4960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(
    mut v_motive_4961_: *mut crate::leanh::LeanObject,
    mut v_t_4962_: *mut crate::leanh::LeanObject,
    mut v_h_4963_: *mut crate::leanh::LeanObject,
    mut v_mono_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4965_: u8 = 0;
    let mut v_res_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4965_ = (crate::leanh::lean_unbox(v_t_4962_) as u8);
    v_res_4966_ = l_Lean_Compiler_LCNF_Phase_mono_elim(
        v_motive_4961_,
        v_t_boxed_4965_,
        v_h_4963_,
        v_mono_4964_,
    );
    crate::leanh::lean_dec(v_mono_4964_);
    return v_res_4966_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(
    mut v_impure_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_impure_4967_);
    return v_impure_4967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(
    mut v_impure_4968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4969_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_4968_);
    crate::leanh::lean_dec(v_impure_4968_);
    return v_res_4969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim(
    mut v_motive_4970_: *mut crate::leanh::LeanObject,
    mut v_t_4971_: u8,
    mut v_h_4972_: *mut crate::leanh::LeanObject,
    mut v_impure_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_impure_4973_);
    return v_impure_4973_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(
    mut v_motive_4974_: *mut crate::leanh::LeanObject,
    mut v_t_4975_: *mut crate::leanh::LeanObject,
    mut v_h_4976_: *mut crate::leanh::LeanObject,
    mut v_impure_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_4978_: u8 = 0;
    let mut v_res_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4978_ = (crate::leanh::lean_unbox(v_t_4975_) as u8);
    v_res_4979_ = l_Lean_Compiler_LCNF_Phase_impure_elim(
        v_motive_4974_,
        v_t_boxed_4978_,
        v_h_4976_,
        v_impure_4977_,
    );
    crate::leanh::lean_dec(v_impure_4977_);
    return v_res_4979_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default() -> u8 {
    let mut v___x_4980_: u8 = 0;
    v___x_4980_ = 0;
    return v___x_4980_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedPhase() -> u8 {
    let mut v___x_4981_: u8 = 0;
    v___x_4981_ = 0;
    return v___x_4981_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ofNat(mut v_n_4982_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    v___x_4983_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4984_ = lean_nat_dec_le(v_n_4982_, v___x_4983_);
    if v___x_4984_ == 0 {
        let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4986_: u8 = 0;
        v___x_4985_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4986_ = lean_nat_dec_le(v_n_4982_, v___x_4985_);
        if v___x_4986_ == 0 {
            let mut v___x_4987_: u8 = 0;
            v___x_4987_ = 2;
            return v___x_4987_;
        } else {
            let mut v___x_4988_: u8 = 0;
            v___x_4988_ = 1;
            return v___x_4988_;
        }
    } else {
        let mut v___x_4989_: u8 = 0;
        v___x_4989_ = 0;
        return v___x_4989_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ofNat___boxed(
    mut v_n_4990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4991_: u8 = 0;
    let mut v_r_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4991_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_4990_);
    crate::leanh::lean_dec(v_n_4990_);
    v_r_4992_ = crate::leanh::lean_box((v_res_4991_) as usize);
    return v_r_4992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableEqPhase(
    mut v_x_4993_: u8,
    mut v_y_4994_: u8,
) -> u8 {
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: u8 = 0;
    v___x_4995_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_4993_);
    v___x_4996_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_4994_);
    v___x_4997_ = lean_nat_dec_eq(v___x_4995_, v___x_4996_);
    crate::leanh::lean_dec(v___x_4996_);
    crate::leanh::lean_dec(v___x_4995_);
    return v___x_4997_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(
    mut v_x_4998_: *mut crate::leanh::LeanObject,
    mut v_y_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_5000_: u8 = 0;
    let mut v_y_14__boxed_5001_: u8 = 0;
    let mut v_res_5002_: u8 = 0;
    let mut v_r_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_5000_ = (crate::leanh::lean_unbox(v_x_4998_) as u8);
    v_y_14__boxed_5001_ = (crate::leanh::lean_unbox(v_y_4999_) as u8);
    v_res_5002_ =
        l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_5000_, v_y_14__boxed_5001_);
    v_r_5003_ = crate::leanh::lean_box((v_res_5002_) as usize);
    return v_r_5003_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toPurity(mut v_x_5004_: u8) -> u8 {
    if v_x_5004_ == 2 {
        let mut v___x_5005_: u8 = 0;
        v___x_5005_ = 1;
        return v___x_5005_;
    } else {
        let mut v___x_5006_: u8 = 0;
        v___x_5006_ = 0;
        return v___x_5006_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toPurity___boxed(
    mut v_x_5007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_23__boxed_5008_: u8 = 0;
    let mut v_res_5009_: u8 = 0;
    let mut v_r_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_23__boxed_5008_ = (crate::leanh::lean_unbox(v_x_5007_) as u8);
    v_res_5009_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_5008_);
    v_r_5010_ = crate::leanh::lean_box((v_res_5009_) as usize);
    return v_r_5010_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5011_ = crate::leanh::lean_box(0);
    v___x_5012_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5013_ = lean_mk_array(v___x_5012_, v___x_5011_);
    return v___x_5013_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0,
    );
    v___x_5015_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5016_, 0, v___x_5015_);
    crate::leanh::lean_ctor_set(v___x_5016_, 1, v___x_5014_);
    return v___x_5016_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1,
    );
    v___x_5018_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5018_, 0, v___x_5017_);
    crate::leanh::lean_ctor_set(v___x_5018_, 1, v___x_5017_);
    crate::leanh::lean_ctor_set(v___x_5018_, 2, v___x_5017_);
    crate::leanh::lean_ctor_set(v___x_5018_, 3, v___x_5017_);
    crate::leanh::lean_ctor_set(v___x_5018_, 4, v___x_5017_);
    crate::leanh::lean_ctor_set(v___x_5018_, 5, v___x_5017_);
    return v___x_5018_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5019_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5020_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2,
    );
    v___x_5021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5021_, 0, v___x_5020_);
    crate::leanh::lean_ctor_set(v___x_5021_, 1, v___x_5019_);
    return v___x_5021_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3,
    );
    return v___x_5022_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
    return v___x_5023_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
    v___x_5025_ = 0;
    v___x_5026_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5026_, 0, v___x_5024_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5026_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5025_,
    );
    return v___x_5026_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5027_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0,
    );
    return v___x_5027_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5028_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
    return v___x_5028_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(
    mut v_00_u03b1_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5036_, 0, v___y_5030_);
    return v___x_5036_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(
    mut v_00_u03b1_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(
        v_00_u03b1_5037_,
        v___y_5038_,
        v___y_5039_,
        v___y_5040_,
        v___y_5041_,
        v___y_5042_,
    );
    crate::leanh::lean_dec(v___y_5042_);
    crate::leanh::lean_dec_ref(v___y_5041_);
    crate::leanh::lean_dec(v___y_5040_);
    crate::leanh::lean_dec_ref(v___y_5039_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(
    mut v_00_u03b1_5045_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5060_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5052_);
                crate::leanh::lean_inc_ref(v___y_5051_);
                crate::leanh::lean_inc(v___y_5050_);
                crate::leanh::lean_inc_ref(v___y_5049_);
                v___x_5054_ = crate::leanh::lean_apply_5(
                    v___y_5047_,
                    v___y_5049_,
                    v___y_5050_,
                    v___y_5051_,
                    v___y_5052_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5054_) == 0 {
                    v_a_5055_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                    crate::leanh::lean_inc(v_a_5055_);
                    crate::leanh::lean_dec_ref_known(v___x_5054_, 1);
                    crate::leanh::lean_inc(v___y_5052_);
                    crate::leanh::lean_inc_ref(v___y_5051_);
                    crate::leanh::lean_inc(v___y_5050_);
                    crate::leanh::lean_inc_ref(v___y_5049_);
                    v___x_5056_ = crate::leanh::lean_apply_6(
                        v___y_5048_,
                        v_a_5055_,
                        v___y_5049_,
                        v___y_5050_,
                        v___y_5051_,
                        v___y_5052_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5056_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5048_);
                    v_a_5057_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                    v_isSharedCheck_5064_ = (!crate::leanh::lean_is_exclusive(v___x_5054_)) as u8;
                    if v_isSharedCheck_5064_ == 0 {
                        v___x_5059_ = v___x_5054_;
                        v_isShared_5060_ = v_isSharedCheck_5064_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5057_);
                        crate::leanh::lean_dec(v___x_5054_);
                        v___x_5059_ = crate::leanh::lean_box(0);
                        v_isShared_5060_ = v_isSharedCheck_5064_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5060_ == 0 {
                    v___x_5062_ = v___x_5059_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
                    v___x_5062_ = v_reuseFailAlloc_5063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(
    mut v_00_u03b1_5065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5074_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(
        v_00_u03b1_5065_,
        v_00_u03b2_5066_,
        v___y_5067_,
        v___y_5068_,
        v___y_5069_,
        v___y_5070_,
        v___y_5071_,
        v___y_5072_,
    );
    crate::leanh::lean_dec(v___y_5072_);
    crate::leanh::lean_dec_ref(v___y_5071_);
    crate::leanh::lean_dec(v___y_5070_);
    crate::leanh::lean_dec_ref(v___y_5069_);
    return v_res_5074_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5075_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5076_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once),
        _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0,
    );
    v___x_5077_ = l_StateRefT_x27_instMonad___redArg(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM() -> *mut crate::leanh::LeanObject {
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v_toFunctor_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___f_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut v_unused_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_unused_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5082_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1,
                );
                v_toApplicative_5083_ = crate::leanh::lean_ctor_get(v___x_5082_, 0);
                v_toFunctor_5084_ = crate::leanh::lean_ctor_get(v_toApplicative_5083_, 0);
                v_toSeq_5085_ = crate::leanh::lean_ctor_get(v_toApplicative_5083_, 2);
                v_toSeqLeft_5086_ = crate::leanh::lean_ctor_get(v_toApplicative_5083_, 3);
                v_toSeqRight_5087_ = crate::leanh::lean_ctor_get(v_toApplicative_5083_, 4);
                v___f_5088_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2;
                v___f_5089_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5084_, 2);
                v___f_5090_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5090_, 0, v_toFunctor_5084_);
                v___f_5091_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5091_, 0, v_toFunctor_5084_);
                v___x_5092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5092_, 0, v___f_5090_);
                crate::leanh::lean_ctor_set(v___x_5092_, 1, v___f_5091_);
                crate::leanh::lean_inc(v_toSeqRight_5087_);
                v___f_5093_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5093_, 0, v_toSeqRight_5087_);
                crate::leanh::lean_inc(v_toSeqLeft_5086_);
                v___f_5094_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5094_, 0, v_toSeqLeft_5086_);
                crate::leanh::lean_inc(v_toSeq_5085_);
                v___f_5095_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5095_, 0, v_toSeq_5085_);
                v___x_5096_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5096_, 0, v___x_5092_);
                crate::leanh::lean_ctor_set(v___x_5096_, 1, v___f_5088_);
                crate::leanh::lean_ctor_set(v___x_5096_, 2, v___f_5095_);
                crate::leanh::lean_ctor_set(v___x_5096_, 3, v___f_5094_);
                crate::leanh::lean_ctor_set(v___x_5096_, 4, v___f_5093_);
                v___x_5097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5097_, 0, v___x_5096_);
                crate::leanh::lean_ctor_set(v___x_5097_, 1, v___f_5089_);
                v___x_5098_ = l_StateRefT_x27_instMonad___redArg(v___x_5097_);
                v_toApplicative_5099_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                v_isSharedCheck_5126_ = (!crate::leanh::lean_is_exclusive(v___x_5098_)) as u8;
                if v_isSharedCheck_5126_ == 0 {
                    v_unused_5127_ = crate::leanh::lean_ctor_get(v___x_5098_, 1);
                    crate::leanh::lean_dec(v_unused_5127_);
                    v___x_5101_ = v___x_5098_;
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5099_);
                    crate::leanh::lean_dec(v___x_5098_);
                    v___x_5101_ = crate::leanh::lean_box(0);
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5103_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 0);
                v_toSeq_5104_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 2);
                v_toSeqLeft_5105_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 3);
                v_toSeqRight_5106_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 4);
                v_isSharedCheck_5124_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5099_)) as u8;
                if v_isSharedCheck_5124_ == 0 {
                    v_unused_5125_ = crate::leanh::lean_ctor_get(v_toApplicative_5099_, 1);
                    crate::leanh::lean_dec(v_unused_5125_);
                    v___x_5108_ = v_toApplicative_5099_;
                    v_isShared_5109_ = v_isSharedCheck_5124_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5106_);
                    crate::leanh::lean_inc(v_toSeqLeft_5105_);
                    crate::leanh::lean_inc(v_toSeq_5104_);
                    crate::leanh::lean_inc(v_toFunctor_5103_);
                    crate::leanh::lean_dec(v_toApplicative_5099_);
                    v___x_5108_ = crate::leanh::lean_box(0);
                    v_isShared_5109_ = v_isSharedCheck_5124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5110_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4;
                v___f_5111_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_5103_);
                v___f_5112_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5112_, 0, v_toFunctor_5103_);
                v___f_5113_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5113_, 0, v_toFunctor_5103_);
                v___x_5114_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5114_, 0, v___f_5112_);
                crate::leanh::lean_ctor_set(v___x_5114_, 1, v___f_5113_);
                v___f_5115_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5115_, 0, v_toSeqRight_5106_);
                v___f_5116_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5116_, 0, v_toSeqLeft_5105_);
                v___f_5117_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5117_, 0, v_toSeq_5104_);
                if v_isShared_5109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5108_, 4, v___f_5115_);
                    crate::leanh::lean_ctor_set(v___x_5108_, 3, v___f_5116_);
                    crate::leanh::lean_ctor_set(v___x_5108_, 2, v___f_5117_);
                    crate::leanh::lean_ctor_set(v___x_5108_, 1, v___f_5110_);
                    crate::leanh::lean_ctor_set(v___x_5108_, 0, v___x_5114_);
                    v___x_5119_ = v___x_5108_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5123_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 1, v___f_5110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 2, v___f_5117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 3, v___f_5116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 4, v___f_5115_);
                    v___x_5119_ = v_reuseFailAlloc_5123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5101_, 1, v___f_5111_);
                    crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5119_);
                    v___x_5121_ = v___x_5101_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 1, v___f_5111_);
                    v___x_5121_ = v_reuseFailAlloc_5122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase___redArg(
    mut v_phase_5128_: u8,
    mut v_x_5129_: *mut crate::leanh::LeanObject,
    mut v_a_5130_: *mut crate::leanh::LeanObject,
    mut v_a_5131_: *mut crate::leanh::LeanObject,
    mut v_a_5132_: *mut crate::leanh::LeanObject,
    mut v_a_5133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_5135_ = crate::leanh::lean_ctor_get(v_a_5130_, 0);
    crate::leanh::lean_inc_ref(v_config_5135_);
    v___x_5136_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5136_, 0, v_config_5135_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5136_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_phase_5128_,
    );
    crate::leanh::lean_inc(v_a_5133_);
    crate::leanh::lean_inc_ref(v_a_5132_);
    crate::leanh::lean_inc(v_a_5131_);
    v___x_5137_ = crate::leanh::lean_apply_5(
        v_x_5129_,
        v___x_5136_,
        v_a_5131_,
        v_a_5132_,
        v_a_5133_,
        crate::leanh::lean_box(0),
    );
    return v___x_5137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase___redArg___boxed(
    mut v_phase_5138_: *mut crate::leanh::LeanObject,
    mut v_x_5139_: *mut crate::leanh::LeanObject,
    mut v_a_5140_: *mut crate::leanh::LeanObject,
    mut v_a_5141_: *mut crate::leanh::LeanObject,
    mut v_a_5142_: *mut crate::leanh::LeanObject,
    mut v_a_5143_: *mut crate::leanh::LeanObject,
    mut v_a_5144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5145_: u8 = 0;
    let mut v_res_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5145_ = (crate::leanh::lean_unbox(v_phase_5138_) as u8);
    v_res_5146_ = l_Lean_Compiler_LCNF_withPhase___redArg(
        v_phase_boxed_5145_,
        v_x_5139_,
        v_a_5140_,
        v_a_5141_,
        v_a_5142_,
        v_a_5143_,
    );
    crate::leanh::lean_dec(v_a_5143_);
    crate::leanh::lean_dec_ref(v_a_5142_);
    crate::leanh::lean_dec(v_a_5141_);
    crate::leanh::lean_dec_ref(v_a_5140_);
    return v_res_5146_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase(
    mut v_00_u03b1_5147_: *mut crate::leanh::LeanObject,
    mut v_phase_5148_: u8,
    mut v_x_5149_: *mut crate::leanh::LeanObject,
    mut v_a_5150_: *mut crate::leanh::LeanObject,
    mut v_a_5151_: *mut crate::leanh::LeanObject,
    mut v_a_5152_: *mut crate::leanh::LeanObject,
    mut v_a_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_5155_ = crate::leanh::lean_ctor_get(v_a_5150_, 0);
    crate::leanh::lean_inc_ref(v_config_5155_);
    v___x_5156_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5156_, 0, v_config_5155_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5156_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_phase_5148_,
    );
    crate::leanh::lean_inc(v_a_5153_);
    crate::leanh::lean_inc_ref(v_a_5152_);
    crate::leanh::lean_inc(v_a_5151_);
    v___x_5157_ = crate::leanh::lean_apply_5(
        v_x_5149_,
        v___x_5156_,
        v_a_5151_,
        v_a_5152_,
        v_a_5153_,
        crate::leanh::lean_box(0),
    );
    return v___x_5157_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase___boxed(
    mut v_00_u03b1_5158_: *mut crate::leanh::LeanObject,
    mut v_phase_5159_: *mut crate::leanh::LeanObject,
    mut v_x_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v_a_5162_: *mut crate::leanh::LeanObject,
    mut v_a_5163_: *mut crate::leanh::LeanObject,
    mut v_a_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_5166_: u8 = 0;
    let mut v_res_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5166_ = (crate::leanh::lean_unbox(v_phase_5159_) as u8);
    v_res_5167_ = l_Lean_Compiler_LCNF_withPhase(
        v_00_u03b1_5158_,
        v_phase_boxed_5166_,
        v_x_5160_,
        v_a_5161_,
        v_a_5162_,
        v_a_5163_,
        v_a_5164_,
    );
    crate::leanh::lean_dec(v_a_5164_);
    crate::leanh::lean_dec_ref(v_a_5163_);
    crate::leanh::lean_dec(v_a_5162_);
    crate::leanh::lean_dec_ref(v_a_5161_);
    return v_res_5167_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___redArg(
    mut v_a_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_5170_ = crate::leanh::lean_ctor_get_uint8(
        v_a_5168_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_5171_ = crate::leanh::lean_box((v_phase_5170_) as usize);
    v___x_5172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5172_, 0, v___x_5171_);
    return v___x_5172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___redArg___boxed(
    mut v_a_5173_: *mut crate::leanh::LeanObject,
    mut v_a_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5173_);
    crate::leanh::lean_dec_ref(v_a_5173_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase(
    mut v_a_5176_: *mut crate::leanh::LeanObject,
    mut v_a_5177_: *mut crate::leanh::LeanObject,
    mut v_a_5178_: *mut crate::leanh::LeanObject,
    mut v_a_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5181_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5176_);
    return v___x_5181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___boxed(
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
    mut v_a_5186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5187_ = l_Lean_Compiler_LCNF_getPhase(v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
    crate::leanh::lean_dec(v_a_5185_);
    crate::leanh::lean_dec_ref(v_a_5184_);
    crate::leanh::lean_dec(v_a_5183_);
    crate::leanh::lean_dec_ref(v_a_5182_);
    return v_res_5187_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity___redArg(
    mut v_a_5188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5190_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5188_);
                v_a_5191_ = crate::leanh::lean_ctor_get(v___x_5190_, 0);
                v_isSharedCheck_5201_ = (!crate::leanh::lean_is_exclusive(v___x_5190_)) as u8;
                if v_isSharedCheck_5201_ == 0 {
                    v___x_5193_ = v___x_5190_;
                    v_isShared_5194_ = v_isSharedCheck_5201_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5191_);
                    crate::leanh::lean_dec(v___x_5190_);
                    v___x_5193_ = crate::leanh::lean_box(0);
                    v_isShared_5194_ = v_isSharedCheck_5201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5195_ = (crate::leanh::lean_unbox(v_a_5191_) as u8);
                crate::leanh::lean_dec(v_a_5191_);
                v___x_5196_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5195_);
                v___x_5197_ = crate::leanh::lean_box((v___x_5196_) as usize);
                if v_isShared_5194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5193_, 0, v___x_5197_);
                    v___x_5199_ = v___x_5193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5197_);
                    v___x_5199_ = v_reuseFailAlloc_5200_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5199_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity___redArg___boxed(
    mut v_a_5202_: *mut crate::leanh::LeanObject,
    mut v_a_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5204_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5202_);
    crate::leanh::lean_dec_ref(v_a_5202_);
    return v_res_5204_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity(
    mut v_a_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
    mut v_a_5207_: *mut crate::leanh::LeanObject,
    mut v_a_5208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5205_);
    return v___x_5210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity___boxed(
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
    mut v_a_5213_: *mut crate::leanh::LeanObject,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5216_ = l_Lean_Compiler_LCNF_getPurity(v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
    crate::leanh::lean_dec(v_a_5214_);
    crate::leanh::lean_dec_ref(v_a_5213_);
    crate::leanh::lean_dec(v_a_5212_);
    crate::leanh::lean_dec_ref(v_a_5211_);
    return v_res_5216_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase___redArg(
    mut v_a_5217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: u8 = 0;
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5219_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5217_);
                v_a_5220_ = crate::leanh::lean_ctor_get(v___x_5219_, 0);
                v_isSharedCheck_5235_ = (!crate::leanh::lean_is_exclusive(v___x_5219_)) as u8;
                if v_isSharedCheck_5235_ == 0 {
                    v___x_5222_ = v___x_5219_;
                    v_isShared_5223_ = v_isSharedCheck_5235_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5220_);
                    crate::leanh::lean_dec(v___x_5219_);
                    v___x_5222_ = crate::leanh::lean_box(0);
                    v_isShared_5223_ = v_isSharedCheck_5235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5224_ = (crate::leanh::lean_unbox(v_a_5220_) as u8);
                crate::leanh::lean_dec(v_a_5220_);
                if v___x_5224_ == 0 {
                    v___x_5225_ = 1;
                    v___x_5226_ = crate::leanh::lean_box((v___x_5225_) as usize);
                    if v_isShared_5223_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5222_, 0, v___x_5226_);
                        v___x_5228_ = v___x_5222_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5229_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
                        v___x_5228_ = v_reuseFailAlloc_5229_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5230_ = 0;
                    v___x_5231_ = crate::leanh::lean_box((v___x_5230_) as usize);
                    if v_isShared_5223_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5222_, 0, v___x_5231_);
                        v___x_5233_ = v___x_5222_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
                        v___x_5233_ = v_reuseFailAlloc_5234_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5228_;
            }
            3 => {
                return v___x_5233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase___redArg___boxed(
    mut v_a_5236_: *mut crate::leanh::LeanObject,
    mut v_a_5237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5238_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_5236_);
    crate::leanh::lean_dec_ref(v_a_5236_);
    return v_res_5238_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase(
    mut v_a_5239_: *mut crate::leanh::LeanObject,
    mut v_a_5240_: *mut crate::leanh::LeanObject,
    mut v_a_5241_: *mut crate::leanh::LeanObject,
    mut v_a_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5244_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_5239_);
    return v___x_5244_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase___boxed(
    mut v_a_5245_: *mut crate::leanh::LeanObject,
    mut v_a_5246_: *mut crate::leanh::LeanObject,
    mut v_a_5247_: *mut crate::leanh::LeanObject,
    mut v_a_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_);
    crate::leanh::lean_dec(v_a_5248_);
    crate::leanh::lean_dec_ref(v_a_5247_);
    crate::leanh::lean_dec(v_a_5246_);
    crate::leanh::lean_dec_ref(v_a_5245_);
    return v_res_5250_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5251_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5252_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0,
    );
    v___x_5253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5253_, 0, v___x_5252_);
    return v___x_5253_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1,
    );
    v___x_5255_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5256_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5256_, 0, v___x_5255_);
    crate::leanh::lean_ctor_set(v___x_5256_, 1, v___x_5255_);
    crate::leanh::lean_ctor_set(v___x_5256_, 2, v___x_5255_);
    crate::leanh::lean_ctor_set(v___x_5256_, 3, v___x_5255_);
    crate::leanh::lean_ctor_set(v___x_5256_, 4, v___x_5254_);
    crate::leanh::lean_ctor_set(v___x_5256_, 5, v___x_5254_);
    crate::leanh::lean_ctor_set(v___x_5256_, 6, v___x_5254_);
    crate::leanh::lean_ctor_set(v___x_5256_, 7, v___x_5254_);
    crate::leanh::lean_ctor_set(v___x_5256_, 8, v___x_5254_);
    crate::leanh::lean_ctor_set(v___x_5256_, 9, v___x_5254_);
    return v___x_5256_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(
    mut v_msgData_5257_: *mut crate::leanh::LeanObject,
    mut v___y_5258_: *mut crate::leanh::LeanObject,
    mut v___y_5259_: *mut crate::leanh::LeanObject,
    mut v___y_5260_: *mut crate::leanh::LeanObject,
    mut v___y_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v_env_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v_options_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut v_unused_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_a_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5263_ = lean_st_ref_get(v___y_5261_);
                v___x_5264_ = lean_st_ref_get(v___y_5259_);
                v___x_5265_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5258_);
                if crate::leanh::lean_obj_tag(v___x_5265_) == 0 {
                    v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5288_ = (!crate::leanh::lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5288_ == 0 {
                        v___x_5268_ = v___x_5265_;
                        v_isShared_5269_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5266_);
                        crate::leanh::lean_dec(v___x_5265_);
                        v___x_5268_ = crate::leanh::lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5264_);
                    crate::leanh::lean_dec(v___x_5263_);
                    crate::leanh::lean_dec_ref(v_msgData_5257_);
                    v_a_5289_ = crate::leanh::lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5296_ = (!crate::leanh::lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5291_ = v___x_5265_;
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5289_);
                        crate::leanh::lean_dec(v___x_5265_);
                        v___x_5291_ = crate::leanh::lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_5270_ = crate::leanh::lean_ctor_get(v___x_5263_, 0);
                crate::leanh::lean_inc_ref(v_env_5270_);
                crate::leanh::lean_dec(v___x_5263_);
                v_lctx_5271_ = crate::leanh::lean_ctor_get(v___x_5264_, 0);
                v_isSharedCheck_5286_ = (!crate::leanh::lean_is_exclusive(v___x_5264_)) as u8;
                if v_isSharedCheck_5286_ == 0 {
                    v_unused_5287_ = crate::leanh::lean_ctor_get(v___x_5264_, 1);
                    crate::leanh::lean_dec(v_unused_5287_);
                    v___x_5273_ = v___x_5264_;
                    v_isShared_5274_ = v_isSharedCheck_5286_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_5271_);
                    crate::leanh::lean_dec(v___x_5264_);
                    v___x_5273_ = crate::leanh::lean_box(0);
                    v_isShared_5274_ = v_isSharedCheck_5286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_options_5275_ = crate::leanh::lean_ctor_get(v___y_5260_, 2);
                v___x_5276_ = (crate::leanh::lean_unbox(v_a_5266_) as u8);
                crate::leanh::lean_dec(v_a_5266_);
                v___x_5277_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5271_, v___x_5276_);
                crate::leanh::lean_dec_ref(v_lctx_5271_);
                v___x_5278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
                crate::leanh::lean_inc_ref(v_options_5275_);
                v___x_5279_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5279_, 0, v_env_5270_);
                crate::leanh::lean_ctor_set(v___x_5279_, 1, v___x_5278_);
                crate::leanh::lean_ctor_set(v___x_5279_, 2, v___x_5277_);
                crate::leanh::lean_ctor_set(v___x_5279_, 3, v_options_5275_);
                if v_isShared_5274_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5273_, 3);
                    crate::leanh::lean_ctor_set(v___x_5273_, 1, v_msgData_5257_);
                    crate::leanh::lean_ctor_set(v___x_5273_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5273_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 1, v_msgData_5257_);
                    v___x_5281_ = v_reuseFailAlloc_5285_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5281_);
                    v___x_5283_ = v___x_5268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5281_);
                    v___x_5283_ = v_reuseFailAlloc_5284_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5283_;
            }
            5 => {
                if v_isShared_5292_ == 0 {
                    v___x_5294_ = v___x_5291_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
                    v___x_5294_ = v_reuseFailAlloc_5295_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(
    mut v_msgData_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5303_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(
        v_msgData_5297_,
        v___y_5298_,
        v___y_5299_,
        v___y_5300_,
        v___y_5301_,
    );
    crate::leanh::lean_dec(v___y_5301_);
    crate::leanh::lean_dec_ref(v___y_5300_);
    crate::leanh::lean_dec(v___y_5299_);
    crate::leanh::lean_dec_ref(v___y_5298_);
    return v_res_5303_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
    mut v_msg_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v_env_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v___x_5326_: u8 = 0;
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_unused_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5312_ = crate::leanh::lean_ctor_get(v___y_5309_, 2);
                v_ref_5313_ = crate::leanh::lean_ctor_get(v___y_5309_, 5);
                v___x_5314_ = lean_st_ref_get(v___y_5310_);
                v___x_5315_ = lean_st_ref_get(v___y_5308_);
                v___x_5316_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5307_);
                if crate::leanh::lean_obj_tag(v___x_5316_) == 0 {
                    v_a_5317_ = crate::leanh::lean_ctor_get(v___x_5316_, 0);
                    v_isSharedCheck_5339_ = (!crate::leanh::lean_is_exclusive(v___x_5316_)) as u8;
                    if v_isSharedCheck_5339_ == 0 {
                        v___x_5319_ = v___x_5316_;
                        v_isShared_5320_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5317_);
                        crate::leanh::lean_dec(v___x_5316_);
                        v___x_5319_ = crate::leanh::lean_box(0);
                        v_isShared_5320_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5315_);
                    crate::leanh::lean_dec(v___x_5314_);
                    crate::leanh::lean_dec_ref(v_msg_5306_);
                    v_a_5340_ = crate::leanh::lean_ctor_get(v___x_5316_, 0);
                    v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v___x_5316_)) as u8;
                    if v_isSharedCheck_5347_ == 0 {
                        v___x_5342_ = v___x_5316_;
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5340_);
                        crate::leanh::lean_dec(v___x_5316_);
                        v___x_5342_ = crate::leanh::lean_box(0);
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_5321_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                crate::leanh::lean_inc_ref(v_env_5321_);
                crate::leanh::lean_dec(v___x_5314_);
                v_lctx_5322_ = crate::leanh::lean_ctor_get(v___x_5315_, 0);
                v_isSharedCheck_5337_ = (!crate::leanh::lean_is_exclusive(v___x_5315_)) as u8;
                if v_isSharedCheck_5337_ == 0 {
                    v_unused_5338_ = crate::leanh::lean_ctor_get(v___x_5315_, 1);
                    crate::leanh::lean_dec(v_unused_5338_);
                    v___x_5324_ = v___x_5315_;
                    v_isShared_5325_ = v_isSharedCheck_5337_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_5322_);
                    crate::leanh::lean_dec(v___x_5315_);
                    v___x_5324_ = crate::leanh::lean_box(0);
                    v_isShared_5325_ = v_isSharedCheck_5337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5326_ = (crate::leanh::lean_unbox(v_a_5317_) as u8);
                crate::leanh::lean_dec(v_a_5317_);
                v___x_5327_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5322_, v___x_5326_);
                crate::leanh::lean_dec_ref(v_lctx_5322_);
                v___x_5328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
                crate::leanh::lean_inc_ref(v_options_5312_);
                v___x_5329_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5329_, 0, v_env_5321_);
                crate::leanh::lean_ctor_set(v___x_5329_, 1, v___x_5328_);
                crate::leanh::lean_ctor_set(v___x_5329_, 2, v___x_5327_);
                crate::leanh::lean_ctor_set(v___x_5329_, 3, v_options_5312_);
                if v_isShared_5325_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5324_, 3);
                    crate::leanh::lean_ctor_set(v___x_5324_, 1, v_msg_5306_);
                    crate::leanh::lean_ctor_set(v___x_5324_, 0, v___x_5329_);
                    v___x_5331_ = v___x_5324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 1, v_msg_5306_);
                    v___x_5331_ = v_reuseFailAlloc_5336_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_5313_);
                v___x_5332_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5332_, 0, v_ref_5313_);
                crate::leanh::lean_ctor_set(v___x_5332_, 1, v___x_5331_);
                if v_isShared_5320_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5319_, 1);
                    crate::leanh::lean_ctor_set(v___x_5319_, 0, v___x_5332_);
                    v___x_5334_ = v___x_5319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
                    v___x_5334_ = v_reuseFailAlloc_5335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5334_;
            }
            5 => {
                if v_isShared_5343_ == 0 {
                    v___x_5345_ = v___x_5342_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg___boxed(
    mut v_msg_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5354_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
        v_msg_5348_,
        v___y_5349_,
        v___y_5350_,
        v___y_5351_,
        v___y_5352_,
    );
    crate::leanh::lean_dec(v___y_5352_);
    crate::leanh::lean_dec_ref(v___y_5351_);
    crate::leanh::lean_dec(v___y_5350_);
    crate::leanh::lean_dec_ref(v___y_5349_);
    return v_res_5354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(
    mut v_00_u03b1_5355_: *mut crate::leanh::LeanObject,
    mut v_msg_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5362_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
        v_msg_5356_,
        v___y_5357_,
        v___y_5358_,
        v___y_5359_,
        v___y_5360_,
    );
    return v___x_5362_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___boxed(
    mut v_00_u03b1_5363_: *mut crate::leanh::LeanObject,
    mut v_msg_5364_: *mut crate::leanh::LeanObject,
    mut v___y_5365_: *mut crate::leanh::LeanObject,
    mut v___y_5366_: *mut crate::leanh::LeanObject,
    mut v___y_5367_: *mut crate::leanh::LeanObject,
    mut v___y_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(
        v_00_u03b1_5363_,
        v_msg_5364_,
        v___y_5365_,
        v___y_5366_,
        v___y_5367_,
        v___y_5368_,
    );
    crate::leanh::lean_dec(v___y_5368_);
    crate::leanh::lean_dec_ref(v___y_5367_);
    crate::leanh::lean_dec(v___y_5366_);
    crate::leanh::lean_dec_ref(v___y_5365_);
    return v_res_5370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(
    mut v_a_5371_: *mut crate::leanh::LeanObject,
    mut v_x_5372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5372_) == 0 {
                    v___x_5373_ = crate::leanh::lean_box(0);
                    return v___x_5373_;
                } else {
                    v_key_5374_ = crate::leanh::lean_ctor_get(v_x_5372_, 0);
                    v_value_5375_ = crate::leanh::lean_ctor_get(v_x_5372_, 1);
                    v_tail_5376_ = crate::leanh::lean_ctor_get(v_x_5372_, 2);
                    v___x_5377_ = l_Lean_instBEqFVarId_beq(v_key_5374_, v_a_5371_);
                    if v___x_5377_ == 0 {
                        v_x_5372_ = v_tail_5376_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5375_);
                        v___x_5379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5379_, 0, v_value_5375_);
                        return v___x_5379_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(
    mut v_a_5380_: *mut crate::leanh::LeanObject,
    mut v_x_5381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_5380_, v_x_5381_);
    crate::leanh::lean_dec(v_x_5381_);
    crate::leanh::lean_dec(v_a_5380_);
    return v_res_5382_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(
    mut v_m_5383_: *mut crate::leanh::LeanObject,
    mut v_a_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: u64 = 0;
    let mut v___x_5388_: u64 = 0;
    let mut v___x_5389_: u64 = 0;
    let mut v_fold_5390_: u64 = 0;
    let mut v___x_5391_: u64 = 0;
    let mut v___x_5392_: u64 = 0;
    let mut v___x_5393_: u64 = 0;
    let mut v___x_5394_: usize = 0;
    let mut v___x_5395_: usize = 0;
    let mut v___x_5396_: usize = 0;
    let mut v___x_5397_: usize = 0;
    let mut v___x_5398_: usize = 0;
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5385_ = crate::leanh::lean_ctor_get(v_m_5383_, 1);
    v___x_5386_ = lean_array_get_size(v_buckets_5385_);
    v___x_5387_ = l_Lean_instHashableFVarId_hash(v_a_5384_);
    v___x_5388_ = 32u64;
    v___x_5389_ = lean_uint64_shift_right(v___x_5387_, v___x_5388_);
    v_fold_5390_ = lean_uint64_xor(v___x_5387_, v___x_5389_);
    v___x_5391_ = 16u64;
    v___x_5392_ = lean_uint64_shift_right(v_fold_5390_, v___x_5391_);
    v___x_5393_ = lean_uint64_xor(v_fold_5390_, v___x_5392_);
    v___x_5394_ = lean_uint64_to_usize(v___x_5393_);
    v___x_5395_ = lean_usize_of_nat(v___x_5386_);
    v___x_5396_ = 1usize;
    v___x_5397_ = lean_usize_sub(v___x_5395_, v___x_5396_);
    v___x_5398_ = lean_usize_land(v___x_5394_, v___x_5397_);
    v___x_5399_ = lean_array_uget_borrowed(v_buckets_5385_, v___x_5398_);
    v___x_5400_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_5384_, v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg___boxed(
    mut v_m_5401_: *mut crate::leanh::LeanObject,
    mut v_a_5402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_5401_, v_a_5402_);
    crate::leanh::lean_dec(v_a_5402_);
    crate::leanh::lean_dec_ref(v_m_5401_);
    return v_res_5403_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getType___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5405_ = l_Lean_Compiler_LCNF_getType___closed__0;
    v___x_5406_ = l_Lean_stringToMessageData(v___x_5405_);
    return v___x_5406_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getType(
    mut v_fvarId_5407_: *mut crate::leanh::LeanObject,
    mut v_a_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v_a_5410_: *mut crate::leanh::LeanObject,
    mut v_a_5411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5418_: u8 = 0;
    let mut v___y_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5438_: u8 = 0;
    let mut v_type_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut v___x_5444_: u8 = 0;
    let mut v_funDeclsPure_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5453_: u8 = 0;
    let mut v_type_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v___x_5459_: u8 = 0;
    let mut v_paramsPure_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: u8 = 0;
    let mut v_letDeclsPure_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut v_a_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5469_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5413_ = lean_st_ref_get(v_a_5409_);
                v___x_5414_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5408_);
                if crate::leanh::lean_obj_tag(v___x_5414_) == 0 {
                    v_a_5415_ = crate::leanh::lean_ctor_get(v___x_5414_, 0);
                    v_isSharedCheck_5465_ = (!crate::leanh::lean_is_exclusive(v___x_5414_)) as u8;
                    if v_isSharedCheck_5465_ == 0 {
                        v___x_5417_ = v___x_5414_;
                        v_isShared_5418_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5415_);
                        crate::leanh::lean_dec(v___x_5414_);
                        v___x_5417_ = crate::leanh::lean_box(0);
                        v_isShared_5418_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5413_);
                    crate::leanh::lean_dec(v_fvarId_5407_);
                    v_a_5466_ = crate::leanh::lean_ctor_get(v___x_5414_, 0);
                    v_isSharedCheck_5473_ = (!crate::leanh::lean_is_exclusive(v___x_5414_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5468_ = v___x_5414_;
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5466_);
                        crate::leanh::lean_dec(v___x_5414_);
                        v___x_5468_ = crate::leanh::lean_box(0);
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_5431_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                crate::leanh::lean_inc_ref(v_lctx_5431_);
                crate::leanh::lean_dec(v___x_5413_);
                v___x_5462_ = (crate::leanh::lean_unbox(v_a_5415_) as u8);
                if v___x_5462_ == 0 {
                    v_letDeclsPure_5463_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 2);
                    crate::leanh::lean_inc_ref(v_letDeclsPure_5463_);
                    v___y_5448_ = v_letDeclsPure_5463_;
                    state = 7;
                    continue;
                } else {
                    v_letDeclsImpure_5464_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 3);
                    crate::leanh::lean_inc_ref(v_letDeclsImpure_5464_);
                    v___y_5448_ = v_letDeclsImpure_5464_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_5421_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5420_, v_fvarId_5407_);
                crate::leanh::lean_dec_ref(v___y_5420_);
                if crate::leanh::lean_obj_tag(v___x_5421_) == 1 {
                    crate::leanh::lean_dec(v_fvarId_5407_);
                    v_val_5422_ = crate::leanh::lean_ctor_get(v___x_5421_, 0);
                    crate::leanh::lean_inc(v_val_5422_);
                    crate::leanh::lean_dec_ref_known(v___x_5421_, 1);
                    v_type_5423_ = crate::leanh::lean_ctor_get(v_val_5422_, 3);
                    crate::leanh::lean_inc_ref(v_type_5423_);
                    crate::leanh::lean_dec(v_val_5422_);
                    if v_isShared_5418_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5417_, 0, v_type_5423_);
                        v___x_5425_ = v___x_5417_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_type_5423_);
                        v___x_5425_ = v_reuseFailAlloc_5426_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5421_);
                    crate::leanh::lean_del_object(v___x_5417_);
                    v___x_5427_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getType___closed__1,
                    );
                    v___x_5428_ = l_Lean_MessageData_ofName(v_fvarId_5407_);
                    v___x_5429_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5429_, 0, v___x_5427_);
                    crate::leanh::lean_ctor_set(v___x_5429_, 1, v___x_5428_);
                    v___x_5430_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
                            v___x_5429_,
                            v_a_5408_,
                            v_a_5409_,
                            v_a_5410_,
                            v_a_5411_,
                        );
                    return v___x_5430_;
                }
            }
            3 => {
                return v___x_5425_;
            }
            4 => {
                v___x_5434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5433_, v_fvarId_5407_);
                crate::leanh::lean_dec_ref(v___y_5433_);
                if crate::leanh::lean_obj_tag(v___x_5434_) == 1 {
                    crate::leanh::lean_dec_ref(v_lctx_5431_);
                    crate::leanh::lean_del_object(v___x_5417_);
                    crate::leanh::lean_dec(v_a_5415_);
                    crate::leanh::lean_dec(v_fvarId_5407_);
                    v_val_5435_ = crate::leanh::lean_ctor_get(v___x_5434_, 0);
                    v_isSharedCheck_5443_ = (!crate::leanh::lean_is_exclusive(v___x_5434_)) as u8;
                    if v_isSharedCheck_5443_ == 0 {
                        v___x_5437_ = v___x_5434_;
                        v_isShared_5438_ = v_isSharedCheck_5443_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5435_);
                        crate::leanh::lean_dec(v___x_5434_);
                        v___x_5437_ = crate::leanh::lean_box(0);
                        v_isShared_5438_ = v_isSharedCheck_5443_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5434_);
                    v___x_5444_ = (crate::leanh::lean_unbox(v_a_5415_) as u8);
                    crate::leanh::lean_dec(v_a_5415_);
                    if v___x_5444_ == 0 {
                        v_funDeclsPure_5445_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 4);
                        crate::leanh::lean_inc_ref(v_funDeclsPure_5445_);
                        crate::leanh::lean_dec_ref(v_lctx_5431_);
                        v___y_5420_ = v_funDeclsPure_5445_;
                        state = 2;
                        continue;
                    } else {
                        v_funDeclsImpure_5446_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 5);
                        crate::leanh::lean_inc_ref(v_funDeclsImpure_5446_);
                        crate::leanh::lean_dec_ref(v_lctx_5431_);
                        v___y_5420_ = v_funDeclsImpure_5446_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_type_5439_ = crate::leanh::lean_ctor_get(v_val_5435_, 2);
                crate::leanh::lean_inc_ref(v_type_5439_);
                crate::leanh::lean_dec(v_val_5435_);
                if v_isShared_5438_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5437_, 0);
                    crate::leanh::lean_ctor_set(v___x_5437_, 0, v_type_5439_);
                    v___x_5441_ = v___x_5437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_type_5439_);
                    v___x_5441_ = v_reuseFailAlloc_5442_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5441_;
            }
            7 => {
                v___x_5449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5448_, v_fvarId_5407_);
                crate::leanh::lean_dec_ref(v___y_5448_);
                if crate::leanh::lean_obj_tag(v___x_5449_) == 1 {
                    crate::leanh::lean_dec_ref(v_lctx_5431_);
                    crate::leanh::lean_del_object(v___x_5417_);
                    crate::leanh::lean_dec(v_a_5415_);
                    crate::leanh::lean_dec(v_fvarId_5407_);
                    v_val_5450_ = crate::leanh::lean_ctor_get(v___x_5449_, 0);
                    v_isSharedCheck_5458_ = (!crate::leanh::lean_is_exclusive(v___x_5449_)) as u8;
                    if v_isSharedCheck_5458_ == 0 {
                        v___x_5452_ = v___x_5449_;
                        v_isShared_5453_ = v_isSharedCheck_5458_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5450_);
                        crate::leanh::lean_dec(v___x_5449_);
                        v___x_5452_ = crate::leanh::lean_box(0);
                        v_isShared_5453_ = v_isSharedCheck_5458_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5449_);
                    v___x_5459_ = (crate::leanh::lean_unbox(v_a_5415_) as u8);
                    if v___x_5459_ == 0 {
                        v_paramsPure_5460_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 0);
                        crate::leanh::lean_inc_ref(v_paramsPure_5460_);
                        v___y_5433_ = v_paramsPure_5460_;
                        state = 4;
                        continue;
                    } else {
                        v_paramsImpure_5461_ = crate::leanh::lean_ctor_get(v_lctx_5431_, 1);
                        crate::leanh::lean_inc_ref(v_paramsImpure_5461_);
                        v___y_5433_ = v_paramsImpure_5461_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v_type_5454_ = crate::leanh::lean_ctor_get(v_val_5450_, 2);
                crate::leanh::lean_inc_ref(v_type_5454_);
                crate::leanh::lean_dec(v_val_5450_);
                if v_isShared_5453_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5452_, 0);
                    crate::leanh::lean_ctor_set(v___x_5452_, 0, v_type_5454_);
                    v___x_5456_ = v___x_5452_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_type_5454_);
                    v___x_5456_ = v_reuseFailAlloc_5457_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5456_;
            }
            10 => {
                if v_isShared_5469_ == 0 {
                    v___x_5471_ = v___x_5468_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
                    v___x_5471_ = v_reuseFailAlloc_5472_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getType___boxed(
    mut v_fvarId_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
    mut v_a_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ =
        l_Lean_Compiler_LCNF_getType(v_fvarId_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_);
    crate::leanh::lean_dec(v_a_5478_);
    crate::leanh::lean_dec_ref(v_a_5477_);
    crate::leanh::lean_dec(v_a_5476_);
    crate::leanh::lean_dec_ref(v_a_5475_);
    return v_res_5480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(
    mut v_00_u03b2_5481_: *mut crate::leanh::LeanObject,
    mut v_m_5482_: *mut crate::leanh::LeanObject,
    mut v_a_5483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_5482_, v_a_5483_);
    return v___x_5484_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(
    mut v_00_u03b2_5485_: *mut crate::leanh::LeanObject,
    mut v_m_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5488_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(
            v_00_u03b2_5485_,
            v_m_5486_,
            v_a_5487_,
        );
    crate::leanh::lean_dec(v_a_5487_);
    crate::leanh::lean_dec_ref(v_m_5486_);
    return v_res_5488_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(
    mut v_00_u03b2_5489_: *mut crate::leanh::LeanObject,
    mut v_a_5490_: *mut crate::leanh::LeanObject,
    mut v_x_5491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5492_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_5490_, v_x_5491_);
    return v___x_5492_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(
    mut v_00_u03b2_5493_: *mut crate::leanh::LeanObject,
    mut v_a_5494_: *mut crate::leanh::LeanObject,
    mut v_x_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_5493_, v_a_5494_, v_x_5495_);
    crate::leanh::lean_dec(v_x_5495_);
    crate::leanh::lean_dec(v_a_5494_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBinderName(
    mut v_fvarId_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: *mut crate::leanh::LeanObject,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
    mut v_a_5500_: *mut crate::leanh::LeanObject,
    mut v_a_5501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5508_: u8 = 0;
    let mut v___y_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v_binderName_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5533_: u8 = 0;
    let mut v___x_5534_: u8 = 0;
    let mut v_funDeclsPure_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v_binderName_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut v___x_5549_: u8 = 0;
    let mut v_paramsPure_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v_letDeclsPure_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_a_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5503_ = lean_st_ref_get(v_a_5499_);
                v___x_5504_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5498_);
                if crate::leanh::lean_obj_tag(v___x_5504_) == 0 {
                    v_a_5505_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5555_ = (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5555_ == 0 {
                        v___x_5507_ = v___x_5504_;
                        v_isShared_5508_ = v_isSharedCheck_5555_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5505_);
                        crate::leanh::lean_dec(v___x_5504_);
                        v___x_5507_ = crate::leanh::lean_box(0);
                        v_isShared_5508_ = v_isSharedCheck_5555_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5503_);
                    crate::leanh::lean_dec(v_fvarId_5497_);
                    v_a_5556_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5563_ = (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5563_ == 0 {
                        v___x_5558_ = v___x_5504_;
                        v_isShared_5559_ = v_isSharedCheck_5563_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5556_);
                        crate::leanh::lean_dec(v___x_5504_);
                        v___x_5558_ = crate::leanh::lean_box(0);
                        v_isShared_5559_ = v_isSharedCheck_5563_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_5521_ = crate::leanh::lean_ctor_get(v___x_5503_, 0);
                crate::leanh::lean_inc_ref(v_lctx_5521_);
                crate::leanh::lean_dec(v___x_5503_);
                v___x_5552_ = (crate::leanh::lean_unbox(v_a_5505_) as u8);
                if v___x_5552_ == 0 {
                    v_letDeclsPure_5553_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 2);
                    crate::leanh::lean_inc_ref(v_letDeclsPure_5553_);
                    v___y_5538_ = v_letDeclsPure_5553_;
                    state = 7;
                    continue;
                } else {
                    v_letDeclsImpure_5554_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 3);
                    crate::leanh::lean_inc_ref(v_letDeclsImpure_5554_);
                    v___y_5538_ = v_letDeclsImpure_5554_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_5511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5510_, v_fvarId_5497_);
                crate::leanh::lean_dec_ref(v___y_5510_);
                if crate::leanh::lean_obj_tag(v___x_5511_) == 1 {
                    crate::leanh::lean_dec(v_fvarId_5497_);
                    v_val_5512_ = crate::leanh::lean_ctor_get(v___x_5511_, 0);
                    crate::leanh::lean_inc(v_val_5512_);
                    crate::leanh::lean_dec_ref_known(v___x_5511_, 1);
                    v_binderName_5513_ = crate::leanh::lean_ctor_get(v_val_5512_, 1);
                    crate::leanh::lean_inc(v_binderName_5513_);
                    crate::leanh::lean_dec(v_val_5512_);
                    if v_isShared_5508_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5507_, 0, v_binderName_5513_);
                        v___x_5515_ = v___x_5507_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_binderName_5513_);
                        v___x_5515_ = v_reuseFailAlloc_5516_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5511_);
                    crate::leanh::lean_del_object(v___x_5507_);
                    v___x_5517_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getType___closed__1,
                    );
                    v___x_5518_ = l_Lean_MessageData_ofName(v_fvarId_5497_);
                    v___x_5519_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5519_, 0, v___x_5517_);
                    crate::leanh::lean_ctor_set(v___x_5519_, 1, v___x_5518_);
                    v___x_5520_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
                            v___x_5519_,
                            v_a_5498_,
                            v_a_5499_,
                            v_a_5500_,
                            v_a_5501_,
                        );
                    return v___x_5520_;
                }
            }
            3 => {
                return v___x_5515_;
            }
            4 => {
                v___x_5524_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5523_, v_fvarId_5497_);
                crate::leanh::lean_dec_ref(v___y_5523_);
                if crate::leanh::lean_obj_tag(v___x_5524_) == 1 {
                    crate::leanh::lean_dec_ref(v_lctx_5521_);
                    crate::leanh::lean_del_object(v___x_5507_);
                    crate::leanh::lean_dec(v_a_5505_);
                    crate::leanh::lean_dec(v_fvarId_5497_);
                    v_val_5525_ = crate::leanh::lean_ctor_get(v___x_5524_, 0);
                    v_isSharedCheck_5533_ = (!crate::leanh::lean_is_exclusive(v___x_5524_)) as u8;
                    if v_isSharedCheck_5533_ == 0 {
                        v___x_5527_ = v___x_5524_;
                        v_isShared_5528_ = v_isSharedCheck_5533_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5525_);
                        crate::leanh::lean_dec(v___x_5524_);
                        v___x_5527_ = crate::leanh::lean_box(0);
                        v_isShared_5528_ = v_isSharedCheck_5533_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5524_);
                    v___x_5534_ = (crate::leanh::lean_unbox(v_a_5505_) as u8);
                    crate::leanh::lean_dec(v_a_5505_);
                    if v___x_5534_ == 0 {
                        v_funDeclsPure_5535_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 4);
                        crate::leanh::lean_inc_ref(v_funDeclsPure_5535_);
                        crate::leanh::lean_dec_ref(v_lctx_5521_);
                        v___y_5510_ = v_funDeclsPure_5535_;
                        state = 2;
                        continue;
                    } else {
                        v_funDeclsImpure_5536_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 5);
                        crate::leanh::lean_inc_ref(v_funDeclsImpure_5536_);
                        crate::leanh::lean_dec_ref(v_lctx_5521_);
                        v___y_5510_ = v_funDeclsImpure_5536_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_binderName_5529_ = crate::leanh::lean_ctor_get(v_val_5525_, 1);
                crate::leanh::lean_inc(v_binderName_5529_);
                crate::leanh::lean_dec(v_val_5525_);
                if v_isShared_5528_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5527_, 0);
                    crate::leanh::lean_ctor_set(v___x_5527_, 0, v_binderName_5529_);
                    v___x_5531_ = v___x_5527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_binderName_5529_);
                    v___x_5531_ = v_reuseFailAlloc_5532_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5531_;
            }
            7 => {
                v___x_5539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5538_, v_fvarId_5497_);
                crate::leanh::lean_dec_ref(v___y_5538_);
                if crate::leanh::lean_obj_tag(v___x_5539_) == 1 {
                    crate::leanh::lean_dec_ref(v_lctx_5521_);
                    crate::leanh::lean_del_object(v___x_5507_);
                    crate::leanh::lean_dec(v_a_5505_);
                    crate::leanh::lean_dec(v_fvarId_5497_);
                    v_val_5540_ = crate::leanh::lean_ctor_get(v___x_5539_, 0);
                    v_isSharedCheck_5548_ = (!crate::leanh::lean_is_exclusive(v___x_5539_)) as u8;
                    if v_isSharedCheck_5548_ == 0 {
                        v___x_5542_ = v___x_5539_;
                        v_isShared_5543_ = v_isSharedCheck_5548_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5540_);
                        crate::leanh::lean_dec(v___x_5539_);
                        v___x_5542_ = crate::leanh::lean_box(0);
                        v_isShared_5543_ = v_isSharedCheck_5548_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5539_);
                    v___x_5549_ = (crate::leanh::lean_unbox(v_a_5505_) as u8);
                    if v___x_5549_ == 0 {
                        v_paramsPure_5550_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 0);
                        crate::leanh::lean_inc_ref(v_paramsPure_5550_);
                        v___y_5523_ = v_paramsPure_5550_;
                        state = 4;
                        continue;
                    } else {
                        v_paramsImpure_5551_ = crate::leanh::lean_ctor_get(v_lctx_5521_, 1);
                        crate::leanh::lean_inc_ref(v_paramsImpure_5551_);
                        v___y_5523_ = v_paramsImpure_5551_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v_binderName_5544_ = crate::leanh::lean_ctor_get(v_val_5540_, 1);
                crate::leanh::lean_inc(v_binderName_5544_);
                crate::leanh::lean_dec(v_val_5540_);
                if v_isShared_5543_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5542_, 0);
                    crate::leanh::lean_ctor_set(v___x_5542_, 0, v_binderName_5544_);
                    v___x_5546_ = v___x_5542_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_binderName_5544_);
                    v___x_5546_ = v_reuseFailAlloc_5547_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5546_;
            }
            10 => {
                if v_isShared_5559_ == 0 {
                    v___x_5561_ = v___x_5558_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
                    v___x_5561_ = v_reuseFailAlloc_5562_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getBinderName___boxed(
    mut v_fvarId_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
    mut v_a_5568_: *mut crate::leanh::LeanObject,
    mut v_a_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Lean_Compiler_LCNF_getBinderName(
        v_fvarId_5564_,
        v_a_5565_,
        v_a_5566_,
        v_a_5567_,
        v_a_5568_,
    );
    crate::leanh::lean_dec(v_a_5568_);
    crate::leanh::lean_dec_ref(v_a_5567_);
    crate::leanh::lean_dec(v_a_5566_);
    crate::leanh::lean_dec_ref(v_a_5565_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___redArg(
    mut v_pu_5571_: u8,
    mut v_fvarId_5572_: *mut crate::leanh::LeanObject,
    mut v_a_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5575_ = lean_st_ref_get(v_a_5573_);
                if v_pu_5571_ == 0 {
                    v_lctx_5580_ = crate::leanh::lean_ctor_get(v___x_5575_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5580_);
                    crate::leanh::lean_dec(v___x_5575_);
                    v_paramsPure_5581_ = crate::leanh::lean_ctor_get(v_lctx_5580_, 0);
                    crate::leanh::lean_inc_ref(v_paramsPure_5581_);
                    crate::leanh::lean_dec_ref(v_lctx_5580_);
                    v___y_5577_ = v_paramsPure_5581_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5582_ = crate::leanh::lean_ctor_get(v___x_5575_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5582_);
                    crate::leanh::lean_dec(v___x_5575_);
                    v_paramsImpure_5583_ = crate::leanh::lean_ctor_get(v_lctx_5582_, 1);
                    crate::leanh::lean_inc_ref(v_paramsImpure_5583_);
                    crate::leanh::lean_dec_ref(v_lctx_5582_);
                    v___y_5577_ = v_paramsImpure_5583_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5577_, v_fvarId_5572_);
                crate::leanh::lean_dec_ref(v___y_5577_);
                v___x_5579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5579_, 0, v___x_5578_);
                return v___x_5579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(
    mut v_pu_5584_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5585_: *mut crate::leanh::LeanObject,
    mut v_a_5586_: *mut crate::leanh::LeanObject,
    mut v_a_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5588_: u8 = 0;
    let mut v_res_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5588_ = (crate::leanh::lean_unbox(v_pu_5584_) as u8);
    v_res_5589_ =
        l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_5588_, v_fvarId_5585_, v_a_5586_);
    crate::leanh::lean_dec(v_a_5586_);
    crate::leanh::lean_dec(v_fvarId_5585_);
    return v_res_5589_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f(
    mut v_pu_5590_: u8,
    mut v_fvarId_5591_: *mut crate::leanh::LeanObject,
    mut v_a_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
    mut v_a_5594_: *mut crate::leanh::LeanObject,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5597_ =
        l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_5590_, v_fvarId_5591_, v_a_5593_);
    return v___x_5597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___boxed(
    mut v_pu_5598_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
    mut v_a_5601_: *mut crate::leanh::LeanObject,
    mut v_a_5602_: *mut crate::leanh::LeanObject,
    mut v_a_5603_: *mut crate::leanh::LeanObject,
    mut v_a_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5605_: u8 = 0;
    let mut v_res_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5605_ = (crate::leanh::lean_unbox(v_pu_5598_) as u8);
    v_res_5606_ = l_Lean_Compiler_LCNF_findParam_x3f(
        v_pu_boxed_5605_,
        v_fvarId_5599_,
        v_a_5600_,
        v_a_5601_,
        v_a_5602_,
        v_a_5603_,
    );
    crate::leanh::lean_dec(v_a_5603_);
    crate::leanh::lean_dec_ref(v_a_5602_);
    crate::leanh::lean_dec(v_a_5601_);
    crate::leanh::lean_dec_ref(v_a_5600_);
    crate::leanh::lean_dec(v_fvarId_5599_);
    return v_res_5606_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
    mut v_pu_5607_: u8,
    mut v_fvarId_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5611_ = lean_st_ref_get(v_a_5609_);
                if v_pu_5607_ == 0 {
                    v_lctx_5616_ = crate::leanh::lean_ctor_get(v___x_5611_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5616_);
                    crate::leanh::lean_dec(v___x_5611_);
                    v_letDeclsPure_5617_ = crate::leanh::lean_ctor_get(v_lctx_5616_, 2);
                    crate::leanh::lean_inc_ref(v_letDeclsPure_5617_);
                    crate::leanh::lean_dec_ref(v_lctx_5616_);
                    v___y_5613_ = v_letDeclsPure_5617_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5618_ = crate::leanh::lean_ctor_get(v___x_5611_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5618_);
                    crate::leanh::lean_dec(v___x_5611_);
                    v_letDeclsImpure_5619_ = crate::leanh::lean_ctor_get(v_lctx_5618_, 3);
                    crate::leanh::lean_inc_ref(v_letDeclsImpure_5619_);
                    crate::leanh::lean_dec_ref(v_lctx_5618_);
                    v___y_5613_ = v_letDeclsImpure_5619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5613_, v_fvarId_5608_);
                crate::leanh::lean_dec_ref(v___y_5613_);
                v___x_5615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5615_, 0, v___x_5614_);
                return v___x_5615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(
    mut v_pu_5620_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5621_: *mut crate::leanh::LeanObject,
    mut v_a_5622_: *mut crate::leanh::LeanObject,
    mut v_a_5623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5624_: u8 = 0;
    let mut v_res_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5624_ = (crate::leanh::lean_unbox(v_pu_5620_) as u8);
    v_res_5625_ =
        l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_5624_, v_fvarId_5621_, v_a_5622_);
    crate::leanh::lean_dec(v_a_5622_);
    crate::leanh::lean_dec(v_fvarId_5621_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f(
    mut v_pu_5626_: u8,
    mut v_fvarId_5627_: *mut crate::leanh::LeanObject,
    mut v_a_5628_: *mut crate::leanh::LeanObject,
    mut v_a_5629_: *mut crate::leanh::LeanObject,
    mut v_a_5630_: *mut crate::leanh::LeanObject,
    mut v_a_5631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5633_ =
        l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_5626_, v_fvarId_5627_, v_a_5629_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(
    mut v_pu_5634_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
    mut v_a_5637_: *mut crate::leanh::LeanObject,
    mut v_a_5638_: *mut crate::leanh::LeanObject,
    mut v_a_5639_: *mut crate::leanh::LeanObject,
    mut v_a_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5641_: u8 = 0;
    let mut v_res_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5641_ = (crate::leanh::lean_unbox(v_pu_5634_) as u8);
    v_res_5642_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(
        v_pu_boxed_5641_,
        v_fvarId_5635_,
        v_a_5636_,
        v_a_5637_,
        v_a_5638_,
        v_a_5639_,
    );
    crate::leanh::lean_dec(v_a_5639_);
    crate::leanh::lean_dec_ref(v_a_5638_);
    crate::leanh::lean_dec(v_a_5637_);
    crate::leanh::lean_dec_ref(v_a_5636_);
    crate::leanh::lean_dec(v_fvarId_5635_);
    return v_res_5642_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
    mut v_pu_5643_: u8,
    mut v_fvarId_5644_: *mut crate::leanh::LeanObject,
    mut v_a_5645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5647_ = lean_st_ref_get(v_a_5645_);
                if v_pu_5643_ == 0 {
                    v_lctx_5652_ = crate::leanh::lean_ctor_get(v___x_5647_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5652_);
                    crate::leanh::lean_dec(v___x_5647_);
                    v_funDeclsPure_5653_ = crate::leanh::lean_ctor_get(v_lctx_5652_, 4);
                    crate::leanh::lean_inc_ref(v_funDeclsPure_5653_);
                    crate::leanh::lean_dec_ref(v_lctx_5652_);
                    v___y_5649_ = v_funDeclsPure_5653_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5654_ = crate::leanh::lean_ctor_get(v___x_5647_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_5654_);
                    crate::leanh::lean_dec(v___x_5647_);
                    v_funDeclsImpure_5655_ = crate::leanh::lean_ctor_get(v_lctx_5654_, 5);
                    crate::leanh::lean_inc_ref(v_funDeclsImpure_5655_);
                    crate::leanh::lean_dec_ref(v_lctx_5654_);
                    v___y_5649_ = v_funDeclsImpure_5655_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5649_, v_fvarId_5644_);
                crate::leanh::lean_dec_ref(v___y_5649_);
                v___x_5651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5651_, 0, v___x_5650_);
                return v___x_5651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(
    mut v_pu_5656_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
    mut v_a_5659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5660_: u8 = 0;
    let mut v_res_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5660_ = (crate::leanh::lean_unbox(v_pu_5656_) as u8);
    v_res_5661_ =
        l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_5660_, v_fvarId_5657_, v_a_5658_);
    crate::leanh::lean_dec(v_a_5658_);
    crate::leanh::lean_dec(v_fvarId_5657_);
    return v_res_5661_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f(
    mut v_pu_5662_: u8,
    mut v_fvarId_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
    mut v_a_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5669_ =
        l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_5662_, v_fvarId_5663_, v_a_5665_);
    return v___x_5669_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(
    mut v_pu_5670_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5671_: *mut crate::leanh::LeanObject,
    mut v_a_5672_: *mut crate::leanh::LeanObject,
    mut v_a_5673_: *mut crate::leanh::LeanObject,
    mut v_a_5674_: *mut crate::leanh::LeanObject,
    mut v_a_5675_: *mut crate::leanh::LeanObject,
    mut v_a_5676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5677_: u8 = 0;
    let mut v_res_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5677_ = (crate::leanh::lean_unbox(v_pu_5670_) as u8);
    v_res_5678_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(
        v_pu_boxed_5677_,
        v_fvarId_5671_,
        v_a_5672_,
        v_a_5673_,
        v_a_5674_,
        v_a_5675_,
    );
    crate::leanh::lean_dec(v_a_5675_);
    crate::leanh::lean_dec_ref(v_a_5674_);
    crate::leanh::lean_dec(v_a_5673_);
    crate::leanh::lean_dec_ref(v_a_5672_);
    crate::leanh::lean_dec(v_fvarId_5671_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
    mut v_pu_5679_: u8,
    mut v_fvarId_5680_: *mut crate::leanh::LeanObject,
    mut v_a_5681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v_val_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v_value_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5699_: u8 = 0;
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5683_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v_pu_5679_,
                    v_fvarId_5680_,
                    v_a_5681_,
                );
                v_a_5684_ = crate::leanh::lean_ctor_get(v___x_5683_, 0);
                v_isSharedCheck_5704_ = (!crate::leanh::lean_is_exclusive(v___x_5683_)) as u8;
                if v_isSharedCheck_5704_ == 0 {
                    v___x_5686_ = v___x_5683_;
                    v_isShared_5687_ = v_isSharedCheck_5704_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5684_);
                    crate::leanh::lean_dec(v___x_5683_);
                    v___x_5686_ = crate::leanh::lean_box(0);
                    v_isShared_5687_ = v_isSharedCheck_5704_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5684_) == 1 {
                    v_val_5688_ = crate::leanh::lean_ctor_get(v_a_5684_, 0);
                    v_isSharedCheck_5699_ = (!crate::leanh::lean_is_exclusive(v_a_5684_)) as u8;
                    if v_isSharedCheck_5699_ == 0 {
                        v___x_5690_ = v_a_5684_;
                        v_isShared_5691_ = v_isSharedCheck_5699_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5688_);
                        crate::leanh::lean_dec(v_a_5684_);
                        v___x_5690_ = crate::leanh::lean_box(0);
                        v_isShared_5691_ = v_isSharedCheck_5699_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5684_);
                    v___x_5700_ = crate::leanh::lean_box(0);
                    if v_isShared_5687_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5700_);
                        v___x_5702_ = v___x_5686_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5700_);
                        v___x_5702_ = v_reuseFailAlloc_5703_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_value_5692_ = crate::leanh::lean_ctor_get(v_val_5688_, 3);
                crate::leanh::lean_inc(v_value_5692_);
                crate::leanh::lean_dec(v_val_5688_);
                if v_isShared_5691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5690_, 0, v_value_5692_);
                    v___x_5694_ = v___x_5690_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_value_5692_);
                    v___x_5694_ = v_reuseFailAlloc_5698_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5694_);
                    v___x_5696_ = v___x_5686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5694_);
                    v___x_5696_ = v_reuseFailAlloc_5697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5696_;
            }
            5 => {
                return v___x_5702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f___redArg___boxed(
    mut v_pu_5705_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5709_: u8 = 0;
    let mut v_res_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5709_ = (crate::leanh::lean_unbox(v_pu_5705_) as u8);
    v_res_5710_ =
        l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_5709_, v_fvarId_5706_, v_a_5707_);
    crate::leanh::lean_dec(v_a_5707_);
    crate::leanh::lean_dec(v_fvarId_5706_);
    return v_res_5710_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f(
    mut v_pu_5711_: u8,
    mut v_fvarId_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_a_5716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5718_ =
        l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_5711_, v_fvarId_5712_, v_a_5714_);
    return v___x_5718_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(
    mut v_pu_5719_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5720_: *mut crate::leanh::LeanObject,
    mut v_a_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
    mut v_a_5725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5726_: u8 = 0;
    let mut v_res_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5726_ = (crate::leanh::lean_unbox(v_pu_5719_) as u8);
    v_res_5727_ = l_Lean_Compiler_LCNF_findLetValue_x3f(
        v_pu_boxed_5726_,
        v_fvarId_5720_,
        v_a_5721_,
        v_a_5722_,
        v_a_5723_,
        v_a_5724_,
    );
    crate::leanh::lean_dec(v_a_5724_);
    crate::leanh::lean_dec_ref(v_a_5723_);
    crate::leanh::lean_dec(v_a_5722_);
    crate::leanh::lean_dec_ref(v_a_5721_);
    crate::leanh::lean_dec(v_fvarId_5720_);
    return v_res_5727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp___redArg(
    mut v_fvarId_5728_: *mut crate::leanh::LeanObject,
    mut v_a_5729_: *mut crate::leanh::LeanObject,
    mut v_a_5730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5732_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5737_: u8 = 0;
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5747_: u8 = 0;
    let mut v_declName_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: u8 = 0;
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5765_: u8 = 0;
    let mut v_unused_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5771_: u8 = 0;
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5776_: u8 = 0;
    let mut v_isSharedCheck_5777_: u8 = 0;
    let mut v_a_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5732_ = 0;
                v___x_5733_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_5732_,
                    v_fvarId_5728_,
                    v_a_5729_,
                );
                if crate::leanh::lean_obj_tag(v___x_5733_) == 0 {
                    v_a_5734_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5777_ = (!crate::leanh::lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5777_ == 0 {
                        v___x_5736_ = v___x_5733_;
                        v_isShared_5737_ = v_isSharedCheck_5777_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5734_);
                        crate::leanh::lean_dec(v___x_5733_);
                        v___x_5736_ = crate::leanh::lean_box(0);
                        v_isShared_5737_ = v_isSharedCheck_5777_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5778_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5785_ = (!crate::leanh::lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5785_ == 0 {
                        v___x_5780_ = v___x_5733_;
                        v_isShared_5781_ = v_isSharedCheck_5785_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5778_);
                        crate::leanh::lean_dec(v___x_5733_);
                        v___x_5780_ = crate::leanh::lean_box(0);
                        v_isShared_5781_ = v_isSharedCheck_5785_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5734_) == 1 {
                    v_val_5744_ = crate::leanh::lean_ctor_get(v_a_5734_, 0);
                    v_isSharedCheck_5776_ = (!crate::leanh::lean_is_exclusive(v_a_5734_)) as u8;
                    if v_isSharedCheck_5776_ == 0 {
                        v___x_5746_ = v_a_5734_;
                        v_isShared_5747_ = v_isSharedCheck_5776_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5744_);
                        crate::leanh::lean_dec(v_a_5734_);
                        v___x_5746_ = crate::leanh::lean_box(0);
                        v_isShared_5747_ = v_isSharedCheck_5776_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5734_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5739_ = 0;
                v___x_5740_ = crate::leanh::lean_box((v___x_5739_) as usize);
                if v_isShared_5737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5736_, 0, v___x_5740_);
                    v___x_5742_ = v___x_5736_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5740_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5742_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_val_5744_) == 3 {
                    crate::leanh::lean_del_object(v___x_5736_);
                    v_declName_5748_ = crate::leanh::lean_ctor_get(v_val_5744_, 0);
                    crate::leanh::lean_inc(v_declName_5748_);
                    crate::leanh::lean_dec_ref_known(v_val_5744_, 3);
                    v___x_5749_ = lean_st_ref_get(v_a_5730_);
                    v_env_5750_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                    crate::leanh::lean_inc_ref(v_env_5750_);
                    crate::leanh::lean_dec(v___x_5749_);
                    v___x_5751_ = 0;
                    v___x_5752_ =
                        l_Lean_Environment_find_x3f(v_env_5750_, v_declName_5748_, v___x_5751_);
                    if crate::leanh::lean_obj_tag(v___x_5752_) == 1 {
                        crate::leanh::lean_del_object(v___x_5746_);
                        v_val_5753_ = crate::leanh::lean_ctor_get(v___x_5752_, 0);
                        v_isSharedCheck_5771_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5752_)) as u8;
                        if v_isSharedCheck_5771_ == 0 {
                            v___x_5755_ = v___x_5752_;
                            v_isShared_5756_ = v_isSharedCheck_5771_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5753_);
                            crate::leanh::lean_dec(v___x_5752_);
                            v___x_5755_ = crate::leanh::lean_box(0);
                            v_isShared_5756_ = v_isSharedCheck_5771_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5752_);
                        v___x_5772_ = crate::leanh::lean_box((v___x_5751_) as usize);
                        if v_isShared_5747_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5746_, 0);
                            crate::leanh::lean_ctor_set(v___x_5746_, 0, v___x_5772_);
                            v___x_5774_ = v___x_5746_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_5775_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
                            v___x_5774_ = v_reuseFailAlloc_5775_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5746_);
                    crate::leanh::lean_dec(v_val_5744_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_val_5753_) == 6 {
                    crate::leanh::lean_del_object(v___x_5755_);
                    v_isSharedCheck_5765_ = (!crate::leanh::lean_is_exclusive(v_val_5753_)) as u8;
                    if v_isSharedCheck_5765_ == 0 {
                        v_unused_5766_ = crate::leanh::lean_ctor_get(v_val_5753_, 0);
                        crate::leanh::lean_dec(v_unused_5766_);
                        v___x_5758_ = v_val_5753_;
                        v_isShared_5759_ = v_isSharedCheck_5765_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_5753_);
                        v___x_5758_ = crate::leanh::lean_box(0);
                        v_isShared_5759_ = v_isSharedCheck_5765_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_5753_);
                    v___x_5767_ = crate::leanh::lean_box((v___x_5751_) as usize);
                    if v_isShared_5756_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5755_, 0);
                        crate::leanh::lean_ctor_set(v___x_5755_, 0, v___x_5767_);
                        v___x_5769_ = v___x_5755_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
                        v___x_5769_ = v_reuseFailAlloc_5770_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5760_ = 1;
                v___x_5761_ = crate::leanh::lean_box((v___x_5760_) as usize);
                if v_isShared_5759_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5758_, 0);
                    crate::leanh::lean_ctor_set(v___x_5758_, 0, v___x_5761_);
                    v___x_5763_ = v___x_5758_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
                    v___x_5763_ = v_reuseFailAlloc_5764_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5763_;
            }
            8 => {
                return v___x_5769_;
            }
            9 => {
                return v___x_5774_;
            }
            10 => {
                if v_isShared_5781_ == 0 {
                    v___x_5783_ = v___x_5780_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
                    v___x_5783_ = v_reuseFailAlloc_5784_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp___redArg___boxed(
    mut v_fvarId_5786_: *mut crate::leanh::LeanObject,
    mut v_a_5787_: *mut crate::leanh::LeanObject,
    mut v_a_5788_: *mut crate::leanh::LeanObject,
    mut v_a_5789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ =
        l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5786_, v_a_5787_, v_a_5788_);
    crate::leanh::lean_dec(v_a_5788_);
    crate::leanh::lean_dec(v_a_5787_);
    crate::leanh::lean_dec(v_fvarId_5786_);
    return v_res_5790_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp(
    mut v_fvarId_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
    mut v_a_5793_: *mut crate::leanh::LeanObject,
    mut v_a_5794_: *mut crate::leanh::LeanObject,
    mut v_a_5795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5797_ =
        l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5791_, v_a_5793_, v_a_5795_);
    return v___x_5797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp___boxed(
    mut v_fvarId_5798_: *mut crate::leanh::LeanObject,
    mut v_a_5799_: *mut crate::leanh::LeanObject,
    mut v_a_5800_: *mut crate::leanh::LeanObject,
    mut v_a_5801_: *mut crate::leanh::LeanObject,
    mut v_a_5802_: *mut crate::leanh::LeanObject,
    mut v_a_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5804_ = l_Lean_Compiler_LCNF_isConstructorApp(
        v_fvarId_5798_,
        v_a_5799_,
        v_a_5800_,
        v_a_5801_,
        v_a_5802_,
    );
    crate::leanh::lean_dec(v_a_5802_);
    crate::leanh::lean_dec_ref(v_a_5801_);
    crate::leanh::lean_dec(v_a_5800_);
    crate::leanh::lean_dec_ref(v_a_5799_);
    crate::leanh::lean_dec(v_fvarId_5798_);
    return v_res_5804_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(
    mut v_arg_5805_: *mut crate::leanh::LeanObject,
    mut v_a_5806_: *mut crate::leanh::LeanObject,
    mut v_a_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_arg_5805_) == 1 {
        let mut v_fvarId_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_5809_ = crate::leanh::lean_ctor_get(v_arg_5805_, 0);
        v___x_5810_ =
            l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5809_, v_a_5806_, v_a_5807_);
        return v___x_5810_;
    } else {
        let mut v___x_5811_: u8 = 0;
        let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5811_ = 0;
        v___x_5812_ = crate::leanh::lean_box((v___x_5811_) as usize);
        v___x_5813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5813_, 0, v___x_5812_);
        return v___x_5813_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(
    mut v_arg_5814_: *mut crate::leanh::LeanObject,
    mut v_a_5815_: *mut crate::leanh::LeanObject,
    mut v_a_5816_: *mut crate::leanh::LeanObject,
    mut v_a_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5818_ =
        l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_5814_, v_a_5815_, v_a_5816_);
    crate::leanh::lean_dec(v_a_5816_);
    crate::leanh::lean_dec(v_a_5815_);
    crate::leanh::lean_dec(v_arg_5814_);
    return v_res_5818_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp(
    mut v_pu_5819_: u8,
    mut v_arg_5820_: *mut crate::leanh::LeanObject,
    mut v_a_5821_: *mut crate::leanh::LeanObject,
    mut v_a_5822_: *mut crate::leanh::LeanObject,
    mut v_a_5823_: *mut crate::leanh::LeanObject,
    mut v_a_5824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5826_ =
        l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_5820_, v_a_5822_, v_a_5824_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(
    mut v_pu_5827_: *mut crate::leanh::LeanObject,
    mut v_arg_5828_: *mut crate::leanh::LeanObject,
    mut v_a_5829_: *mut crate::leanh::LeanObject,
    mut v_a_5830_: *mut crate::leanh::LeanObject,
    mut v_a_5831_: *mut crate::leanh::LeanObject,
    mut v_a_5832_: *mut crate::leanh::LeanObject,
    mut v_a_5833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5834_ = (crate::leanh::lean_unbox(v_pu_5827_) as u8);
    v_res_5835_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(
        v_pu_boxed_5834_,
        v_arg_5828_,
        v_a_5829_,
        v_a_5830_,
        v_a_5831_,
        v_a_5832_,
    );
    crate::leanh::lean_dec(v_a_5832_);
    crate::leanh::lean_dec_ref(v_a_5831_);
    crate::leanh::lean_dec(v_a_5830_);
    crate::leanh::lean_dec_ref(v_a_5829_);
    crate::leanh::lean_dec(v_arg_5828_);
    return v_res_5835_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getParam___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_Compiler_LCNF_getParam___closed__0;
    v___x_5838_ = l_Lean_stringToMessageData(v___x_5837_);
    return v___x_5838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getParam(
    mut v_pu_5839_: u8,
    mut v_fvarId_5840_: *mut crate::leanh::LeanObject,
    mut v_a_5841_: *mut crate::leanh::LeanObject,
    mut v_a_5842_: *mut crate::leanh::LeanObject,
    mut v_a_5843_: *mut crate::leanh::LeanObject,
    mut v_a_5844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5850_: u8 = 0;
    let mut v_val_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5846_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(
                    v_pu_5839_,
                    v_fvarId_5840_,
                    v_a_5842_,
                );
                v_a_5847_ = crate::leanh::lean_ctor_get(v___x_5846_, 0);
                v_isSharedCheck_5859_ = (!crate::leanh::lean_is_exclusive(v___x_5846_)) as u8;
                if v_isSharedCheck_5859_ == 0 {
                    v___x_5849_ = v___x_5846_;
                    v_isShared_5850_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5847_);
                    crate::leanh::lean_dec(v___x_5846_);
                    v___x_5849_ = crate::leanh::lean_box(0);
                    v_isShared_5850_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5847_) == 1 {
                    crate::leanh::lean_dec(v_fvarId_5840_);
                    v_val_5851_ = crate::leanh::lean_ctor_get(v_a_5847_, 0);
                    crate::leanh::lean_inc(v_val_5851_);
                    crate::leanh::lean_dec_ref_known(v_a_5847_, 1);
                    if v_isShared_5850_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5849_, 0, v_val_5851_);
                        v___x_5853_ = v___x_5849_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_val_5851_);
                        v___x_5853_ = v_reuseFailAlloc_5854_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5849_);
                    crate::leanh::lean_dec(v_a_5847_);
                    v___x_5855_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getParam___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getParam___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getParam___closed__1,
                    );
                    v___x_5856_ = l_Lean_MessageData_ofName(v_fvarId_5840_);
                    v___x_5857_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5857_, 0, v___x_5855_);
                    crate::leanh::lean_ctor_set(v___x_5857_, 1, v___x_5856_);
                    v___x_5858_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
                            v___x_5857_,
                            v_a_5841_,
                            v_a_5842_,
                            v_a_5843_,
                            v_a_5844_,
                        );
                    return v___x_5858_;
                }
            }
            2 => {
                return v___x_5853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getParam___boxed(
    mut v_pu_5860_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5861_: *mut crate::leanh::LeanObject,
    mut v_a_5862_: *mut crate::leanh::LeanObject,
    mut v_a_5863_: *mut crate::leanh::LeanObject,
    mut v_a_5864_: *mut crate::leanh::LeanObject,
    mut v_a_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5867_: u8 = 0;
    let mut v_res_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5867_ = (crate::leanh::lean_unbox(v_pu_5860_) as u8);
    v_res_5868_ = l_Lean_Compiler_LCNF_getParam(
        v_pu_boxed_5867_,
        v_fvarId_5861_,
        v_a_5862_,
        v_a_5863_,
        v_a_5864_,
        v_a_5865_,
    );
    crate::leanh::lean_dec(v_a_5865_);
    crate::leanh::lean_dec_ref(v_a_5864_);
    crate::leanh::lean_dec(v_a_5863_);
    crate::leanh::lean_dec_ref(v_a_5862_);
    return v_res_5868_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5870_ = l_Lean_Compiler_LCNF_getLetDecl___closed__0;
    v___x_5871_ = l_Lean_stringToMessageData(v___x_5870_);
    return v___x_5871_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLetDecl(
    mut v_pu_5872_: u8,
    mut v_fvarId_5873_: *mut crate::leanh::LeanObject,
    mut v_a_5874_: *mut crate::leanh::LeanObject,
    mut v_a_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
    mut v_a_5877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v_val_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5879_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v_pu_5872_,
                    v_fvarId_5873_,
                    v_a_5875_,
                );
                v_a_5880_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                v_isSharedCheck_5892_ = (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                if v_isSharedCheck_5892_ == 0 {
                    v___x_5882_ = v___x_5879_;
                    v_isShared_5883_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5880_);
                    crate::leanh::lean_dec(v___x_5879_);
                    v___x_5882_ = crate::leanh::lean_box(0);
                    v_isShared_5883_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5880_) == 1 {
                    crate::leanh::lean_dec(v_fvarId_5873_);
                    v_val_5884_ = crate::leanh::lean_ctor_get(v_a_5880_, 0);
                    crate::leanh::lean_inc(v_val_5884_);
                    crate::leanh::lean_dec_ref_known(v_a_5880_, 1);
                    if v_isShared_5883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5882_, 0, v_val_5884_);
                        v___x_5886_ = v___x_5882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_val_5884_);
                        v___x_5886_ = v_reuseFailAlloc_5887_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5882_);
                    crate::leanh::lean_dec(v_a_5880_);
                    v___x_5888_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getLetDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getLetDecl___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1,
                    );
                    v___x_5889_ = l_Lean_MessageData_ofName(v_fvarId_5873_);
                    v___x_5890_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5890_, 0, v___x_5888_);
                    crate::leanh::lean_ctor_set(v___x_5890_, 1, v___x_5889_);
                    v___x_5891_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
                            v___x_5890_,
                            v_a_5874_,
                            v_a_5875_,
                            v_a_5876_,
                            v_a_5877_,
                        );
                    return v___x_5891_;
                }
            }
            2 => {
                return v___x_5886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getLetDecl___boxed(
    mut v_pu_5893_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5894_: *mut crate::leanh::LeanObject,
    mut v_a_5895_: *mut crate::leanh::LeanObject,
    mut v_a_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_a_5898_: *mut crate::leanh::LeanObject,
    mut v_a_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5900_: u8 = 0;
    let mut v_res_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5900_ = (crate::leanh::lean_unbox(v_pu_5893_) as u8);
    v_res_5901_ = l_Lean_Compiler_LCNF_getLetDecl(
        v_pu_boxed_5900_,
        v_fvarId_5894_,
        v_a_5895_,
        v_a_5896_,
        v_a_5897_,
        v_a_5898_,
    );
    crate::leanh::lean_dec(v_a_5898_);
    crate::leanh::lean_dec_ref(v_a_5897_);
    crate::leanh::lean_dec(v_a_5896_);
    crate::leanh::lean_dec_ref(v_a_5895_);
    return v_res_5901_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5903_ = l_Lean_Compiler_LCNF_getFunDecl___closed__0;
    v___x_5904_ = l_Lean_stringToMessageData(v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getFunDecl(
    mut v_pu_5905_: u8,
    mut v_fvarId_5906_: *mut crate::leanh::LeanObject,
    mut v_a_5907_: *mut crate::leanh::LeanObject,
    mut v_a_5908_: *mut crate::leanh::LeanObject,
    mut v_a_5909_: *mut crate::leanh::LeanObject,
    mut v_a_5910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_val_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                    v_pu_5905_,
                    v_fvarId_5906_,
                    v_a_5908_,
                );
                v_a_5913_ = crate::leanh::lean_ctor_get(v___x_5912_, 0);
                v_isSharedCheck_5925_ = (!crate::leanh::lean_is_exclusive(v___x_5912_)) as u8;
                if v_isSharedCheck_5925_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    v_isShared_5916_ = v_isSharedCheck_5925_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5913_);
                    crate::leanh::lean_dec(v___x_5912_);
                    v___x_5915_ = crate::leanh::lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5913_) == 1 {
                    crate::leanh::lean_dec(v_fvarId_5906_);
                    v_val_5917_ = crate::leanh::lean_ctor_get(v_a_5913_, 0);
                    crate::leanh::lean_inc(v_val_5917_);
                    crate::leanh::lean_dec_ref_known(v_a_5913_, 1);
                    if v_isShared_5916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5915_, 0, v_val_5917_);
                        v___x_5919_ = v___x_5915_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_val_5917_);
                        v___x_5919_ = v_reuseFailAlloc_5920_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5915_);
                    crate::leanh::lean_dec(v_a_5913_);
                    v___x_5921_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getFunDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getFunDecl___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1,
                    );
                    v___x_5922_ = l_Lean_MessageData_ofName(v_fvarId_5906_);
                    v___x_5923_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5923_, 0, v___x_5921_);
                    crate::leanh::lean_ctor_set(v___x_5923_, 1, v___x_5922_);
                    v___x_5924_ =
                        l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
                            v___x_5923_,
                            v_a_5907_,
                            v_a_5908_,
                            v_a_5909_,
                            v_a_5910_,
                        );
                    return v___x_5924_;
                }
            }
            2 => {
                return v___x_5919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getFunDecl___boxed(
    mut v_pu_5926_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5927_: *mut crate::leanh::LeanObject,
    mut v_a_5928_: *mut crate::leanh::LeanObject,
    mut v_a_5929_: *mut crate::leanh::LeanObject,
    mut v_a_5930_: *mut crate::leanh::LeanObject,
    mut v_a_5931_: *mut crate::leanh::LeanObject,
    mut v_a_5932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5933_: u8 = 0;
    let mut v_res_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5933_ = (crate::leanh::lean_unbox(v_pu_5926_) as u8);
    v_res_5934_ = l_Lean_Compiler_LCNF_getFunDecl(
        v_pu_boxed_5933_,
        v_fvarId_5927_,
        v_a_5928_,
        v_a_5929_,
        v_a_5930_,
        v_a_5931_,
    );
    crate::leanh::lean_dec(v_a_5931_);
    crate::leanh::lean_dec_ref(v_a_5930_);
    crate::leanh::lean_dec(v_a_5929_);
    crate::leanh::lean_dec_ref(v_a_5928_);
    return v_res_5934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___redArg(
    mut v_f_5935_: *mut crate::leanh::LeanObject,
    mut v_a_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5943_: u8 = 0;
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5938_ = lean_st_ref_take(v_a_5936_);
                v_lctx_5939_ = crate::leanh::lean_ctor_get(v___x_5938_, 0);
                v_nextIdx_5940_ = crate::leanh::lean_ctor_get(v___x_5938_, 1);
                v_isSharedCheck_5951_ = (!crate::leanh::lean_is_exclusive(v___x_5938_)) as u8;
                if v_isSharedCheck_5951_ == 0 {
                    v___x_5942_ = v___x_5938_;
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_5940_);
                    crate::leanh::lean_inc(v_lctx_5939_);
                    crate::leanh::lean_dec(v___x_5938_);
                    v___x_5942_ = crate::leanh::lean_box(0);
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5944_ = crate::leanh::lean_apply_1(v_f_5935_, v_lctx_5939_);
                if v_isShared_5943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5942_, 0, v___x_5944_);
                    v___x_5946_ = v___x_5942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 1, v_nextIdx_5940_);
                    v___x_5946_ = v_reuseFailAlloc_5950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5947_ = lean_st_ref_set(v_a_5936_, v___x_5946_);
                v___x_5948_ = crate::leanh::lean_box(0);
                v___x_5949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5948_);
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(
    mut v_f_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5955_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_5952_, v_a_5953_);
    crate::leanh::lean_dec(v_a_5953_);
    return v_res_5955_;
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx(
    mut v_f_5956_: *mut crate::leanh::LeanObject,
    mut v_a_5957_: *mut crate::leanh::LeanObject,
    mut v_a_5958_: *mut crate::leanh::LeanObject,
    mut v_a_5959_: *mut crate::leanh::LeanObject,
    mut v_a_5960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5962_ = lean_st_ref_take(v_a_5958_);
                v_lctx_5963_ = crate::leanh::lean_ctor_get(v___x_5962_, 0);
                v_nextIdx_5964_ = crate::leanh::lean_ctor_get(v___x_5962_, 1);
                v_isSharedCheck_5975_ = (!crate::leanh::lean_is_exclusive(v___x_5962_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v___x_5966_ = v___x_5962_;
                    v_isShared_5967_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_5964_);
                    crate::leanh::lean_inc(v_lctx_5963_);
                    crate::leanh::lean_dec(v___x_5962_);
                    v___x_5966_ = crate::leanh::lean_box(0);
                    v_isShared_5967_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5968_ = crate::leanh::lean_apply_1(v_f_5956_, v_lctx_5963_);
                if v_isShared_5967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5966_, 0, v___x_5968_);
                    v___x_5970_ = v___x_5966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5974_, 1, v_nextIdx_5964_);
                    v___x_5970_ = v_reuseFailAlloc_5974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5971_ = lean_st_ref_set(v_a_5958_, v___x_5970_);
                v___x_5972_ = crate::leanh::lean_box(0);
                v___x_5973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5973_, 0, v___x_5972_);
                return v___x_5973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___boxed(
    mut v_f_5976_: *mut crate::leanh::LeanObject,
    mut v_a_5977_: *mut crate::leanh::LeanObject,
    mut v_a_5978_: *mut crate::leanh::LeanObject,
    mut v_a_5979_: *mut crate::leanh::LeanObject,
    mut v_a_5980_: *mut crate::leanh::LeanObject,
    mut v_a_5981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5982_ =
        l_Lean_Compiler_LCNF_modifyLCtx(v_f_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_);
    crate::leanh::lean_dec(v_a_5980_);
    crate::leanh::lean_dec_ref(v_a_5979_);
    crate::leanh::lean_dec(v_a_5978_);
    crate::leanh::lean_dec_ref(v_a_5977_);
    return v_res_5982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
    mut v_pu_5983_: u8,
    mut v_decl_5984_: *mut crate::leanh::LeanObject,
    mut v_a_5985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5992_: u8 = 0;
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5987_ = lean_st_ref_take(v_a_5985_);
                v_lctx_5988_ = crate::leanh::lean_ctor_get(v___x_5987_, 0);
                v_nextIdx_5989_ = crate::leanh::lean_ctor_get(v___x_5987_, 1);
                v_isSharedCheck_6000_ = (!crate::leanh::lean_is_exclusive(v___x_5987_)) as u8;
                if v_isSharedCheck_6000_ == 0 {
                    v___x_5991_ = v___x_5987_;
                    v_isShared_5992_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_5989_);
                    crate::leanh::lean_inc(v_lctx_5988_);
                    crate::leanh::lean_dec(v___x_5987_);
                    v___x_5991_ = crate::leanh::lean_box(0);
                    v_isShared_5992_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5993_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_5983_, v_lctx_5988_, v_decl_5984_);
                if v_isShared_5992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5991_, 0, v___x_5993_);
                    v___x_5995_ = v___x_5991_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 1, v_nextIdx_5989_);
                    v___x_5995_ = v_reuseFailAlloc_5999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5996_ = lean_st_ref_set(v_a_5985_, v___x_5995_);
                v___x_5997_ = crate::leanh::lean_box(0);
                v___x_5998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5998_, 0, v___x_5997_);
                return v___x_5998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(
    mut v_pu_6001_: *mut crate::leanh::LeanObject,
    mut v_decl_6002_: *mut crate::leanh::LeanObject,
    mut v_a_6003_: *mut crate::leanh::LeanObject,
    mut v_a_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6005_: u8 = 0;
    let mut v_res_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6005_ = (crate::leanh::lean_unbox(v_pu_6001_) as u8);
    v_res_6006_ =
        l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_6005_, v_decl_6002_, v_a_6003_);
    crate::leanh::lean_dec(v_a_6003_);
    crate::leanh::lean_dec_ref(v_decl_6002_);
    return v_res_6006_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl(
    mut v_pu_6007_: u8,
    mut v_decl_6008_: *mut crate::leanh::LeanObject,
    mut v_a_6009_: *mut crate::leanh::LeanObject,
    mut v_a_6010_: *mut crate::leanh::LeanObject,
    mut v_a_6011_: *mut crate::leanh::LeanObject,
    mut v_a_6012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6014_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_6007_, v_decl_6008_, v_a_6010_);
    return v___x_6014_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___boxed(
    mut v_pu_6015_: *mut crate::leanh::LeanObject,
    mut v_decl_6016_: *mut crate::leanh::LeanObject,
    mut v_a_6017_: *mut crate::leanh::LeanObject,
    mut v_a_6018_: *mut crate::leanh::LeanObject,
    mut v_a_6019_: *mut crate::leanh::LeanObject,
    mut v_a_6020_: *mut crate::leanh::LeanObject,
    mut v_a_6021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6022_: u8 = 0;
    let mut v_res_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6022_ = (crate::leanh::lean_unbox(v_pu_6015_) as u8);
    v_res_6023_ = l_Lean_Compiler_LCNF_eraseLetDecl(
        v_pu_boxed_6022_,
        v_decl_6016_,
        v_a_6017_,
        v_a_6018_,
        v_a_6019_,
        v_a_6020_,
    );
    crate::leanh::lean_dec(v_a_6020_);
    crate::leanh::lean_dec_ref(v_a_6019_);
    crate::leanh::lean_dec(v_a_6018_);
    crate::leanh::lean_dec_ref(v_a_6017_);
    crate::leanh::lean_dec_ref(v_decl_6016_);
    return v_res_6023_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
    mut v_pu_6024_: u8,
    mut v_decl_6025_: *mut crate::leanh::LeanObject,
    mut v_recursive_6026_: u8,
    mut v_a_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6029_ = lean_st_ref_take(v_a_6027_);
                v_lctx_6030_ = crate::leanh::lean_ctor_get(v___x_6029_, 0);
                v_nextIdx_6031_ = crate::leanh::lean_ctor_get(v___x_6029_, 1);
                v_isSharedCheck_6042_ = (!crate::leanh::lean_is_exclusive(v___x_6029_)) as u8;
                if v_isSharedCheck_6042_ == 0 {
                    v___x_6033_ = v___x_6029_;
                    v_isShared_6034_ = v_isSharedCheck_6042_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_6031_);
                    crate::leanh::lean_inc(v_lctx_6030_);
                    crate::leanh::lean_dec(v___x_6029_);
                    v___x_6033_ = crate::leanh::lean_box(0);
                    v_isShared_6034_ = v_isSharedCheck_6042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6035_ = l_Lean_Compiler_LCNF_LCtx_eraseFunDecl(
                    v_pu_6024_,
                    v_lctx_6030_,
                    v_decl_6025_,
                    v_recursive_6026_,
                );
                if v_isShared_6034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6033_, 0, v___x_6035_);
                    v___x_6037_ = v___x_6033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6041_, 1, v_nextIdx_6031_);
                    v___x_6037_ = v_reuseFailAlloc_6041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6038_ = lean_st_ref_set(v_a_6027_, v___x_6037_);
                v___x_6039_ = crate::leanh::lean_box(0);
                v___x_6040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6040_, 0, v___x_6039_);
                return v___x_6040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(
    mut v_pu_6043_: *mut crate::leanh::LeanObject,
    mut v_decl_6044_: *mut crate::leanh::LeanObject,
    mut v_recursive_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6048_: u8 = 0;
    let mut v_recursive_boxed_6049_: u8 = 0;
    let mut v_res_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6048_ = (crate::leanh::lean_unbox(v_pu_6043_) as u8);
    v_recursive_boxed_6049_ = (crate::leanh::lean_unbox(v_recursive_6045_) as u8);
    v_res_6050_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
        v_pu_boxed_6048_,
        v_decl_6044_,
        v_recursive_boxed_6049_,
        v_a_6046_,
    );
    crate::leanh::lean_dec(v_a_6046_);
    crate::leanh::lean_dec_ref(v_decl_6044_);
    return v_res_6050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl(
    mut v_pu_6051_: u8,
    mut v_decl_6052_: *mut crate::leanh::LeanObject,
    mut v_recursive_6053_: u8,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6059_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
        v_pu_6051_,
        v_decl_6052_,
        v_recursive_6053_,
        v_a_6055_,
    );
    return v___x_6059_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___boxed(
    mut v_pu_6060_: *mut crate::leanh::LeanObject,
    mut v_decl_6061_: *mut crate::leanh::LeanObject,
    mut v_recursive_6062_: *mut crate::leanh::LeanObject,
    mut v_a_6063_: *mut crate::leanh::LeanObject,
    mut v_a_6064_: *mut crate::leanh::LeanObject,
    mut v_a_6065_: *mut crate::leanh::LeanObject,
    mut v_a_6066_: *mut crate::leanh::LeanObject,
    mut v_a_6067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6068_: u8 = 0;
    let mut v_recursive_boxed_6069_: u8 = 0;
    let mut v_res_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6068_ = (crate::leanh::lean_unbox(v_pu_6060_) as u8);
    v_recursive_boxed_6069_ = (crate::leanh::lean_unbox(v_recursive_6062_) as u8);
    v_res_6070_ = l_Lean_Compiler_LCNF_eraseFunDecl(
        v_pu_boxed_6068_,
        v_decl_6061_,
        v_recursive_boxed_6069_,
        v_a_6063_,
        v_a_6064_,
        v_a_6065_,
        v_a_6066_,
    );
    crate::leanh::lean_dec(v_a_6066_);
    crate::leanh::lean_dec_ref(v_a_6065_);
    crate::leanh::lean_dec(v_a_6064_);
    crate::leanh::lean_dec_ref(v_a_6063_);
    crate::leanh::lean_dec_ref(v_decl_6061_);
    return v_res_6070_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___redArg(
    mut v_pu_6071_: u8,
    mut v_code_6072_: *mut crate::leanh::LeanObject,
    mut v_a_6073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6080_: u8 = 0;
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6075_ = lean_st_ref_take(v_a_6073_);
                v_lctx_6076_ = crate::leanh::lean_ctor_get(v___x_6075_, 0);
                v_nextIdx_6077_ = crate::leanh::lean_ctor_get(v___x_6075_, 1);
                v_isSharedCheck_6088_ = (!crate::leanh::lean_is_exclusive(v___x_6075_)) as u8;
                if v_isSharedCheck_6088_ == 0 {
                    v___x_6079_ = v___x_6075_;
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_6077_);
                    crate::leanh::lean_inc(v_lctx_6076_);
                    crate::leanh::lean_dec(v___x_6075_);
                    v___x_6079_ = crate::leanh::lean_box(0);
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6081_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_6071_, v_code_6072_, v_lctx_6076_);
                if v_isShared_6080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6079_, 0, v___x_6081_);
                    v___x_6083_ = v___x_6079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 1, v_nextIdx_6077_);
                    v___x_6083_ = v_reuseFailAlloc_6087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6084_ = lean_st_ref_set(v_a_6073_, v___x_6083_);
                v___x_6085_ = crate::leanh::lean_box(0);
                v___x_6086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6086_, 0, v___x_6085_);
                return v___x_6086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(
    mut v_pu_6089_: *mut crate::leanh::LeanObject,
    mut v_code_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_a_6092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6093_: u8 = 0;
    let mut v_res_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6093_ = (crate::leanh::lean_unbox(v_pu_6089_) as u8);
    v_res_6094_ =
        l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_6093_, v_code_6090_, v_a_6091_);
    crate::leanh::lean_dec(v_a_6091_);
    crate::leanh::lean_dec_ref(v_code_6090_);
    return v_res_6094_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode(
    mut v_pu_6095_: u8,
    mut v_code_6096_: *mut crate::leanh::LeanObject,
    mut v_a_6097_: *mut crate::leanh::LeanObject,
    mut v_a_6098_: *mut crate::leanh::LeanObject,
    mut v_a_6099_: *mut crate::leanh::LeanObject,
    mut v_a_6100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6102_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_6095_, v_code_6096_, v_a_6098_);
    return v___x_6102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___boxed(
    mut v_pu_6103_: *mut crate::leanh::LeanObject,
    mut v_code_6104_: *mut crate::leanh::LeanObject,
    mut v_a_6105_: *mut crate::leanh::LeanObject,
    mut v_a_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6110_: u8 = 0;
    let mut v_res_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6110_ = (crate::leanh::lean_unbox(v_pu_6103_) as u8);
    v_res_6111_ = l_Lean_Compiler_LCNF_eraseCode(
        v_pu_boxed_6110_,
        v_code_6104_,
        v_a_6105_,
        v_a_6106_,
        v_a_6107_,
        v_a_6108_,
    );
    crate::leanh::lean_dec(v_a_6108_);
    crate::leanh::lean_dec_ref(v_a_6107_);
    crate::leanh::lean_dec(v_a_6106_);
    crate::leanh::lean_dec_ref(v_a_6105_);
    crate::leanh::lean_dec_ref(v_code_6104_);
    return v_res_6111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___redArg(
    mut v_pu_6112_: u8,
    mut v_param_6113_: *mut crate::leanh::LeanObject,
    mut v_a_6114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6116_ = lean_st_ref_take(v_a_6114_);
                v_lctx_6117_ = crate::leanh::lean_ctor_get(v___x_6116_, 0);
                v_nextIdx_6118_ = crate::leanh::lean_ctor_get(v___x_6116_, 1);
                v_isSharedCheck_6129_ = (!crate::leanh::lean_is_exclusive(v___x_6116_)) as u8;
                if v_isSharedCheck_6129_ == 0 {
                    v___x_6120_ = v___x_6116_;
                    v_isShared_6121_ = v_isSharedCheck_6129_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_6118_);
                    crate::leanh::lean_inc(v_lctx_6117_);
                    crate::leanh::lean_dec(v___x_6116_);
                    v___x_6120_ = crate::leanh::lean_box(0);
                    v_isShared_6121_ = v_isSharedCheck_6129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6122_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_6112_, v_lctx_6117_, v_param_6113_);
                if v_isShared_6121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6120_, 0, v___x_6122_);
                    v___x_6124_ = v___x_6120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6128_, 1, v_nextIdx_6118_);
                    v___x_6124_ = v_reuseFailAlloc_6128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6125_ = lean_st_ref_set(v_a_6114_, v___x_6124_);
                v___x_6126_ = crate::leanh::lean_box(0);
                v___x_6127_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6127_, 0, v___x_6126_);
                return v___x_6127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(
    mut v_pu_6130_: *mut crate::leanh::LeanObject,
    mut v_param_6131_: *mut crate::leanh::LeanObject,
    mut v_a_6132_: *mut crate::leanh::LeanObject,
    mut v_a_6133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6134_: u8 = 0;
    let mut v_res_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6134_ = (crate::leanh::lean_unbox(v_pu_6130_) as u8);
    v_res_6135_ =
        l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_6134_, v_param_6131_, v_a_6132_);
    crate::leanh::lean_dec(v_a_6132_);
    crate::leanh::lean_dec_ref(v_param_6131_);
    return v_res_6135_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam(
    mut v_pu_6136_: u8,
    mut v_param_6137_: *mut crate::leanh::LeanObject,
    mut v_a_6138_: *mut crate::leanh::LeanObject,
    mut v_a_6139_: *mut crate::leanh::LeanObject,
    mut v_a_6140_: *mut crate::leanh::LeanObject,
    mut v_a_6141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6143_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_6136_, v_param_6137_, v_a_6139_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___boxed(
    mut v_pu_6144_: *mut crate::leanh::LeanObject,
    mut v_param_6145_: *mut crate::leanh::LeanObject,
    mut v_a_6146_: *mut crate::leanh::LeanObject,
    mut v_a_6147_: *mut crate::leanh::LeanObject,
    mut v_a_6148_: *mut crate::leanh::LeanObject,
    mut v_a_6149_: *mut crate::leanh::LeanObject,
    mut v_a_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6151_: u8 = 0;
    let mut v_res_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6151_ = (crate::leanh::lean_unbox(v_pu_6144_) as u8);
    v_res_6152_ = l_Lean_Compiler_LCNF_eraseParam(
        v_pu_boxed_6151_,
        v_param_6145_,
        v_a_6146_,
        v_a_6147_,
        v_a_6148_,
        v_a_6149_,
    );
    crate::leanh::lean_dec(v_a_6149_);
    crate::leanh::lean_dec_ref(v_a_6148_);
    crate::leanh::lean_dec(v_a_6147_);
    crate::leanh::lean_dec_ref(v_a_6146_);
    crate::leanh::lean_dec_ref(v_param_6145_);
    return v_res_6152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___redArg(
    mut v_pu_6153_: u8,
    mut v_params_6154_: *mut crate::leanh::LeanObject,
    mut v_a_6155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6157_ = lean_st_ref_take(v_a_6155_);
                v_lctx_6158_ = crate::leanh::lean_ctor_get(v___x_6157_, 0);
                v_nextIdx_6159_ = crate::leanh::lean_ctor_get(v___x_6157_, 1);
                v_isSharedCheck_6170_ = (!crate::leanh::lean_is_exclusive(v___x_6157_)) as u8;
                if v_isSharedCheck_6170_ == 0 {
                    v___x_6161_ = v___x_6157_;
                    v_isShared_6162_ = v_isSharedCheck_6170_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_6159_);
                    crate::leanh::lean_inc(v_lctx_6158_);
                    crate::leanh::lean_dec(v___x_6157_);
                    v___x_6161_ = crate::leanh::lean_box(0);
                    v_isShared_6162_ = v_isSharedCheck_6170_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6163_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_6153_, v_lctx_6158_, v_params_6154_);
                if v_isShared_6162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6161_, 0, v___x_6163_);
                    v___x_6165_ = v___x_6161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 1, v_nextIdx_6159_);
                    v___x_6165_ = v_reuseFailAlloc_6169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6166_ = lean_st_ref_set(v_a_6155_, v___x_6165_);
                v___x_6167_ = crate::leanh::lean_box(0);
                v___x_6168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6168_, 0, v___x_6167_);
                return v___x_6168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(
    mut v_pu_6171_: *mut crate::leanh::LeanObject,
    mut v_params_6172_: *mut crate::leanh::LeanObject,
    mut v_a_6173_: *mut crate::leanh::LeanObject,
    mut v_a_6174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6175_: u8 = 0;
    let mut v_res_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6175_ = (crate::leanh::lean_unbox(v_pu_6171_) as u8);
    v_res_6176_ =
        l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_6175_, v_params_6172_, v_a_6173_);
    crate::leanh::lean_dec(v_a_6173_);
    crate::leanh::lean_dec_ref(v_params_6172_);
    return v_res_6176_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams(
    mut v_pu_6177_: u8,
    mut v_params_6178_: *mut crate::leanh::LeanObject,
    mut v_a_6179_: *mut crate::leanh::LeanObject,
    mut v_a_6180_: *mut crate::leanh::LeanObject,
    mut v_a_6181_: *mut crate::leanh::LeanObject,
    mut v_a_6182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6184_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_6177_, v_params_6178_, v_a_6180_);
    return v___x_6184_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___boxed(
    mut v_pu_6185_: *mut crate::leanh::LeanObject,
    mut v_params_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
    mut v_a_6190_: *mut crate::leanh::LeanObject,
    mut v_a_6191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6192_: u8 = 0;
    let mut v_res_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6192_ = (crate::leanh::lean_unbox(v_pu_6185_) as u8);
    v_res_6193_ = l_Lean_Compiler_LCNF_eraseParams(
        v_pu_boxed_6192_,
        v_params_6186_,
        v_a_6187_,
        v_a_6188_,
        v_a_6189_,
        v_a_6190_,
    );
    crate::leanh::lean_dec(v_a_6190_);
    crate::leanh::lean_dec_ref(v_a_6189_);
    crate::leanh::lean_dec(v_a_6188_);
    crate::leanh::lean_dec_ref(v_a_6187_);
    crate::leanh::lean_dec_ref(v_params_6186_);
    return v_res_6193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
    mut v_pu_6194_: u8,
    mut v_decl_6195_: *mut crate::leanh::LeanObject,
    mut v_a_6196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_decl_6195_) {
        0 => {
            let mut v_decl_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6198_ = crate::leanh::lean_ctor_get(v_decl_6195_, 0);
            v___x_6199_ =
                l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_6194_, v_decl_6198_, v_a_6196_);
            return v___x_6199_;
        }
        1 => {
            let mut v_decl_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6201_: u8 = 0;
            let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6200_ = crate::leanh::lean_ctor_get(v_decl_6195_, 0);
            v___x_6201_ = 1;
            v___x_6202_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                v_pu_6194_,
                v_decl_6200_,
                v___x_6201_,
                v_a_6196_,
            );
            return v___x_6202_;
        }
        2 => {
            let mut v_decl_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6204_: u8 = 0;
            let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decl_6203_ = crate::leanh::lean_ctor_get(v_decl_6195_, 0);
            v___x_6204_ = 1;
            v___x_6205_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
                v_pu_6194_,
                v_decl_6203_,
                v___x_6204_,
                v_a_6196_,
            );
            return v___x_6205_;
        }
        _ => {
            let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6206_ = crate::leanh::lean_box(0);
            v___x_6207_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6207_, 0, v___x_6206_);
            return v___x_6207_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(
    mut v_pu_6208_: *mut crate::leanh::LeanObject,
    mut v_decl_6209_: *mut crate::leanh::LeanObject,
    mut v_a_6210_: *mut crate::leanh::LeanObject,
    mut v_a_6211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6212_: u8 = 0;
    let mut v_res_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6212_ = (crate::leanh::lean_unbox(v_pu_6208_) as u8);
    v_res_6213_ =
        l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_6212_, v_decl_6209_, v_a_6210_);
    crate::leanh::lean_dec(v_a_6210_);
    crate::leanh::lean_dec_ref(v_decl_6209_);
    return v_res_6213_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl(
    mut v_pu_6214_: u8,
    mut v_decl_6215_: *mut crate::leanh::LeanObject,
    mut v_a_6216_: *mut crate::leanh::LeanObject,
    mut v_a_6217_: *mut crate::leanh::LeanObject,
    mut v_a_6218_: *mut crate::leanh::LeanObject,
    mut v_a_6219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6221_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_6214_, v_decl_6215_, v_a_6217_);
    return v___x_6221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(
    mut v_pu_6222_: *mut crate::leanh::LeanObject,
    mut v_decl_6223_: *mut crate::leanh::LeanObject,
    mut v_a_6224_: *mut crate::leanh::LeanObject,
    mut v_a_6225_: *mut crate::leanh::LeanObject,
    mut v_a_6226_: *mut crate::leanh::LeanObject,
    mut v_a_6227_: *mut crate::leanh::LeanObject,
    mut v_a_6228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6229_: u8 = 0;
    let mut v_res_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6229_ = (crate::leanh::lean_unbox(v_pu_6222_) as u8);
    v_res_6230_ = l_Lean_Compiler_LCNF_eraseCodeDecl(
        v_pu_boxed_6229_,
        v_decl_6223_,
        v_a_6224_,
        v_a_6225_,
        v_a_6226_,
        v_a_6227_,
    );
    crate::leanh::lean_dec(v_a_6227_);
    crate::leanh::lean_dec_ref(v_a_6226_);
    crate::leanh::lean_dec(v_a_6225_);
    crate::leanh::lean_dec_ref(v_a_6224_);
    crate::leanh::lean_dec_ref(v_decl_6223_);
    return v_res_6230_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(
    mut v_pu_6231_: u8,
    mut v_as_6232_: *mut crate::leanh::LeanObject,
    mut v_i_6233_: usize,
    mut v_stop_6234_: usize,
    mut v_b_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6238_: u8 = 0;
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: usize = 0;
    let mut v___x_6243_: usize = 0;
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6238_ = lean_usize_dec_eq(v_i_6233_, v_stop_6234_);
                if v___x_6238_ == 0 {
                    v___x_6239_ = lean_array_uget_borrowed(v_as_6232_, v_i_6233_);
                    v___x_6240_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
                        v_pu_6231_,
                        v___x_6239_,
                        v___y_6236_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6240_) == 0 {
                        v_a_6241_ = crate::leanh::lean_ctor_get(v___x_6240_, 0);
                        crate::leanh::lean_inc(v_a_6241_);
                        crate::leanh::lean_dec_ref_known(v___x_6240_, 1);
                        v___x_6242_ = 1usize;
                        v___x_6243_ = lean_usize_add(v_i_6233_, v___x_6242_);
                        v_i_6233_ = v___x_6243_;
                        v_b_6235_ = v_a_6241_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6240_;
                    }
                } else {
                    v___x_6245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6245_, 0, v_b_6235_);
                    return v___x_6245_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(
    mut v_pu_6246_: *mut crate::leanh::LeanObject,
    mut v_as_6247_: *mut crate::leanh::LeanObject,
    mut v_i_6248_: *mut crate::leanh::LeanObject,
    mut v_stop_6249_: *mut crate::leanh::LeanObject,
    mut v_b_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6253_: u8 = 0;
    let mut v_i_boxed_6254_: usize = 0;
    let mut v_stop_boxed_6255_: usize = 0;
    let mut v_res_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6253_ = (crate::leanh::lean_unbox(v_pu_6246_) as u8);
    v_i_boxed_6254_ = crate::leanh::lean_unbox_usize(v_i_6248_);
    crate::leanh::lean_dec(v_i_6248_);
    v_stop_boxed_6255_ = crate::leanh::lean_unbox_usize(v_stop_6249_);
    crate::leanh::lean_dec(v_stop_6249_);
    v_res_6256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_6253_, v_as_6247_, v_i_boxed_6254_, v_stop_boxed_6255_, v_b_6250_, v___y_6251_);
    crate::leanh::lean_dec(v___y_6251_);
    crate::leanh::lean_dec_ref(v_as_6247_);
    return v_res_6256_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecls(
    mut v_pu_6257_: u8,
    mut v_decls_6258_: *mut crate::leanh::LeanObject,
    mut v_a_6259_: *mut crate::leanh::LeanObject,
    mut v_a_6260_: *mut crate::leanh::LeanObject,
    mut v_a_6261_: *mut crate::leanh::LeanObject,
    mut v_a_6262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: u8 = 0;
    v___x_6264_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6265_ = lean_array_get_size(v_decls_6258_);
    v___x_6266_ = crate::leanh::lean_box(0);
    v___x_6267_ = lean_nat_dec_lt(v___x_6264_, v___x_6265_);
    if v___x_6267_ == 0 {
        let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6268_, 0, v___x_6266_);
        return v___x_6268_;
    } else {
        let mut v___x_6269_: u8 = 0;
        v___x_6269_ = lean_nat_dec_le(v___x_6265_, v___x_6265_);
        if v___x_6269_ == 0 {
            if v___x_6267_ == 0 {
                let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6270_, 0, v___x_6266_);
                return v___x_6270_;
            } else {
                let mut v___x_6271_: usize = 0;
                let mut v___x_6272_: usize = 0;
                let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6271_ = 0usize;
                v___x_6272_ = lean_usize_of_nat(v___x_6265_);
                v___x_6273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6257_, v_decls_6258_, v___x_6271_, v___x_6272_, v___x_6266_, v_a_6260_);
                return v___x_6273_;
            }
        } else {
            let mut v___x_6274_: usize = 0;
            let mut v___x_6275_: usize = 0;
            let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6274_ = 0usize;
            v___x_6275_ = lean_usize_of_nat(v___x_6265_);
            v___x_6276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6257_, v_decls_6258_, v___x_6274_, v___x_6275_, v___x_6266_, v_a_6260_);
            return v___x_6276_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(
    mut v_pu_6277_: *mut crate::leanh::LeanObject,
    mut v_decls_6278_: *mut crate::leanh::LeanObject,
    mut v_a_6279_: *mut crate::leanh::LeanObject,
    mut v_a_6280_: *mut crate::leanh::LeanObject,
    mut v_a_6281_: *mut crate::leanh::LeanObject,
    mut v_a_6282_: *mut crate::leanh::LeanObject,
    mut v_a_6283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6284_: u8 = 0;
    let mut v_res_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6284_ = (crate::leanh::lean_unbox(v_pu_6277_) as u8);
    v_res_6285_ = l_Lean_Compiler_LCNF_eraseCodeDecls(
        v_pu_boxed_6284_,
        v_decls_6278_,
        v_a_6279_,
        v_a_6280_,
        v_a_6281_,
        v_a_6282_,
    );
    crate::leanh::lean_dec(v_a_6282_);
    crate::leanh::lean_dec_ref(v_a_6281_);
    crate::leanh::lean_dec(v_a_6280_);
    crate::leanh::lean_dec_ref(v_a_6279_);
    crate::leanh::lean_dec_ref(v_decls_6278_);
    return v_res_6285_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(
    mut v_pu_6286_: u8,
    mut v_as_6287_: *mut crate::leanh::LeanObject,
    mut v_i_6288_: usize,
    mut v_stop_6289_: usize,
    mut v_b_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6286_, v_as_6287_, v_i_6288_, v_stop_6289_, v_b_6290_, v___y_6292_);
    return v___x_6296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(
    mut v_pu_6297_: *mut crate::leanh::LeanObject,
    mut v_as_6298_: *mut crate::leanh::LeanObject,
    mut v_i_6299_: *mut crate::leanh::LeanObject,
    mut v_stop_6300_: *mut crate::leanh::LeanObject,
    mut v_b_6301_: *mut crate::leanh::LeanObject,
    mut v___y_6302_: *mut crate::leanh::LeanObject,
    mut v___y_6303_: *mut crate::leanh::LeanObject,
    mut v___y_6304_: *mut crate::leanh::LeanObject,
    mut v___y_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6307_: u8 = 0;
    let mut v_i_boxed_6308_: usize = 0;
    let mut v_stop_boxed_6309_: usize = 0;
    let mut v_res_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6307_ = (crate::leanh::lean_unbox(v_pu_6297_) as u8);
    v_i_boxed_6308_ = crate::leanh::lean_unbox_usize(v_i_6299_);
    crate::leanh::lean_dec(v_i_6299_);
    v_stop_boxed_6309_ = crate::leanh::lean_unbox_usize(v_stop_6300_);
    crate::leanh::lean_dec(v_stop_6300_);
    v_res_6310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_6307_, v_as_6298_, v_i_boxed_6308_, v_stop_boxed_6309_, v_b_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
    crate::leanh::lean_dec(v___y_6305_);
    crate::leanh::lean_dec_ref(v___y_6304_);
    crate::leanh::lean_dec(v___y_6303_);
    crate::leanh::lean_dec_ref(v___y_6302_);
    crate::leanh::lean_dec_ref(v_as_6298_);
    return v_res_6310_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(
    mut v_f_6311_: *mut crate::leanh::LeanObject,
    mut v_v_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6327_: u8 = 0;
    let mut v_unused_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_6312_) == 0 {
                    v_code_6318_ = crate::leanh::lean_ctor_get(v_v_6312_, 0);
                    crate::leanh::lean_inc_ref(v_code_6318_);
                    crate::leanh::lean_dec_ref_known(v_v_6312_, 1);
                    crate::leanh::lean_inc(v___y_6316_);
                    crate::leanh::lean_inc_ref(v___y_6315_);
                    crate::leanh::lean_inc(v___y_6314_);
                    crate::leanh::lean_inc_ref(v___y_6313_);
                    v___x_6319_ = crate::leanh::lean_apply_6(
                        v_f_6311_,
                        v_code_6318_,
                        v___y_6313_,
                        v___y_6314_,
                        v___y_6315_,
                        v___y_6316_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6319_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_6311_);
                    v_isSharedCheck_6327_ = (!crate::leanh::lean_is_exclusive(v_v_6312_)) as u8;
                    if v_isSharedCheck_6327_ == 0 {
                        v_unused_6328_ = crate::leanh::lean_ctor_get(v_v_6312_, 0);
                        crate::leanh::lean_dec(v_unused_6328_);
                        v___x_6321_ = v_v_6312_;
                        v_isShared_6322_ = v_isSharedCheck_6327_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_6312_);
                        v___x_6321_ = crate::leanh::lean_box(0);
                        v_isShared_6322_ = v_isSharedCheck_6327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6323_ = crate::leanh::lean_box(0);
                if v_isShared_6322_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6321_, 0);
                    crate::leanh::lean_ctor_set(v___x_6321_, 0, v___x_6323_);
                    v___x_6325_ = v___x_6321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6326_, 0, v___x_6323_);
                    v___x_6325_ = v_reuseFailAlloc_6326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg___boxed(
    mut v_f_6329_: *mut crate::leanh::LeanObject,
    mut v_v_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6336_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_6329_, v_v_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    crate::leanh::lean_dec(v___y_6334_);
    crate::leanh::lean_dec_ref(v___y_6333_);
    crate::leanh::lean_dec(v___y_6332_);
    crate::leanh::lean_dec_ref(v___y_6331_);
    return v_res_6336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(
    mut v_pu_6337_: u8,
    mut v_f_6338_: *mut crate::leanh::LeanObject,
    mut v_v_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
    mut v___y_6343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6345_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_6338_, v_v_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
    return v___x_6345_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(
    mut v_pu_6346_: *mut crate::leanh::LeanObject,
    mut v_f_6347_: *mut crate::leanh::LeanObject,
    mut v_v_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
    mut v___y_6350_: *mut crate::leanh::LeanObject,
    mut v___y_6351_: *mut crate::leanh::LeanObject,
    mut v___y_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6354_: u8 = 0;
    let mut v_res_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6354_ = (crate::leanh::lean_unbox(v_pu_6346_) as u8);
    v_res_6355_ =
        l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(
            v_pu_boxed_6354_,
            v_f_6347_,
            v_v_6348_,
            v___y_6349_,
            v___y_6350_,
            v___y_6351_,
            v___y_6352_,
        );
    crate::leanh::lean_dec(v___y_6352_);
    crate::leanh::lean_dec_ref(v___y_6351_);
    crate::leanh::lean_dec(v___y_6350_);
    crate::leanh::lean_dec_ref(v___y_6349_);
    return v_res_6355_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseDecl(
    mut v_pu_6356_: u8,
    mut v_decl_6357_: *mut crate::leanh::LeanObject,
    mut v_a_6358_: *mut crate::leanh::LeanObject,
    mut v_a_6359_: *mut crate::leanh::LeanObject,
    mut v_a_6360_: *mut crate::leanh::LeanObject,
    mut v_a_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_6363_ = crate::leanh::lean_ctor_get(v_decl_6357_, 0);
    crate::leanh::lean_inc_ref(v_toSignature_6363_);
    v_value_6364_ = crate::leanh::lean_ctor_get(v_decl_6357_, 1);
    crate::leanh::lean_inc_ref(v_value_6364_);
    crate::leanh::lean_dec_ref(v_decl_6357_);
    v_params_6365_ = crate::leanh::lean_ctor_get(v_toSignature_6363_, 3);
    crate::leanh::lean_inc_ref(v_params_6365_);
    crate::leanh::lean_dec_ref(v_toSignature_6363_);
    v___x_6366_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_6356_, v_params_6365_, v_a_6359_);
    crate::leanh::lean_dec_ref(v_params_6365_);
    crate::leanh::lean_dec_ref(v___x_6366_);
    v___x_6367_ = crate::leanh::lean_box((v_pu_6356_) as usize);
    v___x_6368_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_eraseCode___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___x_6368_, 0, v___x_6367_);
    v___x_6369_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_6368_, v_value_6364_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseDecl___boxed(
    mut v_pu_6370_: *mut crate::leanh::LeanObject,
    mut v_decl_6371_: *mut crate::leanh::LeanObject,
    mut v_a_6372_: *mut crate::leanh::LeanObject,
    mut v_a_6373_: *mut crate::leanh::LeanObject,
    mut v_a_6374_: *mut crate::leanh::LeanObject,
    mut v_a_6375_: *mut crate::leanh::LeanObject,
    mut v_a_6376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6377_: u8 = 0;
    let mut v_res_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6377_ = (crate::leanh::lean_unbox(v_pu_6370_) as u8);
    v_res_6378_ = l_Lean_Compiler_LCNF_eraseDecl(
        v_pu_boxed_6377_,
        v_decl_6371_,
        v_a_6372_,
        v_a_6373_,
        v_a_6374_,
        v_a_6375_,
    );
    crate::leanh::lean_dec(v_a_6375_);
    crate::leanh::lean_dec_ref(v_a_6374_);
    crate::leanh::lean_dec(v_a_6373_);
    crate::leanh::lean_dec_ref(v_a_6372_);
    return v_res_6378_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_erase(
    mut v_pu_6379_: u8,
    mut v_decl_6380_: *mut crate::leanh::LeanObject,
    mut v_a_6381_: *mut crate::leanh::LeanObject,
    mut v_a_6382_: *mut crate::leanh::LeanObject,
    mut v_a_6383_: *mut crate::leanh::LeanObject,
    mut v_a_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6386_ = l_Lean_Compiler_LCNF_eraseDecl(
        v_pu_6379_,
        v_decl_6380_,
        v_a_6381_,
        v_a_6382_,
        v_a_6383_,
        v_a_6384_,
    );
    return v___x_6386_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_erase___boxed(
    mut v_pu_6387_: *mut crate::leanh::LeanObject,
    mut v_decl_6388_: *mut crate::leanh::LeanObject,
    mut v_a_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6394_: u8 = 0;
    let mut v_res_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6394_ = (crate::leanh::lean_unbox(v_pu_6387_) as u8);
    v_res_6395_ = l_Lean_Compiler_LCNF_Decl_erase(
        v_pu_boxed_6394_,
        v_decl_6388_,
        v_a_6389_,
        v_a_6390_,
        v_a_6391_,
        v_a_6392_,
    );
    crate::leanh::lean_dec(v_a_6392_);
    crate::leanh::lean_dec_ref(v_a_6391_);
    crate::leanh::lean_dec(v_a_6390_);
    crate::leanh::lean_dec_ref(v_a_6389_);
    return v_res_6395_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(
    mut v_msg_6396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6397_ = l_Lean_instInhabitedExpr;
    v___x_6398_ = lean_panic_fn_borrowed(v___x_6397_, v_msg_6396_);
    return v___x_6398_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6402_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2;
    v___x_6403_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_6404_ = crate::leanh::lean_unsigned_to_nat(215);
    v___x_6405_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1;
    v___x_6406_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0;
    v___x_6407_ = l_mkPanicMessageWithDecl(
        v___x_6406_,
        v___x_6405_,
        v___x_6404_,
        v___x_6403_,
        v___x_6402_,
    );
    return v___x_6407_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
    mut v_pu_6408_: u8,
    mut v_s_6409_: *mut crate::leanh::LeanObject,
    mut v_translator_6410_: u8,
    mut v_e_6411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6412_: u8 = 0;
    let mut v_fvarId_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6430_: u8 = 0;
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: usize = 0;
    let mut v___x_6435_: usize = 0;
    let mut v___x_6436_: u8 = 0;
    let mut v___x_6437_: usize = 0;
    let mut v___x_6438_: usize = 0;
    let mut v___x_6439_: u8 = 0;
    let mut v_binderName_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6443_: u8 = 0;
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6447_: u8 = 0;
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: u8 = 0;
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: usize = 0;
    let mut v___x_6452_: usize = 0;
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: usize = 0;
    let mut v___x_6455_: usize = 0;
    let mut v___x_6456_: u8 = 0;
    let mut v_binderName_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6460_: u8 = 0;
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6464_: u8 = 0;
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: u8 = 0;
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: usize = 0;
    let mut v___x_6469_: usize = 0;
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6471_: usize = 0;
    let mut v___x_6472_: usize = 0;
    let mut v___x_6473_: u8 = 0;
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: u8 = 0;
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: usize = 0;
    let mut v___x_6488_: usize = 0;
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6412_ = l_Lean_Expr_hasFVar(v_e_6411_);
                if v___x_6412_ == 0 {
                    return v_e_6411_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_6411_) {
                        1 => {
                            v_fvarId_6413_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v___x_6414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6409_, v_fvarId_6413_);
                            if crate::leanh::lean_obj_tag(v___x_6414_) == 0 {
                                return v_e_6411_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_6411_, 1);
                                v_val_6415_ = crate::leanh::lean_ctor_get(v___x_6414_, 0);
                                crate::leanh::lean_inc(v_val_6415_);
                                crate::leanh::lean_dec_ref_known(v___x_6414_, 1);
                                match crate::leanh::lean_obj_tag(v_val_6415_) {
                                    0 => {
                                        v___x_6416_ = l_Lean_Compiler_LCNF_erasedExpr;
                                        return v___x_6416_;
                                    }
                                    1 => {
                                        if v_translator_6410_ == 0 {
                                            v_fvarId_6417_ =
                                                crate::leanh::lean_ctor_get(v_val_6415_, 0);
                                            crate::leanh::lean_inc(v_fvarId_6417_);
                                            crate::leanh::lean_dec_ref_known(v_val_6415_, 1);
                                            v___x_6418_ =
                                                l_Lean_Expr_fvar___override(v_fvarId_6417_);
                                            v_e_6411_ = v___x_6418_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v_fvarId_6420_ =
                                                crate::leanh::lean_ctor_get(v_val_6415_, 0);
                                            crate::leanh::lean_inc(v_fvarId_6420_);
                                            crate::leanh::lean_dec_ref_known(v_val_6415_, 1);
                                            v___x_6421_ =
                                                l_Lean_Expr_fvar___override(v_fvarId_6420_);
                                            return v___x_6421_;
                                        }
                                    }
                                    _ => {
                                        if v_translator_6410_ == 0 {
                                            v_expr_6422_ =
                                                crate::leanh::lean_ctor_get(v_val_6415_, 0);
                                            crate::leanh::lean_inc_ref(v_expr_6422_);
                                            crate::leanh::lean_dec_ref_known(v_val_6415_, 1);
                                            v_e_6411_ = v_expr_6422_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v_expr_6424_ =
                                                crate::leanh::lean_ctor_get(v_val_6415_, 0);
                                            crate::leanh::lean_inc_ref(v_expr_6424_);
                                            crate::leanh::lean_dec_ref_known(v_val_6415_, 1);
                                            return v_expr_6424_;
                                        }
                                    }
                                }
                            }
                        }
                        5 => {
                            v_fn_6425_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v_arg_6426_ = crate::leanh::lean_ctor_get(v_e_6411_, 1);
                            crate::leanh::lean_inc_ref(v_fn_6425_);
                            v___x_6427_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_6408_, v_s_6409_, v_translator_6410_, v_fn_6425_);
                            crate::leanh::lean_inc_ref(v_arg_6426_);
                            v___x_6428_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_arg_6426_);
                            v___x_6434_ = lean_ptr_addr(v_fn_6425_);
                            v___x_6435_ = lean_ptr_addr(v___x_6427_);
                            v___x_6436_ = lean_usize_dec_eq(v___x_6434_, v___x_6435_);
                            if v___x_6436_ == 0 {
                                v___y_6430_ = v___x_6436_;
                                state = 1;
                                continue;
                            } else {
                                v___x_6437_ = lean_ptr_addr(v_arg_6426_);
                                v___x_6438_ = lean_ptr_addr(v___x_6428_);
                                v___x_6439_ = lean_usize_dec_eq(v___x_6437_, v___x_6438_);
                                v___y_6430_ = v___x_6439_;
                                state = 1;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_6440_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v_binderType_6441_ = crate::leanh::lean_ctor_get(v_e_6411_, 1);
                            v_body_6442_ = crate::leanh::lean_ctor_get(v_e_6411_, 2);
                            v_binderInfo_6443_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_6411_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_6441_);
                            v___x_6444_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_binderType_6441_);
                            crate::leanh::lean_inc_ref(v_body_6442_);
                            v___x_6445_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_body_6442_);
                            v___x_6451_ = lean_ptr_addr(v_binderType_6441_);
                            v___x_6452_ = lean_ptr_addr(v___x_6444_);
                            v___x_6453_ = lean_usize_dec_eq(v___x_6451_, v___x_6452_);
                            if v___x_6453_ == 0 {
                                v___y_6447_ = v___x_6453_;
                                state = 2;
                                continue;
                            } else {
                                v___x_6454_ = lean_ptr_addr(v_body_6442_);
                                v___x_6455_ = lean_ptr_addr(v___x_6445_);
                                v___x_6456_ = lean_usize_dec_eq(v___x_6454_, v___x_6455_);
                                v___y_6447_ = v___x_6456_;
                                state = 2;
                                continue;
                            }
                        }
                        7 => {
                            v_binderName_6457_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v_binderType_6458_ = crate::leanh::lean_ctor_get(v_e_6411_, 1);
                            v_body_6459_ = crate::leanh::lean_ctor_get(v_e_6411_, 2);
                            v_binderInfo_6460_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_6411_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_6458_);
                            v___x_6461_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_binderType_6458_);
                            crate::leanh::lean_inc_ref(v_body_6459_);
                            v___x_6462_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_body_6459_);
                            v___x_6468_ = lean_ptr_addr(v_binderType_6458_);
                            v___x_6469_ = lean_ptr_addr(v___x_6461_);
                            v___x_6470_ = lean_usize_dec_eq(v___x_6468_, v___x_6469_);
                            if v___x_6470_ == 0 {
                                v___y_6464_ = v___x_6470_;
                                state = 3;
                                continue;
                            } else {
                                v___x_6471_ = lean_ptr_addr(v_body_6459_);
                                v___x_6472_ = lean_ptr_addr(v___x_6462_);
                                v___x_6473_ = lean_usize_dec_eq(v___x_6471_, v___x_6472_);
                                v___y_6464_ = v___x_6473_;
                                state = 3;
                                continue;
                            }
                        }
                        8 => {
                            crate::leanh::lean_dec_ref_known(v_e_6411_, 4);
                            v___x_6474_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
                            v___x_6475_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_6474_);
                            return v___x_6475_;
                        }
                        10 => {
                            v_data_6476_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v_expr_6477_ = crate::leanh::lean_ctor_get(v_e_6411_, 1);
                            crate::leanh::lean_inc_ref(v_expr_6477_);
                            v___x_6478_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_expr_6477_);
                            v___x_6479_ = lean_ptr_addr(v_expr_6477_);
                            v___x_6480_ = lean_ptr_addr(v___x_6478_);
                            v___x_6481_ = lean_usize_dec_eq(v___x_6479_, v___x_6480_);
                            if v___x_6481_ == 0 {
                                crate::leanh::lean_inc(v_data_6476_);
                                crate::leanh::lean_dec_ref_known(v_e_6411_, 2);
                                v___x_6482_ =
                                    l_Lean_Expr_mdata___override(v_data_6476_, v___x_6478_);
                                return v___x_6482_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_6478_);
                                return v_e_6411_;
                            }
                        }
                        11 => {
                            v_typeName_6483_ = crate::leanh::lean_ctor_get(v_e_6411_, 0);
                            v_idx_6484_ = crate::leanh::lean_ctor_get(v_e_6411_, 1);
                            v_struct_6485_ = crate::leanh::lean_ctor_get(v_e_6411_, 2);
                            crate::leanh::lean_inc_ref(v_struct_6485_);
                            v___x_6486_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_struct_6485_);
                            v___x_6487_ = lean_ptr_addr(v_struct_6485_);
                            v___x_6488_ = lean_ptr_addr(v___x_6486_);
                            v___x_6489_ = lean_usize_dec_eq(v___x_6487_, v___x_6488_);
                            if v___x_6489_ == 0 {
                                crate::leanh::lean_inc(v_idx_6484_);
                                crate::leanh::lean_inc(v_typeName_6483_);
                                crate::leanh::lean_dec_ref_known(v_e_6411_, 3);
                                v___x_6490_ = l_Lean_Expr_proj___override(
                                    v_typeName_6483_,
                                    v_idx_6484_,
                                    v___x_6486_,
                                );
                                return v___x_6490_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_6486_);
                                return v_e_6411_;
                            }
                        }
                        _ => {
                            return v_e_6411_;
                        }
                    }
                }
            }
            1 => {
                if v___y_6430_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_6411_, 2);
                    v___x_6431_ = l_Lean_Expr_app___override(v___x_6427_, v___x_6428_);
                    v___x_6432_ = l_Lean_Expr_headBeta(v___x_6431_);
                    return v___x_6432_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_6428_);
                    crate::leanh::lean_dec_ref(v___x_6427_);
                    v___x_6433_ = l_Lean_Expr_headBeta(v_e_6411_);
                    return v___x_6433_;
                }
            }
            2 => {
                if v___y_6447_ == 0 {
                    crate::leanh::lean_inc(v_binderName_6440_);
                    crate::leanh::lean_dec_ref_known(v_e_6411_, 3);
                    v___x_6448_ = l_Lean_Expr_lam___override(
                        v_binderName_6440_,
                        v___x_6444_,
                        v___x_6445_,
                        v_binderInfo_6443_,
                    );
                    return v___x_6448_;
                } else {
                    v___x_6449_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_6443_, v_binderInfo_6443_);
                    if v___x_6449_ == 0 {
                        crate::leanh::lean_inc(v_binderName_6440_);
                        crate::leanh::lean_dec_ref_known(v_e_6411_, 3);
                        v___x_6450_ = l_Lean_Expr_lam___override(
                            v_binderName_6440_,
                            v___x_6444_,
                            v___x_6445_,
                            v_binderInfo_6443_,
                        );
                        return v___x_6450_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6445_);
                        crate::leanh::lean_dec_ref(v___x_6444_);
                        return v_e_6411_;
                    }
                }
            }
            3 => {
                if v___y_6464_ == 0 {
                    crate::leanh::lean_inc(v_binderName_6457_);
                    crate::leanh::lean_dec_ref_known(v_e_6411_, 3);
                    v___x_6465_ = l_Lean_Expr_forallE___override(
                        v_binderName_6457_,
                        v___x_6461_,
                        v___x_6462_,
                        v_binderInfo_6460_,
                    );
                    return v___x_6465_;
                } else {
                    v___x_6466_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_6460_, v_binderInfo_6460_);
                    if v___x_6466_ == 0 {
                        crate::leanh::lean_inc(v_binderName_6457_);
                        crate::leanh::lean_dec_ref_known(v_e_6411_, 3);
                        v___x_6467_ = l_Lean_Expr_forallE___override(
                            v_binderName_6457_,
                            v___x_6461_,
                            v___x_6462_,
                            v_binderInfo_6460_,
                        );
                        return v___x_6467_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6462_);
                        crate::leanh::lean_dec_ref(v___x_6461_);
                        return v_e_6411_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(
    mut v_pu_6491_: u8,
    mut v_s_6492_: *mut crate::leanh::LeanObject,
    mut v_translator_6493_: u8,
    mut v_e_6494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6500_: u8 = 0;
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: usize = 0;
    let mut v___x_6503_: usize = 0;
    let mut v___x_6504_: u8 = 0;
    let mut v___x_6505_: usize = 0;
    let mut v___x_6506_: usize = 0;
    let mut v___x_6507_: u8 = 0;
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_6494_) == 5 {
                    v_fn_6495_ = crate::leanh::lean_ctor_get(v_e_6494_, 0);
                    v_arg_6496_ = crate::leanh::lean_ctor_get(v_e_6494_, 1);
                    crate::leanh::lean_inc_ref(v_fn_6495_);
                    v___x_6497_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_6491_, v_s_6492_, v_translator_6493_, v_fn_6495_);
                    crate::leanh::lean_inc_ref(v_arg_6496_);
                    v___x_6498_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6491_, v_s_6492_, v_translator_6493_, v_arg_6496_);
                    v___x_6502_ = lean_ptr_addr(v_fn_6495_);
                    v___x_6503_ = lean_ptr_addr(v___x_6497_);
                    v___x_6504_ = lean_usize_dec_eq(v___x_6502_, v___x_6503_);
                    if v___x_6504_ == 0 {
                        v___y_6500_ = v___x_6504_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6505_ = lean_ptr_addr(v_arg_6496_);
                        v___x_6506_ = lean_ptr_addr(v___x_6498_);
                        v___x_6507_ = lean_usize_dec_eq(v___x_6505_, v___x_6506_);
                        v___y_6500_ = v___x_6507_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6508_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6491_, v_s_6492_, v_translator_6493_, v_e_6494_);
                    return v___x_6508_;
                }
            }
            1 => {
                if v___y_6500_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_6494_, 2);
                    v___x_6501_ = l_Lean_Expr_app___override(v___x_6497_, v___x_6498_);
                    return v___x_6501_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_6498_);
                    crate::leanh::lean_dec_ref(v___x_6497_);
                    return v_e_6494_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(
    mut v_pu_6509_: *mut crate::leanh::LeanObject,
    mut v_s_6510_: *mut crate::leanh::LeanObject,
    mut v_translator_6511_: *mut crate::leanh::LeanObject,
    mut v_e_6512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6513_: u8 = 0;
    let mut v_translator_boxed_6514_: u8 = 0;
    let mut v_res_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6513_ = (crate::leanh::lean_unbox(v_pu_6509_) as u8);
    v_translator_boxed_6514_ = (crate::leanh::lean_unbox(v_translator_6511_) as u8);
    v_res_6515_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(
        v_pu_boxed_6513_,
        v_s_6510_,
        v_translator_boxed_6514_,
        v_e_6512_,
    );
    crate::leanh::lean_dec_ref(v_s_6510_);
    return v_res_6515_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(
    mut v_pu_6516_: *mut crate::leanh::LeanObject,
    mut v_s_6517_: *mut crate::leanh::LeanObject,
    mut v_translator_6518_: *mut crate::leanh::LeanObject,
    mut v_e_6519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6520_: u8 = 0;
    let mut v_translator_boxed_6521_: u8 = 0;
    let mut v_res_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6520_ = (crate::leanh::lean_unbox(v_pu_6516_) as u8);
    v_translator_boxed_6521_ = (crate::leanh::lean_unbox(v_translator_6518_) as u8);
    v_res_6522_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_boxed_6520_,
        v_s_6517_,
        v_translator_boxed_6521_,
        v_e_6519_,
    );
    crate::leanh::lean_dec_ref(v_s_6517_);
    return v_res_6522_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(
    mut v_pu_6523_: u8,
    mut v_s_6524_: *mut crate::leanh::LeanObject,
    mut v_e_6525_: *mut crate::leanh::LeanObject,
    mut v_translator_6526_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6527_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_6523_,
        v_s_6524_,
        v_translator_6526_,
        v_e_6525_,
    );
    return v___x_6527_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(
    mut v_pu_6528_: *mut crate::leanh::LeanObject,
    mut v_s_6529_: *mut crate::leanh::LeanObject,
    mut v_e_6530_: *mut crate::leanh::LeanObject,
    mut v_translator_6531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6532_: u8 = 0;
    let mut v_translator_boxed_6533_: u8 = 0;
    let mut v_res_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6532_ = (crate::leanh::lean_unbox(v_pu_6528_) as u8);
    v_translator_boxed_6533_ = (crate::leanh::lean_unbox(v_translator_6531_) as u8);
    v_res_6534_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(
        v_pu_boxed_6532_,
        v_s_6529_,
        v_e_6530_,
        v_translator_boxed_6533_,
    );
    crate::leanh::lean_dec_ref(v_s_6529_);
    return v_res_6534_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(
    mut v_x_6535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6535_) == 0 {
        let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6536_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_6536_;
    } else {
        let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6537_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_6537_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(
    mut v_x_6538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6539_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_6538_);
    crate::leanh::lean_dec(v_x_6538_);
    return v_res_6539_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(
    mut v_t_6540_: *mut crate::leanh::LeanObject,
    mut v_k_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_6540_) == 0 {
        let mut v_fvarId_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_6542_ = crate::leanh::lean_ctor_get(v_t_6540_, 0);
        crate::leanh::lean_inc(v_fvarId_6542_);
        crate::leanh::lean_dec_ref_known(v_t_6540_, 1);
        v___x_6543_ = crate::leanh::lean_apply_1(v_k_6541_, v_fvarId_6542_);
        return v___x_6543_;
    } else {
        return v_k_6541_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(
    mut v_motive_6544_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6545_: *mut crate::leanh::LeanObject,
    mut v_t_6546_: *mut crate::leanh::LeanObject,
    mut v_h_6547_: *mut crate::leanh::LeanObject,
    mut v_k_6548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6549_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6546_, v_k_6548_);
    return v___x_6549_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(
    mut v_motive_6550_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6551_: *mut crate::leanh::LeanObject,
    mut v_t_6552_: *mut crate::leanh::LeanObject,
    mut v_h_6553_: *mut crate::leanh::LeanObject,
    mut v_k_6554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6555_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(
        v_motive_6550_,
        v_ctorIdx_6551_,
        v_t_6552_,
        v_h_6553_,
        v_k_6554_,
    );
    crate::leanh::lean_dec(v_ctorIdx_6551_);
    return v_res_6555_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(
    mut v_t_6556_: *mut crate::leanh::LeanObject,
    mut v_fvar_6557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6556_, v_fvar_6557_);
    return v___x_6558_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(
    mut v_motive_6559_: *mut crate::leanh::LeanObject,
    mut v_t_6560_: *mut crate::leanh::LeanObject,
    mut v_h_6561_: *mut crate::leanh::LeanObject,
    mut v_fvar_6562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6563_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6560_, v_fvar_6562_);
    return v___x_6563_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(
    mut v_t_6564_: *mut crate::leanh::LeanObject,
    mut v_erased_6565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6566_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6564_, v_erased_6565_);
    return v___x_6566_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(
    mut v_motive_6567_: *mut crate::leanh::LeanObject,
    mut v_t_6568_: *mut crate::leanh::LeanObject,
    mut v_h_6569_: *mut crate::leanh::LeanObject,
    mut v_erased_6570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6571_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6568_, v_erased_6570_);
    return v___x_6571_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp___redArg(
    mut v_s_6576_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6577_: *mut crate::leanh::LeanObject,
    mut v_translator_6578_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6576_, v_fvarId_6577_);
                if crate::leanh::lean_obj_tag(v___x_6579_) == 0 {
                    v___x_6580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6580_, 0, v_fvarId_6577_);
                    return v___x_6580_;
                } else {
                    crate::leanh::lean_dec(v_fvarId_6577_);
                    v_val_6581_ = crate::leanh::lean_ctor_get(v___x_6579_, 0);
                    crate::leanh::lean_inc(v_val_6581_);
                    crate::leanh::lean_dec_ref_known(v___x_6579_, 1);
                    if crate::leanh::lean_obj_tag(v_val_6581_) == 1 {
                        if v_translator_6578_ == 0 {
                            v_fvarId_6582_ = crate::leanh::lean_ctor_get(v_val_6581_, 0);
                            crate::leanh::lean_inc(v_fvarId_6582_);
                            crate::leanh::lean_dec_ref_known(v_val_6581_, 1);
                            v_fvarId_6577_ = v_fvarId_6582_;
                            state = 0;
                            continue;
                        } else {
                            v_fvarId_6584_ = crate::leanh::lean_ctor_get(v_val_6581_, 0);
                            v_isSharedCheck_6591_ =
                                (!crate::leanh::lean_is_exclusive(v_val_6581_)) as u8;
                            if v_isSharedCheck_6591_ == 0 {
                                v___x_6586_ = v_val_6581_;
                                v_isShared_6587_ = v_isSharedCheck_6591_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fvarId_6584_);
                                crate::leanh::lean_dec(v_val_6581_);
                                v___x_6586_ = crate::leanh::lean_box(0);
                                v_isShared_6587_ = v_isSharedCheck_6591_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_6581_);
                        v___x_6592_ = crate::leanh::lean_box(1);
                        return v___x_6592_;
                    }
                }
            }
            1 => {
                if v_isShared_6587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6586_, 0);
                    v___x_6589_ = v___x_6586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_fvarId_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp___redArg___boxed(
    mut v_s_6593_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6594_: *mut crate::leanh::LeanObject,
    mut v_translator_6595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_translator_boxed_6596_: u8 = 0;
    let mut v_res_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_translator_boxed_6596_ = (crate::leanh::lean_unbox(v_translator_6595_) as u8);
    v_res_6597_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
        v_s_6593_,
        v_fvarId_6594_,
        v_translator_boxed_6596_,
    );
    crate::leanh::lean_dec_ref(v_s_6593_);
    return v_res_6597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp(
    mut v_pu_6598_: u8,
    mut v_s_6599_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6600_: *mut crate::leanh::LeanObject,
    mut v_translator_6601_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6602_ =
        l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_6599_, v_fvarId_6600_, v_translator_6601_);
    return v___x_6602_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp___boxed(
    mut v_pu_6603_: *mut crate::leanh::LeanObject,
    mut v_s_6604_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6605_: *mut crate::leanh::LeanObject,
    mut v_translator_6606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6607_: u8 = 0;
    let mut v_translator_boxed_6608_: u8 = 0;
    let mut v_res_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6607_ = (crate::leanh::lean_unbox(v_pu_6603_) as u8);
    v_translator_boxed_6608_ = (crate::leanh::lean_unbox(v_translator_6606_) as u8);
    v_res_6609_ = l_Lean_Compiler_LCNF_normFVarImp(
        v_pu_boxed_6607_,
        v_s_6604_,
        v_fvarId_6605_,
        v_translator_boxed_6608_,
    );
    crate::leanh::lean_dec_ref(v_s_6604_);
    return v_res_6609_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
    mut v_pu_6610_: u8,
    mut v_s_6611_: *mut crate::leanh::LeanObject,
    mut v_arg_6612_: *mut crate::leanh::LeanObject,
    mut v_translator_6613_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6626_: u8 = 0;
    let mut v_expr_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6630_: u8 = 0;
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v_expr_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_arg_6612_) {
                0 => {
                    return v_arg_6612_;
                }
                1 => {
                    v_fvarId_6614_ = crate::leanh::lean_ctor_get(v_arg_6612_, 0);
                    v___x_6615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6611_, v_fvarId_6614_);
                    if crate::leanh::lean_obj_tag(v___x_6615_) == 0 {
                        return v_arg_6612_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_arg_6612_, 1);
                        v_val_6616_ = crate::leanh::lean_ctor_get(v___x_6615_, 0);
                        crate::leanh::lean_inc(v_val_6616_);
                        crate::leanh::lean_dec_ref_known(v___x_6615_, 1);
                        match crate::leanh::lean_obj_tag(v_val_6616_) {
                            0 => {
                                v___x_6617_ = crate::leanh::lean_box(0);
                                return v___x_6617_;
                            }
                            1 => {
                                v_fvarId_6618_ = crate::leanh::lean_ctor_get(v_val_6616_, 0);
                                v_isSharedCheck_6626_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_6616_)) as u8;
                                if v_isSharedCheck_6626_ == 0 {
                                    v___x_6620_ = v_val_6616_;
                                    v_isShared_6621_ = v_isSharedCheck_6626_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fvarId_6618_);
                                    crate::leanh::lean_dec(v_val_6616_);
                                    v___x_6620_ = crate::leanh::lean_box(0);
                                    v_isShared_6621_ = v_isSharedCheck_6626_;
                                    state = 1;
                                    continue;
                                }
                            }
                            _ => {
                                v_expr_6627_ = crate::leanh::lean_ctor_get(v_val_6616_, 0);
                                v_isSharedCheck_6634_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_6616_)) as u8;
                                if v_isSharedCheck_6634_ == 0 {
                                    v___x_6629_ = v_val_6616_;
                                    v_isShared_6630_ = v_isSharedCheck_6634_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_expr_6627_);
                                    crate::leanh::lean_dec(v_val_6616_);
                                    v___x_6629_ = crate::leanh::lean_box(0);
                                    v_isShared_6630_ = v_isSharedCheck_6634_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {
                    v_expr_6635_ = crate::leanh::lean_ctor_get(v_arg_6612_, 0);
                    crate::leanh::lean_inc_ref(v_expr_6635_);
                    v___x_6636_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6610_, v_s_6611_, v_translator_6613_, v_expr_6635_);
                    v___x_6637_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(v_pu_6610_, v_arg_6612_, v___x_6636_);
                    return v___x_6637_;
                }
            },
            1 => {
                if v_isShared_6621_ == 0 {
                    v___x_6623_ = v___x_6620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_fvarId_6618_);
                    v___x_6623_ = v_reuseFailAlloc_6625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_translator_6613_ == 0 {
                    v_arg_6612_ = v___x_6623_;
                    state = 0;
                    continue;
                } else {
                    return v___x_6623_;
                }
            }
            3 => {
                if v_isShared_6630_ == 0 {
                    v___x_6632_ = v___x_6629_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6633_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_expr_6627_);
                    v___x_6632_ = v_reuseFailAlloc_6633_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp___boxed(
    mut v_pu_6638_: *mut crate::leanh::LeanObject,
    mut v_s_6639_: *mut crate::leanh::LeanObject,
    mut v_arg_6640_: *mut crate::leanh::LeanObject,
    mut v_translator_6641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6642_: u8 = 0;
    let mut v_translator_boxed_6643_: u8 = 0;
    let mut v_res_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6642_ = (crate::leanh::lean_unbox(v_pu_6638_) as u8);
    v_translator_boxed_6643_ = (crate::leanh::lean_unbox(v_translator_6641_) as u8);
    v_res_6644_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
        v_pu_boxed_6642_,
        v_s_6639_,
        v_arg_6640_,
        v_translator_boxed_6643_,
    );
    crate::leanh::lean_dec_ref(v_s_6639_);
    return v_res_6644_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(
    mut v_pu_6645_: u8,
    mut v_s_6646_: *mut crate::leanh::LeanObject,
    mut v_translator_6647_: u8,
    mut v_i_6648_: *mut crate::leanh::LeanObject,
    mut v_as_6649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: u8 = 0;
    let mut v_a_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: usize = 0;
    let mut v___x_6655_: usize = 0;
    let mut v___x_6656_: u8 = 0;
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6650_ = lean_array_get_size(v_as_6649_);
                v___x_6651_ = lean_nat_dec_lt(v_i_6648_, v___x_6650_);
                if v___x_6651_ == 0 {
                    crate::leanh::lean_dec(v_i_6648_);
                    return v_as_6649_;
                } else {
                    v_a_6652_ = lean_array_fget_borrowed(v_as_6649_, v_i_6648_);
                    crate::leanh::lean_inc(v_a_6652_);
                    v___x_6653_ =
                        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
                            v_pu_6645_,
                            v_s_6646_,
                            v_a_6652_,
                            v_translator_6647_,
                        );
                    v___x_6654_ = lean_ptr_addr(v_a_6652_);
                    v___x_6655_ = lean_ptr_addr(v___x_6653_);
                    v___x_6656_ = lean_usize_dec_eq(v___x_6654_, v___x_6655_);
                    if v___x_6656_ == 0 {
                        v___x_6657_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6658_ = lean_nat_add(v_i_6648_, v___x_6657_);
                        v___x_6659_ = lean_array_fset(v_as_6649_, v_i_6648_, v___x_6653_);
                        crate::leanh::lean_dec(v_i_6648_);
                        v_i_6648_ = v___x_6658_;
                        v_as_6649_ = v___x_6659_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6653_);
                        v___x_6661_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6662_ = lean_nat_add(v_i_6648_, v___x_6661_);
                        crate::leanh::lean_dec(v_i_6648_);
                        v_i_6648_ = v___x_6662_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0___boxed(
    mut v_pu_6664_: *mut crate::leanh::LeanObject,
    mut v_s_6665_: *mut crate::leanh::LeanObject,
    mut v_translator_6666_: *mut crate::leanh::LeanObject,
    mut v_i_6667_: *mut crate::leanh::LeanObject,
    mut v_as_6668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6669_: u8 = 0;
    let mut v_translator_boxed_6670_: u8 = 0;
    let mut v_res_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6669_ = (crate::leanh::lean_unbox(v_pu_6664_) as u8);
    v_translator_boxed_6670_ = (crate::leanh::lean_unbox(v_translator_6666_) as u8);
    v_res_6671_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_6669_, v_s_6665_, v_translator_boxed_6670_, v_i_6667_, v_as_6668_);
    crate::leanh::lean_dec_ref(v_s_6665_);
    return v_res_6671_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
    mut v_pu_6672_: u8,
    mut v_s_6673_: *mut crate::leanh::LeanObject,
    mut v_args_6674_: *mut crate::leanh::LeanObject,
    mut v_translator_6675_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6676_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6677_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_6672_, v_s_6673_, v_translator_6675_, v___x_6676_, v_args_6674_);
    return v___x_6677_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(
    mut v_pu_6678_: *mut crate::leanh::LeanObject,
    mut v_s_6679_: *mut crate::leanh::LeanObject,
    mut v_args_6680_: *mut crate::leanh::LeanObject,
    mut v_translator_6681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6682_: u8 = 0;
    let mut v_translator_boxed_6683_: u8 = 0;
    let mut v_res_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6682_ = (crate::leanh::lean_unbox(v_pu_6678_) as u8);
    v_translator_boxed_6683_ = (crate::leanh::lean_unbox(v_translator_6681_) as u8);
    v_res_6684_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_boxed_6682_,
        v_s_6679_,
        v_args_6680_,
        v_translator_boxed_6683_,
    );
    crate::leanh::lean_dec_ref(v_s_6679_);
    return v_res_6684_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
    mut v_pu_6685_: u8,
    mut v_s_6686_: *mut crate::leanh::LeanObject,
    mut v_e_6687_: *mut crate::leanh::LeanObject,
    mut v_translator_6688_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_6734_: u8 = 0;
    let mut v_args_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_e_6687_) {
                    2 => {
                        v_struct_6699_ = crate::leanh::lean_ctor_get(v_e_6687_, 2);
                        crate::leanh::lean_inc(v_struct_6699_);
                        v___x_6700_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_struct_6699_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6700_) == 0 {
                            v_fvarId_6701_ = crate::leanh::lean_ctor_get(v___x_6700_, 0);
                            crate::leanh::lean_inc(v_fvarId_6701_);
                            crate::leanh::lean_dec_ref_known(v___x_6700_, 1);
                            v___x_6702_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6701_);
                            return v___x_6702_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6703_ = crate::leanh::lean_box(1);
                            return v___x_6703_;
                        }
                    }
                    3 => {
                        v_args_6704_ = crate::leanh::lean_ctor_get(v_e_6687_, 2);
                        crate::leanh::lean_inc_ref(v_args_6704_);
                        v___x_6705_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6704_, v_translator_6688_);
                        v___x_6706_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_6685_, v_e_6687_, v___x_6705_);
                        return v___x_6706_;
                    }
                    4 => {
                        v_fvarId_6707_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        v_args_6708_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc(v_fvarId_6707_);
                        v___x_6709_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6707_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6709_) == 0 {
                            v_fvarId_6710_ = crate::leanh::lean_ctor_get(v___x_6709_, 0);
                            crate::leanh::lean_inc(v_fvarId_6710_);
                            crate::leanh::lean_dec_ref_known(v___x_6709_, 1);
                            crate::leanh::lean_inc_ref(v_args_6708_);
                            v___x_6711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6708_, v_translator_6688_);
                            v___x_6712_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_6685_, v_e_6687_, v_fvarId_6710_, v___x_6711_);
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6712_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            v___x_6713_ = crate::leanh::lean_box(1);
                            return v___x_6713_;
                        }
                    }
                    5 => {
                        v_args_6714_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc_ref(v_args_6714_);
                        v___x_6715_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6714_, v_translator_6688_);
                        v___x_6716_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_6685_, v_e_6687_, v___x_6715_);
                        return v___x_6716_;
                    }
                    6 => {
                        v_var_6717_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc(v_var_6717_);
                        v_fvarId_6690_ = v_var_6717_;
                        state = 1;
                        continue;
                    }
                    7 => {
                        v_var_6718_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc(v_var_6718_);
                        v_fvarId_6690_ = v_var_6718_;
                        state = 1;
                        continue;
                    }
                    8 => {
                        v_var_6719_ = crate::leanh::lean_ctor_get(v_e_6687_, 2);
                        crate::leanh::lean_inc(v_var_6719_);
                        v___x_6720_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6719_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6720_) == 0 {
                            v_fvarId_6721_ = crate::leanh::lean_ctor_get(v___x_6720_, 0);
                            crate::leanh::lean_inc(v_fvarId_6721_);
                            crate::leanh::lean_dec_ref_known(v___x_6720_, 1);
                            v___x_6722_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6721_);
                            return v___x_6722_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6723_ = crate::leanh::lean_box(1);
                            return v___x_6723_;
                        }
                    }
                    9 => {
                        v_args_6724_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc_ref(v_args_6724_);
                        v_args_6696_ = v_args_6724_;
                        state = 2;
                        continue;
                    }
                    10 => {
                        v_args_6725_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc_ref(v_args_6725_);
                        v_args_6696_ = v_args_6725_;
                        state = 2;
                        continue;
                    }
                    11 => {
                        v_n_6726_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        crate::leanh::lean_inc(v_n_6726_);
                        v_var_6727_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc(v_var_6727_);
                        v___x_6728_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6727_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6728_) == 0 {
                            v_fvarId_6729_ = crate::leanh::lean_ctor_get(v___x_6728_, 0);
                            crate::leanh::lean_inc(v_fvarId_6729_);
                            crate::leanh::lean_dec_ref_known(v___x_6728_, 1);
                            v___x_6730_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_6685_, v_e_6687_, v_n_6726_, v_fvarId_6729_);
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6730_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            crate::leanh::lean_dec(v_n_6726_);
                            v___x_6731_ = crate::leanh::lean_box(1);
                            return v___x_6731_;
                        }
                    }
                    12 => {
                        v_var_6732_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        v_i_6733_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc_ref(v_i_6733_);
                        v_updateHeader_6734_ = crate::leanh::lean_ctor_get_uint8(
                            v_e_6687_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_args_6735_ = crate::leanh::lean_ctor_get(v_e_6687_, 2);
                        crate::leanh::lean_inc(v_var_6732_);
                        v___x_6736_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6732_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6736_) == 0 {
                            v_fvarId_6737_ = crate::leanh::lean_ctor_get(v___x_6736_, 0);
                            crate::leanh::lean_inc(v_fvarId_6737_);
                            crate::leanh::lean_dec_ref_known(v___x_6736_, 1);
                            crate::leanh::lean_inc_ref(v_args_6735_);
                            v___x_6738_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6735_, v_translator_6688_);
                            v___x_6739_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_6685_, v_e_6687_, v_fvarId_6737_, v_i_6733_, v_updateHeader_6734_, v___x_6738_);
                            return v___x_6739_;
                        } else {
                            crate::leanh::lean_dec_ref(v_i_6733_);
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6740_ = crate::leanh::lean_box(1);
                            return v___x_6740_;
                        }
                    }
                    13 => {
                        v_ty_6741_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        crate::leanh::lean_inc_ref(v_ty_6741_);
                        v_fvarId_6742_ = crate::leanh::lean_ctor_get(v_e_6687_, 1);
                        crate::leanh::lean_inc(v_fvarId_6742_);
                        v___x_6743_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6742_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6743_) == 0 {
                            v_fvarId_6744_ = crate::leanh::lean_ctor_get(v___x_6743_, 0);
                            crate::leanh::lean_inc(v_fvarId_6744_);
                            crate::leanh::lean_dec_ref_known(v___x_6743_, 1);
                            v___x_6745_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_6685_, v_e_6687_, v_ty_6741_, v_fvarId_6744_);
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6745_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 2);
                            crate::leanh::lean_dec_ref(v_ty_6741_);
                            v___x_6746_ = crate::leanh::lean_box(1);
                            return v___x_6746_;
                        }
                    }
                    14 => {
                        v_fvarId_6747_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        crate::leanh::lean_inc(v_fvarId_6747_);
                        v___x_6748_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6747_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6748_) == 0 {
                            v_fvarId_6749_ = crate::leanh::lean_ctor_get(v___x_6748_, 0);
                            crate::leanh::lean_inc(v_fvarId_6749_);
                            crate::leanh::lean_dec_ref_known(v___x_6748_, 1);
                            v___x_6750_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_6685_, v_e_6687_, v_fvarId_6749_);
                            return v___x_6750_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 1);
                            v___x_6751_ = crate::leanh::lean_box(1);
                            return v___x_6751_;
                        }
                    }
                    15 => {
                        v_fvarId_6752_ = crate::leanh::lean_ctor_get(v_e_6687_, 0);
                        crate::leanh::lean_inc(v_fvarId_6752_);
                        v___x_6753_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6752_,
                            v_translator_6688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6753_) == 0 {
                            v_fvarId_6754_ = crate::leanh::lean_ctor_get(v___x_6753_, 0);
                            crate::leanh::lean_inc(v_fvarId_6754_);
                            crate::leanh::lean_dec_ref_known(v___x_6753_, 1);
                            v___x_6755_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_6685_, v_e_6687_, v_fvarId_6754_);
                            return v___x_6755_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_6687_, 1);
                            v___x_6756_ = crate::leanh::lean_box(1);
                            return v___x_6756_;
                        }
                    }
                    _ => {
                        return v_e_6687_;
                    }
                }
            }
            1 => {
                v___x_6691_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_s_6686_,
                    v_fvarId_6690_,
                    v_translator_6688_,
                );
                if crate::leanh::lean_obj_tag(v___x_6691_) == 0 {
                    v_fvarId_6692_ = crate::leanh::lean_ctor_get(v___x_6691_, 0);
                    crate::leanh::lean_inc(v_fvarId_6692_);
                    crate::leanh::lean_dec_ref_known(v___x_6691_, 1);
                    v___x_6693_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6692_);
                    return v___x_6693_;
                } else {
                    crate::leanh::lean_dec(v_e_6687_);
                    v___x_6694_ = crate::leanh::lean_box(1);
                    return v___x_6694_;
                }
            }
            2 => {
                v___x_6697_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
                        v_pu_6685_,
                        v_s_6686_,
                        v_args_6696_,
                        v_translator_6688_,
                    );
                v___x_6698_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_6685_, v_e_6687_, v___x_6697_);
                return v___x_6698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp___boxed(
    mut v_pu_6757_: *mut crate::leanh::LeanObject,
    mut v_s_6758_: *mut crate::leanh::LeanObject,
    mut v_e_6759_: *mut crate::leanh::LeanObject,
    mut v_translator_6760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6761_: u8 = 0;
    let mut v_translator_boxed_6762_: u8 = 0;
    let mut v_res_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6761_ = (crate::leanh::lean_unbox(v_pu_6757_) as u8);
    v_translator_boxed_6762_ = (crate::leanh::lean_unbox(v_translator_6760_) as u8);
    v_res_6763_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_boxed_6761_,
        v_s_6758_,
        v_e_6759_,
        v_translator_boxed_6762_,
    );
    crate::leanh::lean_dec_ref(v_s_6758_);
    return v_res_6763_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(
    mut v_inst_6764_: *mut crate::leanh::LeanObject,
    mut v_inst_6765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6766_ = crate::leanh::lean_apply_2(v_inst_6764_, crate::leanh::lean_box(0), v_inst_6765_);
    return v___x_6766_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(
    mut v_pu_6767_: u8,
    mut v_t_6768_: u8,
    mut v_m_6769_: *mut crate::leanh::LeanObject,
    mut v_n_6770_: *mut crate::leanh::LeanObject,
    mut v_inst_6771_: *mut crate::leanh::LeanObject,
    mut v_inst_6772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6773_ = crate::leanh::lean_apply_2(v_inst_6771_, crate::leanh::lean_box(0), v_inst_6772_);
    return v___x_6773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(
    mut v_pu_6774_: *mut crate::leanh::LeanObject,
    mut v_t_6775_: *mut crate::leanh::LeanObject,
    mut v_m_6776_: *mut crate::leanh::LeanObject,
    mut v_n_6777_: *mut crate::leanh::LeanObject,
    mut v_inst_6778_: *mut crate::leanh::LeanObject,
    mut v_inst_6779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6780_: u8 = 0;
    let mut v_t_boxed_6781_: u8 = 0;
    let mut v_res_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6780_ = (crate::leanh::lean_unbox(v_pu_6774_) as u8);
    v_t_boxed_6781_ = (crate::leanh::lean_unbox(v_t_6775_) as u8);
    v_res_6782_ = l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(
        v_pu_boxed_6780_,
        v_t_boxed_6781_,
        v_m_6776_,
        v_n_6777_,
        v_inst_6778_,
        v_inst_6779_,
    );
    return v_res_6782_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0(
    mut v_inst_6783_: *mut crate::leanh::LeanObject,
    mut v_inst_6784_: *mut crate::leanh::LeanObject,
    mut v_f_6785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6786_ = crate::leanh::lean_apply_1(v_inst_6783_, v_f_6785_);
    v___x_6787_ = crate::leanh::lean_apply_2(v_inst_6784_, crate::leanh::lean_box(0), v___x_6786_);
    return v___x_6787_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(
    mut v_inst_6788_: *mut crate::leanh::LeanObject,
    mut v_inst_6789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6790_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6790_, 0, v_inst_6789_);
    crate::leanh::lean_closure_set(v___f_6790_, 1, v_inst_6788_);
    return v___f_6790_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(
    mut v_pu_6791_: u8,
    mut v_m_6792_: *mut crate::leanh::LeanObject,
    mut v_n_6793_: *mut crate::leanh::LeanObject,
    mut v_inst_6794_: *mut crate::leanh::LeanObject,
    mut v_inst_6795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6796_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6796_, 0, v_inst_6795_);
    crate::leanh::lean_closure_set(v___f_6796_, 1, v_inst_6794_);
    return v___f_6796_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(
    mut v_pu_6797_: *mut crate::leanh::LeanObject,
    mut v_m_6798_: *mut crate::leanh::LeanObject,
    mut v_n_6799_: *mut crate::leanh::LeanObject,
    mut v_inst_6800_: *mut crate::leanh::LeanObject,
    mut v_inst_6801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6802_: u8 = 0;
    let mut v_res_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6802_ = (crate::leanh::lean_unbox(v_pu_6797_) as u8);
    v_res_6803_ = l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(
        v_pu_boxed_6802_,
        v_m_6798_,
        v_n_6799_,
        v_inst_6800_,
        v_inst_6801_,
    );
    return v_res_6803_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst___redArg___lam__0(
    mut v___x_6804_: *mut crate::leanh::LeanObject,
    mut v___x_6805_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6806_: *mut crate::leanh::LeanObject,
    mut v_arg_6807_: *mut crate::leanh::LeanObject,
    mut v_s_6808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6809_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_6804_,
        v___x_6805_,
        v_s_6808_,
        v_fvarId_6806_,
        v_arg_6807_,
    );
    return v___x_6809_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst___redArg(
    mut v_inst_6812_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6813_: *mut crate::leanh::LeanObject,
    mut v_arg_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6815_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6816_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6817_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_addSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6817_, 0, v___x_6815_);
    crate::leanh::lean_closure_set(v___f_6817_, 1, v___x_6816_);
    crate::leanh::lean_closure_set(v___f_6817_, 2, v_fvarId_6813_);
    crate::leanh::lean_closure_set(v___f_6817_, 3, v_arg_6814_);
    v___x_6818_ = crate::leanh::lean_apply_1(v_inst_6812_, v___f_6817_);
    return v___x_6818_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst(
    mut v_m_6819_: *mut crate::leanh::LeanObject,
    mut v_pu_6820_: u8,
    mut v_inst_6821_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6822_: *mut crate::leanh::LeanObject,
    mut v_arg_6823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6824_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6825_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6826_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_addSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6826_, 0, v___x_6824_);
    crate::leanh::lean_closure_set(v___f_6826_, 1, v___x_6825_);
    crate::leanh::lean_closure_set(v___f_6826_, 2, v_fvarId_6822_);
    crate::leanh::lean_closure_set(v___f_6826_, 3, v_arg_6823_);
    v___x_6827_ = crate::leanh::lean_apply_1(v_inst_6821_, v___f_6826_);
    return v___x_6827_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst___boxed(
    mut v_m_6828_: *mut crate::leanh::LeanObject,
    mut v_pu_6829_: *mut crate::leanh::LeanObject,
    mut v_inst_6830_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6831_: *mut crate::leanh::LeanObject,
    mut v_arg_6832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6833_: u8 = 0;
    let mut v_res_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6833_ = (crate::leanh::lean_unbox(v_pu_6829_) as u8);
    v_res_6834_ = l_Lean_Compiler_LCNF_addSubst(
        v_m_6828_,
        v_pu_boxed_6833_,
        v_inst_6830_,
        v_fvarId_6831_,
        v_arg_6832_,
    );
    return v_res_6834_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0(
    mut v_fvarId_x27_6835_: *mut crate::leanh::LeanObject,
    mut v___x_6836_: *mut crate::leanh::LeanObject,
    mut v___x_6837_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6838_: *mut crate::leanh::LeanObject,
    mut v_s_6839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6840_, 0, v_fvarId_x27_6835_);
    v___x_6841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_6836_,
        v___x_6837_,
        v_s_6839_,
        v_fvarId_6838_,
        v___x_6840_,
    );
    return v___x_6841_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst___redArg(
    mut v_inst_6842_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6843_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_6844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6845_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6846_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6847_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6847_, 0, v_fvarId_x27_6844_);
    crate::leanh::lean_closure_set(v___f_6847_, 1, v___x_6845_);
    crate::leanh::lean_closure_set(v___f_6847_, 2, v___x_6846_);
    crate::leanh::lean_closure_set(v___f_6847_, 3, v_fvarId_6843_);
    v___x_6848_ = crate::leanh::lean_apply_1(v_inst_6842_, v___f_6847_);
    return v___x_6848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst(
    mut v_m_6849_: *mut crate::leanh::LeanObject,
    mut v_ph_6850_: u8,
    mut v_inst_6851_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6852_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_6853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6854_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6855_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6856_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6856_, 0, v_fvarId_x27_6853_);
    crate::leanh::lean_closure_set(v___f_6856_, 1, v___x_6854_);
    crate::leanh::lean_closure_set(v___f_6856_, 2, v___x_6855_);
    crate::leanh::lean_closure_set(v___f_6856_, 3, v_fvarId_6852_);
    v___x_6857_ = crate::leanh::lean_apply_1(v_inst_6851_, v___f_6856_);
    return v___x_6857_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst___boxed(
    mut v_m_6858_: *mut crate::leanh::LeanObject,
    mut v_ph_6859_: *mut crate::leanh::LeanObject,
    mut v_inst_6860_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6861_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_6862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ph_boxed_6863_: u8 = 0;
    let mut v_res_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ph_boxed_6863_ = (crate::leanh::lean_unbox(v_ph_6859_) as u8);
    v_res_6864_ = l_Lean_Compiler_LCNF_addFVarSubst(
        v_m_6858_,
        v_ph_boxed_6863_,
        v_inst_6860_,
        v_fvarId_6861_,
        v_fvarId_x27_6862_,
    );
    return v_res_6864_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(
    mut v_fvarId_6865_: *mut crate::leanh::LeanObject,
    mut v_t_6866_: u8,
    mut v_toPure_6867_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6869_ =
        l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_6868_, v_fvarId_6865_, v_t_6866_);
    v___x_6870_ =
        crate::leanh::lean_apply_2(v_toPure_6867_, crate::leanh::lean_box(0), v___x_6869_);
    return v___x_6870_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(
    mut v_fvarId_6871_: *mut crate::leanh::LeanObject,
    mut v_t_6872_: *mut crate::leanh::LeanObject,
    mut v_toPure_6873_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_6875_: u8 = 0;
    let mut v_res_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_6875_ = (crate::leanh::lean_unbox(v_t_6872_) as u8);
    v_res_6876_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(
        v_fvarId_6871_,
        v_t_boxed_6875_,
        v_toPure_6873_,
        v_____do__lift_6874_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_6874_);
    return v_res_6876_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg(
    mut v_t_6877_: u8,
    mut v_inst_6878_: *mut crate::leanh::LeanObject,
    mut v_inst_6879_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6881_ = crate::leanh::lean_ctor_get(v_inst_6879_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6881_);
    v_toBind_6882_ = crate::leanh::lean_ctor_get(v_inst_6879_, 1);
    crate::leanh::lean_inc(v_toBind_6882_);
    crate::leanh::lean_dec_ref(v_inst_6879_);
    v_toPure_6883_ = crate::leanh::lean_ctor_get(v_toApplicative_6881_, 1);
    crate::leanh::lean_inc(v_toPure_6883_);
    crate::leanh::lean_dec_ref(v_toApplicative_6881_);
    v___x_6884_ = crate::leanh::lean_box((v_t_6877_) as usize);
    v___f_6885_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6885_, 0, v_fvarId_6880_);
    crate::leanh::lean_closure_set(v___f_6885_, 1, v___x_6884_);
    crate::leanh::lean_closure_set(v___f_6885_, 2, v_toPure_6883_);
    v___x_6886_ = crate::leanh::lean_apply_4(
        v_toBind_6882_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6878_,
        v___f_6885_,
    );
    return v___x_6886_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg___boxed(
    mut v_t_6887_: *mut crate::leanh::LeanObject,
    mut v_inst_6888_: *mut crate::leanh::LeanObject,
    mut v_inst_6889_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_6891_: u8 = 0;
    let mut v_res_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_6891_ = (crate::leanh::lean_unbox(v_t_6887_) as u8);
    v_res_6892_ = l_Lean_Compiler_LCNF_normFVar___redArg(
        v_t_boxed_6891_,
        v_inst_6888_,
        v_inst_6889_,
        v_fvarId_6890_,
    );
    return v_res_6892_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar(
    mut v_m_6893_: *mut crate::leanh::LeanObject,
    mut v_pu_6894_: u8,
    mut v_t_6895_: u8,
    mut v_inst_6896_: *mut crate::leanh::LeanObject,
    mut v_inst_6897_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6899_ = crate::leanh::lean_ctor_get(v_inst_6897_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6899_);
    v_toBind_6900_ = crate::leanh::lean_ctor_get(v_inst_6897_, 1);
    crate::leanh::lean_inc(v_toBind_6900_);
    crate::leanh::lean_dec_ref(v_inst_6897_);
    v_toPure_6901_ = crate::leanh::lean_ctor_get(v_toApplicative_6899_, 1);
    crate::leanh::lean_inc(v_toPure_6901_);
    crate::leanh::lean_dec_ref(v_toApplicative_6899_);
    v___x_6902_ = crate::leanh::lean_box((v_t_6895_) as usize);
    v___f_6903_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6903_, 0, v_fvarId_6898_);
    crate::leanh::lean_closure_set(v___f_6903_, 1, v___x_6902_);
    crate::leanh::lean_closure_set(v___f_6903_, 2, v_toPure_6901_);
    v___x_6904_ = crate::leanh::lean_apply_4(
        v_toBind_6900_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6896_,
        v___f_6903_,
    );
    return v___x_6904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___boxed(
    mut v_m_6905_: *mut crate::leanh::LeanObject,
    mut v_pu_6906_: *mut crate::leanh::LeanObject,
    mut v_t_6907_: *mut crate::leanh::LeanObject,
    mut v_inst_6908_: *mut crate::leanh::LeanObject,
    mut v_inst_6909_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6911_: u8 = 0;
    let mut v_t_boxed_6912_: u8 = 0;
    let mut v_res_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6911_ = (crate::leanh::lean_unbox(v_pu_6906_) as u8);
    v_t_boxed_6912_ = (crate::leanh::lean_unbox(v_t_6907_) as u8);
    v_res_6913_ = l_Lean_Compiler_LCNF_normFVar(
        v_m_6905_,
        v_pu_boxed_6911_,
        v_t_boxed_6912_,
        v_inst_6908_,
        v_inst_6909_,
        v_fvarId_6910_,
    );
    return v_res_6913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(
    mut v_pu_6914_: u8,
    mut v_t_6915_: u8,
    mut v_e_6916_: *mut crate::leanh::LeanObject,
    mut v_toPure_6917_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6919_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_6914_,
        v_____do__lift_6918_,
        v_t_6915_,
        v_e_6916_,
    );
    v___x_6920_ =
        crate::leanh::lean_apply_2(v_toPure_6917_, crate::leanh::lean_box(0), v___x_6919_);
    return v___x_6920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(
    mut v_pu_6921_: *mut crate::leanh::LeanObject,
    mut v_t_6922_: *mut crate::leanh::LeanObject,
    mut v_e_6923_: *mut crate::leanh::LeanObject,
    mut v_toPure_6924_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6926_: u8 = 0;
    let mut v_t_boxed_6927_: u8 = 0;
    let mut v_res_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6926_ = (crate::leanh::lean_unbox(v_pu_6921_) as u8);
    v_t_boxed_6927_ = (crate::leanh::lean_unbox(v_t_6922_) as u8);
    v_res_6928_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(
        v_pu_boxed_6926_,
        v_t_boxed_6927_,
        v_e_6923_,
        v_toPure_6924_,
        v_____do__lift_6925_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_6925_);
    return v_res_6928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg(
    mut v_pu_6929_: u8,
    mut v_t_6930_: u8,
    mut v_inst_6931_: *mut crate::leanh::LeanObject,
    mut v_inst_6932_: *mut crate::leanh::LeanObject,
    mut v_e_6933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6934_ = crate::leanh::lean_ctor_get(v_inst_6932_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6934_);
    v_toBind_6935_ = crate::leanh::lean_ctor_get(v_inst_6932_, 1);
    crate::leanh::lean_inc(v_toBind_6935_);
    crate::leanh::lean_dec_ref(v_inst_6932_);
    v_toPure_6936_ = crate::leanh::lean_ctor_get(v_toApplicative_6934_, 1);
    crate::leanh::lean_inc(v_toPure_6936_);
    crate::leanh::lean_dec_ref(v_toApplicative_6934_);
    v___x_6937_ = crate::leanh::lean_box((v_pu_6929_) as usize);
    v___x_6938_ = crate::leanh::lean_box((v_t_6930_) as usize);
    v___f_6939_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6939_, 0, v___x_6937_);
    crate::leanh::lean_closure_set(v___f_6939_, 1, v___x_6938_);
    crate::leanh::lean_closure_set(v___f_6939_, 2, v_e_6933_);
    crate::leanh::lean_closure_set(v___f_6939_, 3, v_toPure_6936_);
    v___x_6940_ = crate::leanh::lean_apply_4(
        v_toBind_6935_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6931_,
        v___f_6939_,
    );
    return v___x_6940_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg___boxed(
    mut v_pu_6941_: *mut crate::leanh::LeanObject,
    mut v_t_6942_: *mut crate::leanh::LeanObject,
    mut v_inst_6943_: *mut crate::leanh::LeanObject,
    mut v_inst_6944_: *mut crate::leanh::LeanObject,
    mut v_e_6945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6946_: u8 = 0;
    let mut v_t_boxed_6947_: u8 = 0;
    let mut v_res_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6946_ = (crate::leanh::lean_unbox(v_pu_6941_) as u8);
    v_t_boxed_6947_ = (crate::leanh::lean_unbox(v_t_6942_) as u8);
    v_res_6948_ = l_Lean_Compiler_LCNF_normExpr___redArg(
        v_pu_boxed_6946_,
        v_t_boxed_6947_,
        v_inst_6943_,
        v_inst_6944_,
        v_e_6945_,
    );
    return v_res_6948_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr(
    mut v_m_6949_: *mut crate::leanh::LeanObject,
    mut v_pu_6950_: u8,
    mut v_t_6951_: u8,
    mut v_inst_6952_: *mut crate::leanh::LeanObject,
    mut v_inst_6953_: *mut crate::leanh::LeanObject,
    mut v_e_6954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6955_ = crate::leanh::lean_ctor_get(v_inst_6953_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6955_);
    v_toBind_6956_ = crate::leanh::lean_ctor_get(v_inst_6953_, 1);
    crate::leanh::lean_inc(v_toBind_6956_);
    crate::leanh::lean_dec_ref(v_inst_6953_);
    v_toPure_6957_ = crate::leanh::lean_ctor_get(v_toApplicative_6955_, 1);
    crate::leanh::lean_inc(v_toPure_6957_);
    crate::leanh::lean_dec_ref(v_toApplicative_6955_);
    v___x_6958_ = crate::leanh::lean_box((v_pu_6950_) as usize);
    v___x_6959_ = crate::leanh::lean_box((v_t_6951_) as usize);
    v___f_6960_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6960_, 0, v___x_6958_);
    crate::leanh::lean_closure_set(v___f_6960_, 1, v___x_6959_);
    crate::leanh::lean_closure_set(v___f_6960_, 2, v_e_6954_);
    crate::leanh::lean_closure_set(v___f_6960_, 3, v_toPure_6957_);
    v___x_6961_ = crate::leanh::lean_apply_4(
        v_toBind_6956_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6952_,
        v___f_6960_,
    );
    return v___x_6961_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___boxed(
    mut v_m_6962_: *mut crate::leanh::LeanObject,
    mut v_pu_6963_: *mut crate::leanh::LeanObject,
    mut v_t_6964_: *mut crate::leanh::LeanObject,
    mut v_inst_6965_: *mut crate::leanh::LeanObject,
    mut v_inst_6966_: *mut crate::leanh::LeanObject,
    mut v_e_6967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6968_: u8 = 0;
    let mut v_t_boxed_6969_: u8 = 0;
    let mut v_res_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6968_ = (crate::leanh::lean_unbox(v_pu_6963_) as u8);
    v_t_boxed_6969_ = (crate::leanh::lean_unbox(v_t_6964_) as u8);
    v_res_6970_ = l_Lean_Compiler_LCNF_normExpr(
        v_m_6962_,
        v_pu_boxed_6968_,
        v_t_boxed_6969_,
        v_inst_6965_,
        v_inst_6966_,
        v_e_6967_,
    );
    return v_res_6970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg___lam__0(
    mut v_pu_6971_: u8,
    mut v_arg_6972_: *mut crate::leanh::LeanObject,
    mut v_t_6973_: u8,
    mut v_toPure_6974_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6976_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
        v_pu_6971_,
        v_____do__lift_6975_,
        v_arg_6972_,
        v_t_6973_,
    );
    v___x_6977_ =
        crate::leanh::lean_apply_2(v_toPure_6974_, crate::leanh::lean_box(0), v___x_6976_);
    return v___x_6977_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(
    mut v_pu_6978_: *mut crate::leanh::LeanObject,
    mut v_arg_6979_: *mut crate::leanh::LeanObject,
    mut v_t_6980_: *mut crate::leanh::LeanObject,
    mut v_toPure_6981_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6983_: u8 = 0;
    let mut v_t_boxed_6984_: u8 = 0;
    let mut v_res_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6983_ = (crate::leanh::lean_unbox(v_pu_6978_) as u8);
    v_t_boxed_6984_ = (crate::leanh::lean_unbox(v_t_6980_) as u8);
    v_res_6985_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(
        v_pu_boxed_6983_,
        v_arg_6979_,
        v_t_boxed_6984_,
        v_toPure_6981_,
        v_____do__lift_6982_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_6982_);
    return v_res_6985_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg(
    mut v_pu_6986_: u8,
    mut v_t_6987_: u8,
    mut v_inst_6988_: *mut crate::leanh::LeanObject,
    mut v_inst_6989_: *mut crate::leanh::LeanObject,
    mut v_arg_6990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6991_ = crate::leanh::lean_ctor_get(v_inst_6989_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_6991_);
    v_toBind_6992_ = crate::leanh::lean_ctor_get(v_inst_6989_, 1);
    crate::leanh::lean_inc(v_toBind_6992_);
    crate::leanh::lean_dec_ref(v_inst_6989_);
    v_toPure_6993_ = crate::leanh::lean_ctor_get(v_toApplicative_6991_, 1);
    crate::leanh::lean_inc(v_toPure_6993_);
    crate::leanh::lean_dec_ref(v_toApplicative_6991_);
    v___x_6994_ = crate::leanh::lean_box((v_pu_6986_) as usize);
    v___x_6995_ = crate::leanh::lean_box((v_t_6987_) as usize);
    v___f_6996_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6996_, 0, v___x_6994_);
    crate::leanh::lean_closure_set(v___f_6996_, 1, v_arg_6990_);
    crate::leanh::lean_closure_set(v___f_6996_, 2, v___x_6995_);
    crate::leanh::lean_closure_set(v___f_6996_, 3, v_toPure_6993_);
    v___x_6997_ = crate::leanh::lean_apply_4(
        v_toBind_6992_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6988_,
        v___f_6996_,
    );
    return v___x_6997_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg___boxed(
    mut v_pu_6998_: *mut crate::leanh::LeanObject,
    mut v_t_6999_: *mut crate::leanh::LeanObject,
    mut v_inst_7000_: *mut crate::leanh::LeanObject,
    mut v_inst_7001_: *mut crate::leanh::LeanObject,
    mut v_arg_7002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7003_: u8 = 0;
    let mut v_t_boxed_7004_: u8 = 0;
    let mut v_res_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7003_ = (crate::leanh::lean_unbox(v_pu_6998_) as u8);
    v_t_boxed_7004_ = (crate::leanh::lean_unbox(v_t_6999_) as u8);
    v_res_7005_ = l_Lean_Compiler_LCNF_normArg___redArg(
        v_pu_boxed_7003_,
        v_t_boxed_7004_,
        v_inst_7000_,
        v_inst_7001_,
        v_arg_7002_,
    );
    return v_res_7005_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg(
    mut v_m_7006_: *mut crate::leanh::LeanObject,
    mut v_pu_7007_: u8,
    mut v_t_7008_: u8,
    mut v_inst_7009_: *mut crate::leanh::LeanObject,
    mut v_inst_7010_: *mut crate::leanh::LeanObject,
    mut v_arg_7011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7012_ = crate::leanh::lean_ctor_get(v_inst_7010_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7012_);
    v_toBind_7013_ = crate::leanh::lean_ctor_get(v_inst_7010_, 1);
    crate::leanh::lean_inc(v_toBind_7013_);
    crate::leanh::lean_dec_ref(v_inst_7010_);
    v_toPure_7014_ = crate::leanh::lean_ctor_get(v_toApplicative_7012_, 1);
    crate::leanh::lean_inc(v_toPure_7014_);
    crate::leanh::lean_dec_ref(v_toApplicative_7012_);
    v___x_7015_ = crate::leanh::lean_box((v_pu_7007_) as usize);
    v___x_7016_ = crate::leanh::lean_box((v_t_7008_) as usize);
    v___f_7017_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7017_, 0, v___x_7015_);
    crate::leanh::lean_closure_set(v___f_7017_, 1, v_arg_7011_);
    crate::leanh::lean_closure_set(v___f_7017_, 2, v___x_7016_);
    crate::leanh::lean_closure_set(v___f_7017_, 3, v_toPure_7014_);
    v___x_7018_ = crate::leanh::lean_apply_4(
        v_toBind_7013_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7009_,
        v___f_7017_,
    );
    return v___x_7018_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___boxed(
    mut v_m_7019_: *mut crate::leanh::LeanObject,
    mut v_pu_7020_: *mut crate::leanh::LeanObject,
    mut v_t_7021_: *mut crate::leanh::LeanObject,
    mut v_inst_7022_: *mut crate::leanh::LeanObject,
    mut v_inst_7023_: *mut crate::leanh::LeanObject,
    mut v_arg_7024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7025_: u8 = 0;
    let mut v_t_boxed_7026_: u8 = 0;
    let mut v_res_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7025_ = (crate::leanh::lean_unbox(v_pu_7020_) as u8);
    v_t_boxed_7026_ = (crate::leanh::lean_unbox(v_t_7021_) as u8);
    v_res_7027_ = l_Lean_Compiler_LCNF_normArg(
        v_m_7019_,
        v_pu_boxed_7025_,
        v_t_boxed_7026_,
        v_inst_7022_,
        v_inst_7023_,
        v_arg_7024_,
    );
    return v_res_7027_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(
    mut v_pu_7028_: u8,
    mut v_e_7029_: *mut crate::leanh::LeanObject,
    mut v_t_7030_: u8,
    mut v_toPure_7031_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7033_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_7028_,
        v_____do__lift_7032_,
        v_e_7029_,
        v_t_7030_,
    );
    v___x_7034_ =
        crate::leanh::lean_apply_2(v_toPure_7031_, crate::leanh::lean_box(0), v___x_7033_);
    return v___x_7034_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(
    mut v_pu_7035_: *mut crate::leanh::LeanObject,
    mut v_e_7036_: *mut crate::leanh::LeanObject,
    mut v_t_7037_: *mut crate::leanh::LeanObject,
    mut v_toPure_7038_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7040_: u8 = 0;
    let mut v_t_boxed_7041_: u8 = 0;
    let mut v_res_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7040_ = (crate::leanh::lean_unbox(v_pu_7035_) as u8);
    v_t_boxed_7041_ = (crate::leanh::lean_unbox(v_t_7037_) as u8);
    v_res_7042_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(
        v_pu_boxed_7040_,
        v_e_7036_,
        v_t_boxed_7041_,
        v_toPure_7038_,
        v_____do__lift_7039_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_7039_);
    return v_res_7042_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg(
    mut v_pu_7043_: u8,
    mut v_t_7044_: u8,
    mut v_inst_7045_: *mut crate::leanh::LeanObject,
    mut v_inst_7046_: *mut crate::leanh::LeanObject,
    mut v_e_7047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7048_ = crate::leanh::lean_ctor_get(v_inst_7046_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7048_);
    v_toBind_7049_ = crate::leanh::lean_ctor_get(v_inst_7046_, 1);
    crate::leanh::lean_inc(v_toBind_7049_);
    crate::leanh::lean_dec_ref(v_inst_7046_);
    v_toPure_7050_ = crate::leanh::lean_ctor_get(v_toApplicative_7048_, 1);
    crate::leanh::lean_inc(v_toPure_7050_);
    crate::leanh::lean_dec_ref(v_toApplicative_7048_);
    v___x_7051_ = crate::leanh::lean_box((v_pu_7043_) as usize);
    v___x_7052_ = crate::leanh::lean_box((v_t_7044_) as usize);
    v___f_7053_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7053_, 0, v___x_7051_);
    crate::leanh::lean_closure_set(v___f_7053_, 1, v_e_7047_);
    crate::leanh::lean_closure_set(v___f_7053_, 2, v___x_7052_);
    crate::leanh::lean_closure_set(v___f_7053_, 3, v_toPure_7050_);
    v___x_7054_ = crate::leanh::lean_apply_4(
        v_toBind_7049_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7045_,
        v___f_7053_,
    );
    return v___x_7054_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(
    mut v_pu_7055_: *mut crate::leanh::LeanObject,
    mut v_t_7056_: *mut crate::leanh::LeanObject,
    mut v_inst_7057_: *mut crate::leanh::LeanObject,
    mut v_inst_7058_: *mut crate::leanh::LeanObject,
    mut v_e_7059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7060_: u8 = 0;
    let mut v_t_boxed_7061_: u8 = 0;
    let mut v_res_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7060_ = (crate::leanh::lean_unbox(v_pu_7055_) as u8);
    v_t_boxed_7061_ = (crate::leanh::lean_unbox(v_t_7056_) as u8);
    v_res_7062_ = l_Lean_Compiler_LCNF_normLetValue___redArg(
        v_pu_boxed_7060_,
        v_t_boxed_7061_,
        v_inst_7057_,
        v_inst_7058_,
        v_e_7059_,
    );
    return v_res_7062_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue(
    mut v_m_7063_: *mut crate::leanh::LeanObject,
    mut v_pu_7064_: u8,
    mut v_t_7065_: u8,
    mut v_inst_7066_: *mut crate::leanh::LeanObject,
    mut v_inst_7067_: *mut crate::leanh::LeanObject,
    mut v_e_7068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7069_ = crate::leanh::lean_ctor_get(v_inst_7067_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7069_);
    v_toBind_7070_ = crate::leanh::lean_ctor_get(v_inst_7067_, 1);
    crate::leanh::lean_inc(v_toBind_7070_);
    crate::leanh::lean_dec_ref(v_inst_7067_);
    v_toPure_7071_ = crate::leanh::lean_ctor_get(v_toApplicative_7069_, 1);
    crate::leanh::lean_inc(v_toPure_7071_);
    crate::leanh::lean_dec_ref(v_toApplicative_7069_);
    v___x_7072_ = crate::leanh::lean_box((v_pu_7064_) as usize);
    v___x_7073_ = crate::leanh::lean_box((v_t_7065_) as usize);
    v___f_7074_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7074_, 0, v___x_7072_);
    crate::leanh::lean_closure_set(v___f_7074_, 1, v_e_7068_);
    crate::leanh::lean_closure_set(v___f_7074_, 2, v___x_7073_);
    crate::leanh::lean_closure_set(v___f_7074_, 3, v_toPure_7071_);
    v___x_7075_ = crate::leanh::lean_apply_4(
        v_toBind_7070_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7066_,
        v___f_7074_,
    );
    return v___x_7075_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___boxed(
    mut v_m_7076_: *mut crate::leanh::LeanObject,
    mut v_pu_7077_: *mut crate::leanh::LeanObject,
    mut v_t_7078_: *mut crate::leanh::LeanObject,
    mut v_inst_7079_: *mut crate::leanh::LeanObject,
    mut v_inst_7080_: *mut crate::leanh::LeanObject,
    mut v_e_7081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7082_: u8 = 0;
    let mut v_t_boxed_7083_: u8 = 0;
    let mut v_res_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7082_ = (crate::leanh::lean_unbox(v_pu_7077_) as u8);
    v_t_boxed_7083_ = (crate::leanh::lean_unbox(v_t_7078_) as u8);
    v_res_7084_ = l_Lean_Compiler_LCNF_normLetValue(
        v_m_7076_,
        v_pu_boxed_7082_,
        v_t_boxed_7083_,
        v_inst_7079_,
        v_inst_7080_,
        v_e_7081_,
    );
    return v_res_7084_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExprCore(
    mut v_pu_7085_: u8,
    mut v_s_7086_: *mut crate::leanh::LeanObject,
    mut v_e_7087_: *mut crate::leanh::LeanObject,
    mut v_translator_7088_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7089_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_7085_,
        v_s_7086_,
        v_translator_7088_,
        v_e_7087_,
    );
    return v___x_7089_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExprCore___boxed(
    mut v_pu_7090_: *mut crate::leanh::LeanObject,
    mut v_s_7091_: *mut crate::leanh::LeanObject,
    mut v_e_7092_: *mut crate::leanh::LeanObject,
    mut v_translator_7093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7094_: u8 = 0;
    let mut v_translator_boxed_7095_: u8 = 0;
    let mut v_res_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7094_ = (crate::leanh::lean_unbox(v_pu_7090_) as u8);
    v_translator_boxed_7095_ = (crate::leanh::lean_unbox(v_translator_7093_) as u8);
    v_res_7096_ = l_Lean_Compiler_LCNF_normExprCore(
        v_pu_boxed_7094_,
        v_s_7091_,
        v_e_7092_,
        v_translator_boxed_7095_,
    );
    crate::leanh::lean_dec_ref(v_s_7091_);
    return v_res_7096_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(
    mut v_pu_7097_: u8,
    mut v_args_7098_: *mut crate::leanh::LeanObject,
    mut v_t_7099_: u8,
    mut v_toPure_7100_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_7097_,
        v_____do__lift_7101_,
        v_args_7098_,
        v_t_7099_,
    );
    v___x_7103_ =
        crate::leanh::lean_apply_2(v_toPure_7100_, crate::leanh::lean_box(0), v___x_7102_);
    return v___x_7103_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(
    mut v_pu_7104_: *mut crate::leanh::LeanObject,
    mut v_args_7105_: *mut crate::leanh::LeanObject,
    mut v_t_7106_: *mut crate::leanh::LeanObject,
    mut v_toPure_7107_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7109_: u8 = 0;
    let mut v_t_boxed_7110_: u8 = 0;
    let mut v_res_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7109_ = (crate::leanh::lean_unbox(v_pu_7104_) as u8);
    v_t_boxed_7110_ = (crate::leanh::lean_unbox(v_t_7106_) as u8);
    v_res_7111_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(
        v_pu_boxed_7109_,
        v_args_7105_,
        v_t_boxed_7110_,
        v_toPure_7107_,
        v_____do__lift_7108_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_7108_);
    return v_res_7111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg(
    mut v_pu_7112_: u8,
    mut v_t_7113_: u8,
    mut v_inst_7114_: *mut crate::leanh::LeanObject,
    mut v_inst_7115_: *mut crate::leanh::LeanObject,
    mut v_args_7116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7117_ = crate::leanh::lean_ctor_get(v_inst_7115_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7117_);
    v_toBind_7118_ = crate::leanh::lean_ctor_get(v_inst_7115_, 1);
    crate::leanh::lean_inc(v_toBind_7118_);
    crate::leanh::lean_dec_ref(v_inst_7115_);
    v_toPure_7119_ = crate::leanh::lean_ctor_get(v_toApplicative_7117_, 1);
    crate::leanh::lean_inc(v_toPure_7119_);
    crate::leanh::lean_dec_ref(v_toApplicative_7117_);
    v___x_7120_ = crate::leanh::lean_box((v_pu_7112_) as usize);
    v___x_7121_ = crate::leanh::lean_box((v_t_7113_) as usize);
    v___f_7122_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7122_, 0, v___x_7120_);
    crate::leanh::lean_closure_set(v___f_7122_, 1, v_args_7116_);
    crate::leanh::lean_closure_set(v___f_7122_, 2, v___x_7121_);
    crate::leanh::lean_closure_set(v___f_7122_, 3, v_toPure_7119_);
    v___x_7123_ = crate::leanh::lean_apply_4(
        v_toBind_7118_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7114_,
        v___f_7122_,
    );
    return v___x_7123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___boxed(
    mut v_pu_7124_: *mut crate::leanh::LeanObject,
    mut v_t_7125_: *mut crate::leanh::LeanObject,
    mut v_inst_7126_: *mut crate::leanh::LeanObject,
    mut v_inst_7127_: *mut crate::leanh::LeanObject,
    mut v_args_7128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7129_: u8 = 0;
    let mut v_t_boxed_7130_: u8 = 0;
    let mut v_res_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7129_ = (crate::leanh::lean_unbox(v_pu_7124_) as u8);
    v_t_boxed_7130_ = (crate::leanh::lean_unbox(v_t_7125_) as u8);
    v_res_7131_ = l_Lean_Compiler_LCNF_normArgs___redArg(
        v_pu_boxed_7129_,
        v_t_boxed_7130_,
        v_inst_7126_,
        v_inst_7127_,
        v_args_7128_,
    );
    return v_res_7131_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs(
    mut v_m_7132_: *mut crate::leanh::LeanObject,
    mut v_pu_7133_: u8,
    mut v_t_7134_: u8,
    mut v_inst_7135_: *mut crate::leanh::LeanObject,
    mut v_inst_7136_: *mut crate::leanh::LeanObject,
    mut v_args_7137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7138_ = l_Lean_Compiler_LCNF_normArgs___redArg(
        v_pu_7133_,
        v_t_7134_,
        v_inst_7135_,
        v_inst_7136_,
        v_args_7137_,
    );
    return v___x_7138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___boxed(
    mut v_m_7139_: *mut crate::leanh::LeanObject,
    mut v_pu_7140_: *mut crate::leanh::LeanObject,
    mut v_t_7141_: *mut crate::leanh::LeanObject,
    mut v_inst_7142_: *mut crate::leanh::LeanObject,
    mut v_inst_7143_: *mut crate::leanh::LeanObject,
    mut v_args_7144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7145_: u8 = 0;
    let mut v_t_boxed_7146_: u8 = 0;
    let mut v_res_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7145_ = (crate::leanh::lean_unbox(v_pu_7140_) as u8);
    v_t_boxed_7146_ = (crate::leanh::lean_unbox(v_t_7141_) as u8);
    v_res_7147_ = l_Lean_Compiler_LCNF_normArgs(
        v_m_7139_,
        v_pu_boxed_7145_,
        v_t_boxed_7146_,
        v_inst_7142_,
        v_inst_7143_,
        v_args_7144_,
    );
    return v_res_7147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(
    mut v_binderName_7148_: *mut crate::leanh::LeanObject,
    mut v_a_7149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7157_: u8 = 0;
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7151_ = lean_st_ref_get(v_a_7149_);
                v___x_7152_ = lean_st_ref_take(v_a_7149_);
                v_lctx_7153_ = crate::leanh::lean_ctor_get(v___x_7152_, 0);
                v_nextIdx_7154_ = crate::leanh::lean_ctor_get(v___x_7152_, 1);
                v_isSharedCheck_7167_ = (!crate::leanh::lean_is_exclusive(v___x_7152_)) as u8;
                if v_isSharedCheck_7167_ == 0 {
                    v___x_7156_ = v___x_7152_;
                    v_isShared_7157_ = v_isSharedCheck_7167_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7154_);
                    crate::leanh::lean_inc(v_lctx_7153_);
                    crate::leanh::lean_dec(v___x_7152_);
                    v___x_7156_ = crate::leanh::lean_box(0);
                    v_isShared_7157_ = v_isSharedCheck_7167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7158_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7159_ = lean_nat_add(v_nextIdx_7154_, v___x_7158_);
                crate::leanh::lean_dec(v_nextIdx_7154_);
                if v_isShared_7157_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7156_, 1, v___x_7159_);
                    v___x_7161_ = v___x_7156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7166_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 0, v_lctx_7153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 1, v___x_7159_);
                    v___x_7161_ = v_reuseFailAlloc_7166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7162_ = lean_st_ref_set(v_a_7149_, v___x_7161_);
                v_nextIdx_7163_ = crate::leanh::lean_ctor_get(v___x_7151_, 1);
                crate::leanh::lean_inc(v_nextIdx_7163_);
                crate::leanh::lean_dec(v___x_7151_);
                v___x_7164_ = l_Lean_Name_num___override(v_binderName_7148_, v_nextIdx_7163_);
                v___x_7165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7165_, 0, v___x_7164_);
                return v___x_7165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(
    mut v_binderName_7168_: *mut crate::leanh::LeanObject,
    mut v_a_7169_: *mut crate::leanh::LeanObject,
    mut v_a_7170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7171_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_7168_, v_a_7169_);
    crate::leanh::lean_dec(v_a_7169_);
    return v_res_7171_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName(
    mut v_binderName_7172_: *mut crate::leanh::LeanObject,
    mut v_a_7173_: *mut crate::leanh::LeanObject,
    mut v_a_7174_: *mut crate::leanh::LeanObject,
    mut v_a_7175_: *mut crate::leanh::LeanObject,
    mut v_a_7176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7178_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_7172_, v_a_7174_);
    return v___x_7178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(
    mut v_binderName_7179_: *mut crate::leanh::LeanObject,
    mut v_a_7180_: *mut crate::leanh::LeanObject,
    mut v_a_7181_: *mut crate::leanh::LeanObject,
    mut v_a_7182_: *mut crate::leanh::LeanObject,
    mut v_a_7183_: *mut crate::leanh::LeanObject,
    mut v_a_7184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7185_ = l_Lean_Compiler_LCNF_mkFreshBinderName(
        v_binderName_7179_,
        v_a_7180_,
        v_a_7181_,
        v_a_7182_,
        v_a_7183_,
    );
    crate::leanh::lean_dec(v_a_7183_);
    crate::leanh::lean_dec_ref(v_a_7182_);
    crate::leanh::lean_dec(v_a_7181_);
    crate::leanh::lean_dec_ref(v_a_7180_);
    return v_res_7185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
    mut v_binderName_7186_: *mut crate::leanh::LeanObject,
    mut v_baseName_7187_: *mut crate::leanh::LeanObject,
    mut v_a_7188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7190_: u8 = 0;
    v___x_7190_ = l_Lean_Name_isAnonymous(v_binderName_7186_);
    if v___x_7190_ == 0 {
        let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_baseName_7187_);
        v___x_7191_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7191_, 0, v_binderName_7186_);
        return v___x_7191_;
    } else {
        let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_binderName_7186_);
        v___x_7192_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_7187_, v_a_7188_);
        return v___x_7192_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(
    mut v_binderName_7193_: *mut crate::leanh::LeanObject,
    mut v_baseName_7194_: *mut crate::leanh::LeanObject,
    mut v_a_7195_: *mut crate::leanh::LeanObject,
    mut v_a_7196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7197_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
        v_binderName_7193_,
        v_baseName_7194_,
        v_a_7195_,
    );
    crate::leanh::lean_dec(v_a_7195_);
    return v_res_7197_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous(
    mut v_binderName_7198_: *mut crate::leanh::LeanObject,
    mut v_baseName_7199_: *mut crate::leanh::LeanObject,
    mut v_a_7200_: *mut crate::leanh::LeanObject,
    mut v_a_7201_: *mut crate::leanh::LeanObject,
    mut v_a_7202_: *mut crate::leanh::LeanObject,
    mut v_a_7203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7205_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
        v_binderName_7198_,
        v_baseName_7199_,
        v_a_7201_,
    );
    return v___x_7205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(
    mut v_binderName_7206_: *mut crate::leanh::LeanObject,
    mut v_baseName_7207_: *mut crate::leanh::LeanObject,
    mut v_a_7208_: *mut crate::leanh::LeanObject,
    mut v_a_7209_: *mut crate::leanh::LeanObject,
    mut v_a_7210_: *mut crate::leanh::LeanObject,
    mut v_a_7211_: *mut crate::leanh::LeanObject,
    mut v_a_7212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7213_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(
        v_binderName_7206_,
        v_baseName_7207_,
        v_a_7208_,
        v_a_7209_,
        v_a_7210_,
        v_a_7211_,
    );
    crate::leanh::lean_dec(v_a_7211_);
    crate::leanh::lean_dec_ref(v_a_7210_);
    crate::leanh::lean_dec(v_a_7209_);
    crate::leanh::lean_dec_ref(v_a_7208_);
    return v_res_7213_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(
    mut v___y_7214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7234_: u8 = 0;
    let mut v_r_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7246_: u8 = 0;
    let mut v_unused_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7216_ = lean_st_ref_get(v___y_7214_);
                v_ngen_7217_ = crate::leanh::lean_ctor_get(v___x_7216_, 2);
                crate::leanh::lean_inc_ref(v_ngen_7217_);
                crate::leanh::lean_dec(v___x_7216_);
                v_namePrefix_7218_ = crate::leanh::lean_ctor_get(v_ngen_7217_, 0);
                v_idx_7219_ = crate::leanh::lean_ctor_get(v_ngen_7217_, 1);
                v_isSharedCheck_7248_ = (!crate::leanh::lean_is_exclusive(v_ngen_7217_)) as u8;
                if v_isSharedCheck_7248_ == 0 {
                    v___x_7221_ = v_ngen_7217_;
                    v_isShared_7222_ = v_isSharedCheck_7248_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_7219_);
                    crate::leanh::lean_inc(v_namePrefix_7218_);
                    crate::leanh::lean_dec(v_ngen_7217_);
                    v___x_7221_ = crate::leanh::lean_box(0);
                    v_isShared_7222_ = v_isSharedCheck_7248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7223_ = lean_st_ref_take(v___y_7214_);
                v_env_7224_ = crate::leanh::lean_ctor_get(v___x_7223_, 0);
                v_nextMacroScope_7225_ = crate::leanh::lean_ctor_get(v___x_7223_, 1);
                v_auxDeclNGen_7226_ = crate::leanh::lean_ctor_get(v___x_7223_, 3);
                v_traceState_7227_ = crate::leanh::lean_ctor_get(v___x_7223_, 4);
                v_cache_7228_ = crate::leanh::lean_ctor_get(v___x_7223_, 5);
                v_messages_7229_ = crate::leanh::lean_ctor_get(v___x_7223_, 6);
                v_infoState_7230_ = crate::leanh::lean_ctor_get(v___x_7223_, 7);
                v_snapshotTasks_7231_ = crate::leanh::lean_ctor_get(v___x_7223_, 8);
                v_isSharedCheck_7246_ = (!crate::leanh::lean_is_exclusive(v___x_7223_)) as u8;
                if v_isSharedCheck_7246_ == 0 {
                    v_unused_7247_ = crate::leanh::lean_ctor_get(v___x_7223_, 2);
                    crate::leanh::lean_dec(v_unused_7247_);
                    v___x_7233_ = v___x_7223_;
                    v_isShared_7234_ = v_isSharedCheck_7246_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7231_);
                    crate::leanh::lean_inc(v_infoState_7230_);
                    crate::leanh::lean_inc(v_messages_7229_);
                    crate::leanh::lean_inc(v_cache_7228_);
                    crate::leanh::lean_inc(v_traceState_7227_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7226_);
                    crate::leanh::lean_inc(v_nextMacroScope_7225_);
                    crate::leanh::lean_inc(v_env_7224_);
                    crate::leanh::lean_dec(v___x_7223_);
                    v___x_7233_ = crate::leanh::lean_box(0);
                    v_isShared_7234_ = v_isSharedCheck_7246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_7219_);
                crate::leanh::lean_inc(v_namePrefix_7218_);
                v_r_7235_ = l_Lean_Name_num___override(v_namePrefix_7218_, v_idx_7219_);
                v___x_7236_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7237_ = lean_nat_add(v_idx_7219_, v___x_7236_);
                crate::leanh::lean_dec(v_idx_7219_);
                if v_isShared_7222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7221_, 1, v___x_7237_);
                    v___x_7239_ = v___x_7221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7245_, 0, v_namePrefix_7218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7245_, 1, v___x_7237_);
                    v___x_7239_ = v_reuseFailAlloc_7245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7233_, 2, v___x_7239_);
                    v___x_7241_ = v___x_7233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7244_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 0, v_env_7224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 1, v_nextMacroScope_7225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 2, v___x_7239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 3, v_auxDeclNGen_7226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 4, v_traceState_7227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 5, v_cache_7228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 6, v_messages_7229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 7, v_infoState_7230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7244_, 8, v_snapshotTasks_7231_);
                    v___x_7241_ = v_reuseFailAlloc_7244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7242_ = lean_st_ref_set(v___y_7214_, v___x_7241_);
                v___x_7243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7243_, 0, v_r_7235_);
                return v___x_7243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7251_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7249_);
    crate::leanh::lean_dec(v___y_7249_);
    return v_res_7251_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
    mut v___y_7252_: *mut crate::leanh::LeanObject,
    mut v___y_7253_: *mut crate::leanh::LeanObject,
    mut v___y_7254_: *mut crate::leanh::LeanObject,
    mut v___y_7255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7261_: u8 = 0;
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7257_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7255_);
                v_a_7258_ = crate::leanh::lean_ctor_get(v___x_7257_, 0);
                v_isSharedCheck_7265_ = (!crate::leanh::lean_is_exclusive(v___x_7257_)) as u8;
                if v_isSharedCheck_7265_ == 0 {
                    v___x_7260_ = v___x_7257_;
                    v_isShared_7261_ = v_isSharedCheck_7265_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7258_);
                    crate::leanh::lean_dec(v___x_7257_);
                    v___x_7260_ = crate::leanh::lean_box(0);
                    v_isShared_7261_ = v_isSharedCheck_7265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7261_ == 0 {
                    v___x_7263_ = v___x_7260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7264_, 0, v_a_7258_);
                    v___x_7263_ = v_reuseFailAlloc_7264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0___boxed(
    mut v___y_7266_: *mut crate::leanh::LeanObject,
    mut v___y_7267_: *mut crate::leanh::LeanObject,
    mut v___y_7268_: *mut crate::leanh::LeanObject,
    mut v___y_7269_: *mut crate::leanh::LeanObject,
    mut v___y_7270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7271_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
        v___y_7266_,
        v___y_7267_,
        v___y_7268_,
        v___y_7269_,
    );
    crate::leanh::lean_dec(v___y_7269_);
    crate::leanh::lean_dec_ref(v___y_7268_);
    crate::leanh::lean_dec(v___y_7267_);
    crate::leanh::lean_dec_ref(v___y_7266_);
    return v_res_7271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkParam(
    mut v_pu_7275_: u8,
    mut v_binderName_7276_: *mut crate::leanh::LeanObject,
    mut v_type_7277_: *mut crate::leanh::LeanObject,
    mut v_borrow_7278_: u8,
    mut v_a_7279_: *mut crate::leanh::LeanObject,
    mut v_a_7280_: *mut crate::leanh::LeanObject,
    mut v_a_7281_: *mut crate::leanh::LeanObject,
    mut v_a_7282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7291_: u8 = 0;
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7297_: u8 = 0;
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7307_: u8 = 0;
    let mut v_isSharedCheck_7308_: u8 = 0;
    let mut v_a_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7312_: u8 = 0;
    let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7284_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7279_, v_a_7280_, v_a_7281_, v_a_7282_,
                );
                if crate::leanh::lean_obj_tag(v___x_7284_) == 0 {
                    v_a_7285_ = crate::leanh::lean_ctor_get(v___x_7284_, 0);
                    crate::leanh::lean_inc(v_a_7285_);
                    crate::leanh::lean_dec_ref_known(v___x_7284_, 1);
                    v___x_7286_ = l_Lean_Compiler_LCNF_mkParam___closed__1;
                    v___x_7287_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7276_,
                        v___x_7286_,
                        v_a_7280_,
                    );
                    v_a_7288_ = crate::leanh::lean_ctor_get(v___x_7287_, 0);
                    v_isSharedCheck_7308_ = (!crate::leanh::lean_is_exclusive(v___x_7287_)) as u8;
                    if v_isSharedCheck_7308_ == 0 {
                        v___x_7290_ = v___x_7287_;
                        v_isShared_7291_ = v_isSharedCheck_7308_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7288_);
                        crate::leanh::lean_dec(v___x_7287_);
                        v___x_7290_ = crate::leanh::lean_box(0);
                        v_isShared_7291_ = v_isSharedCheck_7308_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_7277_);
                    crate::leanh::lean_dec(v_binderName_7276_);
                    v_a_7309_ = crate::leanh::lean_ctor_get(v___x_7284_, 0);
                    v_isSharedCheck_7316_ = (!crate::leanh::lean_is_exclusive(v___x_7284_)) as u8;
                    if v_isSharedCheck_7316_ == 0 {
                        v___x_7311_ = v___x_7284_;
                        v_isShared_7312_ = v_isSharedCheck_7316_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7309_);
                        crate::leanh::lean_dec(v___x_7284_);
                        v___x_7311_ = crate::leanh::lean_box(0);
                        v_isShared_7312_ = v_isSharedCheck_7316_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7292_ = lean_st_ref_take(v_a_7280_);
                v_lctx_7293_ = crate::leanh::lean_ctor_get(v___x_7292_, 0);
                v_nextIdx_7294_ = crate::leanh::lean_ctor_get(v___x_7292_, 1);
                v_isSharedCheck_7307_ = (!crate::leanh::lean_is_exclusive(v___x_7292_)) as u8;
                if v_isSharedCheck_7307_ == 0 {
                    v___x_7296_ = v___x_7292_;
                    v_isShared_7297_ = v_isSharedCheck_7307_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7294_);
                    crate::leanh::lean_inc(v_lctx_7293_);
                    crate::leanh::lean_dec(v___x_7292_);
                    v___x_7296_ = crate::leanh::lean_box(0);
                    v_isShared_7297_ = v_isSharedCheck_7307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7298_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_7298_, 0, v_a_7285_);
                crate::leanh::lean_ctor_set(v___x_7298_, 1, v_a_7288_);
                crate::leanh::lean_ctor_set(v___x_7298_, 2, v_type_7277_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7298_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_borrow_7278_,
                );
                crate::leanh::lean_inc_ref(v___x_7298_);
                v___x_7299_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7275_, v_lctx_7293_, v___x_7298_);
                if v_isShared_7297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7296_, 0, v___x_7299_);
                    v___x_7301_ = v___x_7296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7306_, 0, v___x_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7306_, 1, v_nextIdx_7294_);
                    v___x_7301_ = v_reuseFailAlloc_7306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7302_ = lean_st_ref_set(v_a_7280_, v___x_7301_);
                if v_isShared_7291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7290_, 0, v___x_7298_);
                    v___x_7304_ = v___x_7290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7305_, 0, v___x_7298_);
                    v___x_7304_ = v_reuseFailAlloc_7305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7304_;
            }
            5 => {
                if v_isShared_7312_ == 0 {
                    v___x_7314_ = v___x_7311_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7315_, 0, v_a_7309_);
                    v___x_7314_ = v_reuseFailAlloc_7315_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkParam___boxed(
    mut v_pu_7317_: *mut crate::leanh::LeanObject,
    mut v_binderName_7318_: *mut crate::leanh::LeanObject,
    mut v_type_7319_: *mut crate::leanh::LeanObject,
    mut v_borrow_7320_: *mut crate::leanh::LeanObject,
    mut v_a_7321_: *mut crate::leanh::LeanObject,
    mut v_a_7322_: *mut crate::leanh::LeanObject,
    mut v_a_7323_: *mut crate::leanh::LeanObject,
    mut v_a_7324_: *mut crate::leanh::LeanObject,
    mut v_a_7325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7326_: u8 = 0;
    let mut v_borrow_boxed_7327_: u8 = 0;
    let mut v_res_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7326_ = (crate::leanh::lean_unbox(v_pu_7317_) as u8);
    v_borrow_boxed_7327_ = (crate::leanh::lean_unbox(v_borrow_7320_) as u8);
    v_res_7328_ = l_Lean_Compiler_LCNF_mkParam(
        v_pu_boxed_7326_,
        v_binderName_7318_,
        v_type_7319_,
        v_borrow_boxed_7327_,
        v_a_7321_,
        v_a_7322_,
        v_a_7323_,
        v_a_7324_,
    );
    crate::leanh::lean_dec(v_a_7324_);
    crate::leanh::lean_dec_ref(v_a_7323_);
    crate::leanh::lean_dec(v_a_7322_);
    crate::leanh::lean_dec_ref(v_a_7321_);
    return v_res_7328_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(
    mut v___y_7329_: *mut crate::leanh::LeanObject,
    mut v___y_7330_: *mut crate::leanh::LeanObject,
    mut v___y_7331_: *mut crate::leanh::LeanObject,
    mut v___y_7332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7334_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7332_);
    return v___x_7334_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(
    mut v___y_7335_: *mut crate::leanh::LeanObject,
    mut v___y_7336_: *mut crate::leanh::LeanObject,
    mut v___y_7337_: *mut crate::leanh::LeanObject,
    mut v___y_7338_: *mut crate::leanh::LeanObject,
    mut v___y_7339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7340_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_7335_, v___y_7336_, v___y_7337_, v___y_7338_);
    crate::leanh::lean_dec(v___y_7338_);
    crate::leanh::lean_dec_ref(v___y_7337_);
    crate::leanh::lean_dec(v___y_7336_);
    crate::leanh::lean_dec_ref(v___y_7335_);
    return v_res_7340_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDecl(
    mut v_pu_7344_: u8,
    mut v_binderName_7345_: *mut crate::leanh::LeanObject,
    mut v_type_7346_: *mut crate::leanh::LeanObject,
    mut v_value_7347_: *mut crate::leanh::LeanObject,
    mut v_a_7348_: *mut crate::leanh::LeanObject,
    mut v_a_7349_: *mut crate::leanh::LeanObject,
    mut v_a_7350_: *mut crate::leanh::LeanObject,
    mut v_a_7351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7360_: u8 = 0;
    let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7366_: u8 = 0;
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7376_: u8 = 0;
    let mut v_isSharedCheck_7377_: u8 = 0;
    let mut v_a_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7381_: u8 = 0;
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7353_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7348_, v_a_7349_, v_a_7350_, v_a_7351_,
                );
                if crate::leanh::lean_obj_tag(v___x_7353_) == 0 {
                    v_a_7354_ = crate::leanh::lean_ctor_get(v___x_7353_, 0);
                    crate::leanh::lean_inc(v_a_7354_);
                    crate::leanh::lean_dec_ref_known(v___x_7353_, 1);
                    v___x_7355_ = l_Lean_Compiler_LCNF_mkLetDecl___closed__1;
                    v___x_7356_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7345_,
                        v___x_7355_,
                        v_a_7349_,
                    );
                    v_a_7357_ = crate::leanh::lean_ctor_get(v___x_7356_, 0);
                    v_isSharedCheck_7377_ = (!crate::leanh::lean_is_exclusive(v___x_7356_)) as u8;
                    if v_isSharedCheck_7377_ == 0 {
                        v___x_7359_ = v___x_7356_;
                        v_isShared_7360_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7357_);
                        crate::leanh::lean_dec(v___x_7356_);
                        v___x_7359_ = crate::leanh::lean_box(0);
                        v_isShared_7360_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_7347_);
                    crate::leanh::lean_dec_ref(v_type_7346_);
                    crate::leanh::lean_dec(v_binderName_7345_);
                    v_a_7378_ = crate::leanh::lean_ctor_get(v___x_7353_, 0);
                    v_isSharedCheck_7385_ = (!crate::leanh::lean_is_exclusive(v___x_7353_)) as u8;
                    if v_isSharedCheck_7385_ == 0 {
                        v___x_7380_ = v___x_7353_;
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7378_);
                        crate::leanh::lean_dec(v___x_7353_);
                        v___x_7380_ = crate::leanh::lean_box(0);
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7361_ = lean_st_ref_take(v_a_7349_);
                v_lctx_7362_ = crate::leanh::lean_ctor_get(v___x_7361_, 0);
                v_nextIdx_7363_ = crate::leanh::lean_ctor_get(v___x_7361_, 1);
                v_isSharedCheck_7376_ = (!crate::leanh::lean_is_exclusive(v___x_7361_)) as u8;
                if v_isSharedCheck_7376_ == 0 {
                    v___x_7365_ = v___x_7361_;
                    v_isShared_7366_ = v_isSharedCheck_7376_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7363_);
                    crate::leanh::lean_inc(v_lctx_7362_);
                    crate::leanh::lean_dec(v___x_7361_);
                    v___x_7365_ = crate::leanh::lean_box(0);
                    v_isShared_7366_ = v_isSharedCheck_7376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7367_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7367_, 0, v_a_7354_);
                crate::leanh::lean_ctor_set(v___x_7367_, 1, v_a_7357_);
                crate::leanh::lean_ctor_set(v___x_7367_, 2, v_type_7346_);
                crate::leanh::lean_ctor_set(v___x_7367_, 3, v_value_7347_);
                crate::leanh::lean_inc_ref(v___x_7367_);
                v___x_7368_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_7344_, v_lctx_7362_, v___x_7367_);
                if v_isShared_7366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7365_, 0, v___x_7368_);
                    v___x_7370_ = v___x_7365_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7375_, 0, v___x_7368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7375_, 1, v_nextIdx_7363_);
                    v___x_7370_ = v_reuseFailAlloc_7375_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7371_ = lean_st_ref_set(v_a_7349_, v___x_7370_);
                if v_isShared_7360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7359_, 0, v___x_7367_);
                    v___x_7373_ = v___x_7359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7374_, 0, v___x_7367_);
                    v___x_7373_ = v_reuseFailAlloc_7374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7373_;
            }
            5 => {
                if v_isShared_7381_ == 0 {
                    v___x_7383_ = v___x_7380_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7384_, 0, v_a_7378_);
                    v___x_7383_ = v_reuseFailAlloc_7384_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDecl___boxed(
    mut v_pu_7386_: *mut crate::leanh::LeanObject,
    mut v_binderName_7387_: *mut crate::leanh::LeanObject,
    mut v_type_7388_: *mut crate::leanh::LeanObject,
    mut v_value_7389_: *mut crate::leanh::LeanObject,
    mut v_a_7390_: *mut crate::leanh::LeanObject,
    mut v_a_7391_: *mut crate::leanh::LeanObject,
    mut v_a_7392_: *mut crate::leanh::LeanObject,
    mut v_a_7393_: *mut crate::leanh::LeanObject,
    mut v_a_7394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7395_: u8 = 0;
    let mut v_res_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7395_ = (crate::leanh::lean_unbox(v_pu_7386_) as u8);
    v_res_7396_ = l_Lean_Compiler_LCNF_mkLetDecl(
        v_pu_boxed_7395_,
        v_binderName_7387_,
        v_type_7388_,
        v_value_7389_,
        v_a_7390_,
        v_a_7391_,
        v_a_7392_,
        v_a_7393_,
    );
    crate::leanh::lean_dec(v_a_7393_);
    crate::leanh::lean_dec_ref(v_a_7392_);
    crate::leanh::lean_dec(v_a_7391_);
    crate::leanh::lean_dec_ref(v_a_7390_);
    return v_res_7396_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFunDecl(
    mut v_pu_7400_: u8,
    mut v_binderName_7401_: *mut crate::leanh::LeanObject,
    mut v_type_7402_: *mut crate::leanh::LeanObject,
    mut v_params_7403_: *mut crate::leanh::LeanObject,
    mut v_value_7404_: *mut crate::leanh::LeanObject,
    mut v_a_7405_: *mut crate::leanh::LeanObject,
    mut v_a_7406_: *mut crate::leanh::LeanObject,
    mut v_a_7407_: *mut crate::leanh::LeanObject,
    mut v_a_7408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7417_: u8 = 0;
    let mut v___x_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7423_: u8 = 0;
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7433_: u8 = 0;
    let mut v_isSharedCheck_7434_: u8 = 0;
    let mut v_a_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v___x_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7410_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7405_, v_a_7406_, v_a_7407_, v_a_7408_,
                );
                if crate::leanh::lean_obj_tag(v___x_7410_) == 0 {
                    v_a_7411_ = crate::leanh::lean_ctor_get(v___x_7410_, 0);
                    crate::leanh::lean_inc(v_a_7411_);
                    crate::leanh::lean_dec_ref_known(v___x_7410_, 1);
                    v___x_7412_ = l_Lean_Compiler_LCNF_mkFunDecl___closed__1;
                    v___x_7413_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7401_,
                        v___x_7412_,
                        v_a_7406_,
                    );
                    v_a_7414_ = crate::leanh::lean_ctor_get(v___x_7413_, 0);
                    v_isSharedCheck_7434_ = (!crate::leanh::lean_is_exclusive(v___x_7413_)) as u8;
                    if v_isSharedCheck_7434_ == 0 {
                        v___x_7416_ = v___x_7413_;
                        v_isShared_7417_ = v_isSharedCheck_7434_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7414_);
                        crate::leanh::lean_dec(v___x_7413_);
                        v___x_7416_ = crate::leanh::lean_box(0);
                        v_isShared_7417_ = v_isSharedCheck_7434_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_7404_);
                    crate::leanh::lean_dec_ref(v_params_7403_);
                    crate::leanh::lean_dec_ref(v_type_7402_);
                    crate::leanh::lean_dec(v_binderName_7401_);
                    v_a_7435_ = crate::leanh::lean_ctor_get(v___x_7410_, 0);
                    v_isSharedCheck_7442_ = (!crate::leanh::lean_is_exclusive(v___x_7410_)) as u8;
                    if v_isSharedCheck_7442_ == 0 {
                        v___x_7437_ = v___x_7410_;
                        v_isShared_7438_ = v_isSharedCheck_7442_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7435_);
                        crate::leanh::lean_dec(v___x_7410_);
                        v___x_7437_ = crate::leanh::lean_box(0);
                        v_isShared_7438_ = v_isSharedCheck_7442_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7418_ = lean_st_ref_take(v_a_7406_);
                v_lctx_7419_ = crate::leanh::lean_ctor_get(v___x_7418_, 0);
                v_nextIdx_7420_ = crate::leanh::lean_ctor_get(v___x_7418_, 1);
                v_isSharedCheck_7433_ = (!crate::leanh::lean_is_exclusive(v___x_7418_)) as u8;
                if v_isSharedCheck_7433_ == 0 {
                    v___x_7422_ = v___x_7418_;
                    v_isShared_7423_ = v_isSharedCheck_7433_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7420_);
                    crate::leanh::lean_inc(v_lctx_7419_);
                    crate::leanh::lean_dec(v___x_7418_);
                    v___x_7422_ = crate::leanh::lean_box(0);
                    v_isShared_7423_ = v_isSharedCheck_7433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7424_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7424_, 0, v_a_7411_);
                crate::leanh::lean_ctor_set(v___x_7424_, 1, v_a_7414_);
                crate::leanh::lean_ctor_set(v___x_7424_, 2, v_params_7403_);
                crate::leanh::lean_ctor_set(v___x_7424_, 3, v_type_7402_);
                crate::leanh::lean_ctor_set(v___x_7424_, 4, v_value_7404_);
                crate::leanh::lean_inc_ref(v___x_7424_);
                v___x_7425_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_7400_, v_lctx_7419_, v___x_7424_);
                if v_isShared_7423_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7422_, 0, v___x_7425_);
                    v___x_7427_ = v___x_7422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7432_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7432_, 0, v___x_7425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7432_, 1, v_nextIdx_7420_);
                    v___x_7427_ = v_reuseFailAlloc_7432_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7428_ = lean_st_ref_set(v_a_7406_, v___x_7427_);
                if v_isShared_7417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7416_, 0, v___x_7424_);
                    v___x_7430_ = v___x_7416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7431_, 0, v___x_7424_);
                    v___x_7430_ = v_reuseFailAlloc_7431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7430_;
            }
            5 => {
                if v_isShared_7438_ == 0 {
                    v___x_7440_ = v___x_7437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7441_, 0, v_a_7435_);
                    v___x_7440_ = v_reuseFailAlloc_7441_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFunDecl___boxed(
    mut v_pu_7443_: *mut crate::leanh::LeanObject,
    mut v_binderName_7444_: *mut crate::leanh::LeanObject,
    mut v_type_7445_: *mut crate::leanh::LeanObject,
    mut v_params_7446_: *mut crate::leanh::LeanObject,
    mut v_value_7447_: *mut crate::leanh::LeanObject,
    mut v_a_7448_: *mut crate::leanh::LeanObject,
    mut v_a_7449_: *mut crate::leanh::LeanObject,
    mut v_a_7450_: *mut crate::leanh::LeanObject,
    mut v_a_7451_: *mut crate::leanh::LeanObject,
    mut v_a_7452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7453_ = (crate::leanh::lean_unbox(v_pu_7443_) as u8);
    v_res_7454_ = l_Lean_Compiler_LCNF_mkFunDecl(
        v_pu_boxed_7453_,
        v_binderName_7444_,
        v_type_7445_,
        v_params_7446_,
        v_value_7447_,
        v_a_7448_,
        v_a_7449_,
        v_a_7450_,
        v_a_7451_,
    );
    crate::leanh::lean_dec(v_a_7451_);
    crate::leanh::lean_dec_ref(v_a_7450_);
    crate::leanh::lean_dec(v_a_7449_);
    crate::leanh::lean_dec_ref(v_a_7448_);
    return v_res_7454_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDeclErased(
    mut v_pu_7455_: u8,
    mut v_a_7456_: *mut crate::leanh::LeanObject,
    mut v_a_7457_: *mut crate::leanh::LeanObject,
    mut v_a_7458_: *mut crate::leanh::LeanObject,
    mut v_a_7459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7461_ = l_Lean_Compiler_LCNF_mkLetDecl___closed__1;
    v___x_7462_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_7461_, v_a_7457_);
    v_a_7463_ = crate::leanh::lean_ctor_get(v___x_7462_, 0);
    crate::leanh::lean_inc(v_a_7463_);
    crate::leanh::lean_dec_ref(v___x_7462_);
    v___x_7464_ = l_Lean_Compiler_LCNF_erasedExpr;
    v___x_7465_ = crate::leanh::lean_box(1);
    v___x_7466_ = l_Lean_Compiler_LCNF_mkLetDecl(
        v_pu_7455_,
        v_a_7463_,
        v___x_7464_,
        v___x_7465_,
        v_a_7456_,
        v_a_7457_,
        v_a_7458_,
        v_a_7459_,
    );
    return v___x_7466_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDeclErased___boxed(
    mut v_pu_7467_: *mut crate::leanh::LeanObject,
    mut v_a_7468_: *mut crate::leanh::LeanObject,
    mut v_a_7469_: *mut crate::leanh::LeanObject,
    mut v_a_7470_: *mut crate::leanh::LeanObject,
    mut v_a_7471_: *mut crate::leanh::LeanObject,
    mut v_a_7472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7473_: u8 = 0;
    let mut v_res_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7473_ = (crate::leanh::lean_unbox(v_pu_7467_) as u8);
    v_res_7474_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
        v_pu_boxed_7473_,
        v_a_7468_,
        v_a_7469_,
        v_a_7470_,
        v_a_7471_,
    );
    crate::leanh::lean_dec(v_a_7471_);
    crate::leanh::lean_dec_ref(v_a_7470_);
    crate::leanh::lean_dec(v_a_7469_);
    crate::leanh::lean_dec_ref(v_a_7468_);
    return v_res_7474_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkReturnErased(
    mut v_pu_7475_: u8,
    mut v_a_7476_: *mut crate::leanh::LeanObject,
    mut v_a_7477_: *mut crate::leanh::LeanObject,
    mut v_a_7478_: *mut crate::leanh::LeanObject,
    mut v_a_7479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7485_: u8 = 0;
    let mut v_fvarId_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7492_: u8 = 0;
    let mut v_a_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7496_: u8 = 0;
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7481_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
                    v_pu_7475_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_,
                );
                if crate::leanh::lean_obj_tag(v___x_7481_) == 0 {
                    v_a_7482_ = crate::leanh::lean_ctor_get(v___x_7481_, 0);
                    v_isSharedCheck_7492_ = (!crate::leanh::lean_is_exclusive(v___x_7481_)) as u8;
                    if v_isSharedCheck_7492_ == 0 {
                        v___x_7484_ = v___x_7481_;
                        v_isShared_7485_ = v_isSharedCheck_7492_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7482_);
                        crate::leanh::lean_dec(v___x_7481_);
                        v___x_7484_ = crate::leanh::lean_box(0);
                        v_isShared_7485_ = v_isSharedCheck_7492_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7493_ = crate::leanh::lean_ctor_get(v___x_7481_, 0);
                    v_isSharedCheck_7500_ = (!crate::leanh::lean_is_exclusive(v___x_7481_)) as u8;
                    if v_isSharedCheck_7500_ == 0 {
                        v___x_7495_ = v___x_7481_;
                        v_isShared_7496_ = v_isSharedCheck_7500_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7493_);
                        crate::leanh::lean_dec(v___x_7481_);
                        v___x_7495_ = crate::leanh::lean_box(0);
                        v_isShared_7496_ = v_isSharedCheck_7500_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_7486_ = crate::leanh::lean_ctor_get(v_a_7482_, 0);
                crate::leanh::lean_inc(v_fvarId_7486_);
                v___x_7487_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7487_, 0, v_fvarId_7486_);
                v___x_7488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7488_, 0, v_a_7482_);
                crate::leanh::lean_ctor_set(v___x_7488_, 1, v___x_7487_);
                if v_isShared_7485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7484_, 0, v___x_7488_);
                    v___x_7490_ = v___x_7484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7491_, 0, v___x_7488_);
                    v___x_7490_ = v_reuseFailAlloc_7491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7490_;
            }
            3 => {
                if v_isShared_7496_ == 0 {
                    v___x_7498_ = v___x_7495_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7499_, 0, v_a_7493_);
                    v___x_7498_ = v_reuseFailAlloc_7499_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkReturnErased___boxed(
    mut v_pu_7501_: *mut crate::leanh::LeanObject,
    mut v_a_7502_: *mut crate::leanh::LeanObject,
    mut v_a_7503_: *mut crate::leanh::LeanObject,
    mut v_a_7504_: *mut crate::leanh::LeanObject,
    mut v_a_7505_: *mut crate::leanh::LeanObject,
    mut v_a_7506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7507_: u8 = 0;
    let mut v_res_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7507_ = (crate::leanh::lean_unbox(v_pu_7501_) as u8);
    v_res_7508_ = l_Lean_Compiler_LCNF_mkReturnErased(
        v_pu_boxed_7507_,
        v_a_7502_,
        v_a_7503_,
        v_a_7504_,
        v_a_7505_,
    );
    crate::leanh::lean_dec(v_a_7505_);
    crate::leanh::lean_dec_ref(v_a_7504_);
    crate::leanh::lean_dec(v_a_7503_);
    crate::leanh::lean_dec_ref(v_a_7502_);
    return v_res_7508_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(
    mut v_pu_7509_: u8,
    mut v_p_7510_: *mut crate::leanh::LeanObject,
    mut v_type_7511_: *mut crate::leanh::LeanObject,
    mut v_a_7512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_7517_: u8 = 0;
    let mut v___x_7518_: usize = 0;
    let mut v___x_7519_: usize = 0;
    let mut v___x_7520_: u8 = 0;
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7523_: u8 = 0;
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7529_: u8 = 0;
    let mut v_p_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7539_: u8 = 0;
    let mut v_isSharedCheck_7540_: u8 = 0;
    let mut v_unused_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7514_ = crate::leanh::lean_ctor_get(v_p_7510_, 0);
                v_binderName_7515_ = crate::leanh::lean_ctor_get(v_p_7510_, 1);
                v_type_7516_ = crate::leanh::lean_ctor_get(v_p_7510_, 2);
                v_borrow_7517_ = crate::leanh::lean_ctor_get_uint8(
                    v_p_7510_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_7518_ = lean_ptr_addr(v_type_7511_);
                v___x_7519_ = lean_ptr_addr(v_type_7516_);
                v___x_7520_ = lean_usize_dec_eq(v___x_7518_, v___x_7519_);
                if v___x_7520_ == 0 {
                    crate::leanh::lean_inc(v_binderName_7515_);
                    crate::leanh::lean_inc(v_fvarId_7514_);
                    v_isSharedCheck_7540_ = (!crate::leanh::lean_is_exclusive(v_p_7510_)) as u8;
                    if v_isSharedCheck_7540_ == 0 {
                        v_unused_7541_ = crate::leanh::lean_ctor_get(v_p_7510_, 2);
                        crate::leanh::lean_dec(v_unused_7541_);
                        v_unused_7542_ = crate::leanh::lean_ctor_get(v_p_7510_, 1);
                        crate::leanh::lean_dec(v_unused_7542_);
                        v_unused_7543_ = crate::leanh::lean_ctor_get(v_p_7510_, 0);
                        crate::leanh::lean_dec(v_unused_7543_);
                        v___x_7522_ = v_p_7510_;
                        v_isShared_7523_ = v_isSharedCheck_7540_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_p_7510_);
                        v___x_7522_ = crate::leanh::lean_box(0);
                        v_isShared_7523_ = v_isSharedCheck_7540_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_7511_);
                    v___x_7544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7544_, 0, v_p_7510_);
                    return v___x_7544_;
                }
            }
            1 => {
                v___x_7524_ = lean_st_ref_take(v_a_7512_);
                v_lctx_7525_ = crate::leanh::lean_ctor_get(v___x_7524_, 0);
                v_nextIdx_7526_ = crate::leanh::lean_ctor_get(v___x_7524_, 1);
                v_isSharedCheck_7539_ = (!crate::leanh::lean_is_exclusive(v___x_7524_)) as u8;
                if v_isSharedCheck_7539_ == 0 {
                    v___x_7528_ = v___x_7524_;
                    v_isShared_7529_ = v_isSharedCheck_7539_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7526_);
                    crate::leanh::lean_inc(v_lctx_7525_);
                    crate::leanh::lean_dec(v___x_7524_);
                    v___x_7528_ = crate::leanh::lean_box(0);
                    v_isShared_7529_ = v_isSharedCheck_7539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_7523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7522_, 2, v_type_7511_);
                    v_p_7531_ = v___x_7522_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7538_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7538_, 0, v_fvarId_7514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7538_, 1, v_binderName_7515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7538_, 2, v_type_7511_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7538_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_borrow_7517_,
                    );
                    v_p_7531_ = v_reuseFailAlloc_7538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_p_7531_);
                v___x_7532_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7509_, v_lctx_7525_, v_p_7531_);
                if v_isShared_7529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7528_, 0, v___x_7532_);
                    v___x_7534_ = v___x_7528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7537_, 0, v___x_7532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7537_, 1, v_nextIdx_7526_);
                    v___x_7534_ = v_reuseFailAlloc_7537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7535_ = lean_st_ref_set(v_a_7512_, v___x_7534_);
                v___x_7536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7536_, 0, v_p_7531_);
                return v___x_7536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(
    mut v_pu_7545_: *mut crate::leanh::LeanObject,
    mut v_p_7546_: *mut crate::leanh::LeanObject,
    mut v_type_7547_: *mut crate::leanh::LeanObject,
    mut v_a_7548_: *mut crate::leanh::LeanObject,
    mut v_a_7549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7550_: u8 = 0;
    let mut v_res_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7550_ = (crate::leanh::lean_unbox(v_pu_7545_) as u8);
    v_res_7551_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(
            v_pu_boxed_7550_,
            v_p_7546_,
            v_type_7547_,
            v_a_7548_,
        );
    crate::leanh::lean_dec(v_a_7548_);
    return v_res_7551_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(
    mut v_pu_7552_: u8,
    mut v_p_7553_: *mut crate::leanh::LeanObject,
    mut v_type_7554_: *mut crate::leanh::LeanObject,
    mut v_a_7555_: *mut crate::leanh::LeanObject,
    mut v_a_7556_: *mut crate::leanh::LeanObject,
    mut v_a_7557_: *mut crate::leanh::LeanObject,
    mut v_a_7558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7560_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(
            v_pu_7552_,
            v_p_7553_,
            v_type_7554_,
            v_a_7556_,
        );
    return v___x_7560_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed(
    mut v_pu_7561_: *mut crate::leanh::LeanObject,
    mut v_p_7562_: *mut crate::leanh::LeanObject,
    mut v_type_7563_: *mut crate::leanh::LeanObject,
    mut v_a_7564_: *mut crate::leanh::LeanObject,
    mut v_a_7565_: *mut crate::leanh::LeanObject,
    mut v_a_7566_: *mut crate::leanh::LeanObject,
    mut v_a_7567_: *mut crate::leanh::LeanObject,
    mut v_a_7568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7569_: u8 = 0;
    let mut v_res_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7569_ = (crate::leanh::lean_unbox(v_pu_7561_) as u8);
    v_res_7570_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(
        v_pu_boxed_7569_,
        v_p_7562_,
        v_type_7563_,
        v_a_7564_,
        v_a_7565_,
        v_a_7566_,
        v_a_7567_,
    );
    crate::leanh::lean_dec(v_a_7567_);
    crate::leanh::lean_dec_ref(v_a_7566_);
    crate::leanh::lean_dec(v_a_7565_);
    crate::leanh::lean_dec_ref(v_a_7564_);
    return v_res_7570_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(
    mut v_pu_7571_: u8,
    mut v_p_7572_: *mut crate::leanh::LeanObject,
    mut v_borrow_7573_: u8,
    mut v_a_7574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_7579_: u8 = 0;
    let mut v___x_7581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7586_: u8 = 0;
    let mut v_p_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7594_: u8 = 0;
    let mut v___x_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7576_ = crate::leanh::lean_ctor_get(v_p_7572_, 0);
                v_binderName_7577_ = crate::leanh::lean_ctor_get(v_p_7572_, 1);
                v_type_7578_ = crate::leanh::lean_ctor_get(v_p_7572_, 2);
                v_borrow_7579_ = crate::leanh::lean_ctor_get_uint8(
                    v_p_7572_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_borrow_7573_ == 0 {
                    if v_borrow_7579_ == 0 {
                        v___x_7595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7595_, 0, v_p_7572_);
                        return v___x_7595_;
                    } else {
                        crate::leanh::lean_inc_ref(v_type_7578_);
                        crate::leanh::lean_inc(v_binderName_7577_);
                        crate::leanh::lean_inc(v_fvarId_7576_);
                        crate::leanh::lean_dec_ref(v_p_7572_);
                        state = 1;
                        continue;
                    }
                } else {
                    if v_borrow_7579_ == 0 {
                        crate::leanh::lean_inc_ref(v_type_7578_);
                        crate::leanh::lean_inc(v_binderName_7577_);
                        crate::leanh::lean_inc(v_fvarId_7576_);
                        crate::leanh::lean_dec_ref(v_p_7572_);
                        state = 1;
                        continue;
                    } else {
                        v___x_7596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7596_, 0, v_p_7572_);
                        return v___x_7596_;
                    }
                }
            }
            1 => {
                v___x_7581_ = lean_st_ref_take(v_a_7574_);
                v_lctx_7582_ = crate::leanh::lean_ctor_get(v___x_7581_, 0);
                v_nextIdx_7583_ = crate::leanh::lean_ctor_get(v___x_7581_, 1);
                v_isSharedCheck_7594_ = (!crate::leanh::lean_is_exclusive(v___x_7581_)) as u8;
                if v_isSharedCheck_7594_ == 0 {
                    v___x_7585_ = v___x_7581_;
                    v_isShared_7586_ = v_isSharedCheck_7594_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7583_);
                    crate::leanh::lean_inc(v_lctx_7582_);
                    crate::leanh::lean_dec(v___x_7581_);
                    v___x_7585_ = crate::leanh::lean_box(0);
                    v_isShared_7586_ = v_isSharedCheck_7594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_p_7587_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v_p_7587_, 0, v_fvarId_7576_);
                crate::leanh::lean_ctor_set(v_p_7587_, 1, v_binderName_7577_);
                crate::leanh::lean_ctor_set(v_p_7587_, 2, v_type_7578_);
                crate::leanh::lean_ctor_set_uint8(
                    v_p_7587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_borrow_7573_,
                );
                crate::leanh::lean_inc_ref(v_p_7587_);
                v___x_7588_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7571_, v_lctx_7582_, v_p_7587_);
                if v_isShared_7586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7585_, 0, v___x_7588_);
                    v___x_7590_ = v___x_7585_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7593_, 0, v___x_7588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7593_, 1, v_nextIdx_7583_);
                    v___x_7590_ = v_reuseFailAlloc_7593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7591_ = lean_st_ref_set(v_a_7574_, v___x_7590_);
                v___x_7592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7592_, 0, v_p_7587_);
                return v___x_7592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(
    mut v_pu_7597_: *mut crate::leanh::LeanObject,
    mut v_p_7598_: *mut crate::leanh::LeanObject,
    mut v_borrow_7599_: *mut crate::leanh::LeanObject,
    mut v_a_7600_: *mut crate::leanh::LeanObject,
    mut v_a_7601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7602_: u8 = 0;
    let mut v_borrow_boxed_7603_: u8 = 0;
    let mut v_res_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7602_ = (crate::leanh::lean_unbox(v_pu_7597_) as u8);
    v_borrow_boxed_7603_ = (crate::leanh::lean_unbox(v_borrow_7599_) as u8);
    v_res_7604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_7602_, v_p_7598_, v_borrow_boxed_7603_, v_a_7600_);
    crate::leanh::lean_dec(v_a_7600_);
    return v_res_7604_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(
    mut v_pu_7605_: u8,
    mut v_p_7606_: *mut crate::leanh::LeanObject,
    mut v_borrow_7607_: u8,
    mut v_a_7608_: *mut crate::leanh::LeanObject,
    mut v_a_7609_: *mut crate::leanh::LeanObject,
    mut v_a_7610_: *mut crate::leanh::LeanObject,
    mut v_a_7611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7613_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_7605_, v_p_7606_, v_borrow_7607_, v_a_7609_);
    return v___x_7613_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(
    mut v_pu_7614_: *mut crate::leanh::LeanObject,
    mut v_p_7615_: *mut crate::leanh::LeanObject,
    mut v_borrow_7616_: *mut crate::leanh::LeanObject,
    mut v_a_7617_: *mut crate::leanh::LeanObject,
    mut v_a_7618_: *mut crate::leanh::LeanObject,
    mut v_a_7619_: *mut crate::leanh::LeanObject,
    mut v_a_7620_: *mut crate::leanh::LeanObject,
    mut v_a_7621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7622_: u8 = 0;
    let mut v_borrow_boxed_7623_: u8 = 0;
    let mut v_res_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7622_ = (crate::leanh::lean_unbox(v_pu_7614_) as u8);
    v_borrow_boxed_7623_ = (crate::leanh::lean_unbox(v_borrow_7616_) as u8);
    v_res_7624_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(
            v_pu_boxed_7622_,
            v_p_7615_,
            v_borrow_boxed_7623_,
            v_a_7617_,
            v_a_7618_,
            v_a_7619_,
            v_a_7620_,
        );
    crate::leanh::lean_dec(v_a_7620_);
    crate::leanh::lean_dec_ref(v_a_7619_);
    crate::leanh::lean_dec(v_a_7618_);
    crate::leanh::lean_dec_ref(v_a_7617_);
    return v_res_7624_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
    mut v_pu_7625_: u8,
    mut v_decl_7626_: *mut crate::leanh::LeanObject,
    mut v_type_7627_: *mut crate::leanh::LeanObject,
    mut v_value_7628_: *mut crate::leanh::LeanObject,
    mut v_a_7629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_7631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7636_: u8 = 0;
    let mut v___x_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7639_: u8 = 0;
    let mut v___x_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7645_: u8 = 0;
    let mut v_decl_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7655_: u8 = 0;
    let mut v_isSharedCheck_7656_: u8 = 0;
    let mut v_unused_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: usize = 0;
    let mut v___x_7663_: usize = 0;
    let mut v___x_7664_: u8 = 0;
    let mut v___x_7665_: usize = 0;
    let mut v___x_7666_: usize = 0;
    let mut v___x_7667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7631_ = crate::leanh::lean_ctor_get(v_decl_7626_, 0);
                v_binderName_7632_ = crate::leanh::lean_ctor_get(v_decl_7626_, 1);
                v_type_7633_ = crate::leanh::lean_ctor_get(v_decl_7626_, 2);
                v_value_7634_ = crate::leanh::lean_ctor_get(v_decl_7626_, 3);
                v___x_7662_ = lean_ptr_addr(v_type_7627_);
                v___x_7663_ = lean_ptr_addr(v_type_7633_);
                v___x_7664_ = lean_usize_dec_eq(v___x_7662_, v___x_7663_);
                if v___x_7664_ == 0 {
                    v___y_7636_ = v___x_7664_;
                    state = 1;
                    continue;
                } else {
                    v___x_7665_ = lean_ptr_addr(v_value_7628_);
                    v___x_7666_ = lean_ptr_addr(v_value_7634_);
                    v___x_7667_ = lean_usize_dec_eq(v___x_7665_, v___x_7666_);
                    v___y_7636_ = v___x_7667_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_7636_ == 0 {
                    crate::leanh::lean_inc(v_binderName_7632_);
                    crate::leanh::lean_inc(v_fvarId_7631_);
                    v_isSharedCheck_7656_ = (!crate::leanh::lean_is_exclusive(v_decl_7626_)) as u8;
                    if v_isSharedCheck_7656_ == 0 {
                        v_unused_7657_ = crate::leanh::lean_ctor_get(v_decl_7626_, 3);
                        crate::leanh::lean_dec(v_unused_7657_);
                        v_unused_7658_ = crate::leanh::lean_ctor_get(v_decl_7626_, 2);
                        crate::leanh::lean_dec(v_unused_7658_);
                        v_unused_7659_ = crate::leanh::lean_ctor_get(v_decl_7626_, 1);
                        crate::leanh::lean_dec(v_unused_7659_);
                        v_unused_7660_ = crate::leanh::lean_ctor_get(v_decl_7626_, 0);
                        crate::leanh::lean_dec(v_unused_7660_);
                        v___x_7638_ = v_decl_7626_;
                        v_isShared_7639_ = v_isSharedCheck_7656_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_decl_7626_);
                        v___x_7638_ = crate::leanh::lean_box(0);
                        v_isShared_7639_ = v_isSharedCheck_7656_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_7628_);
                    crate::leanh::lean_dec_ref(v_type_7627_);
                    v___x_7661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7661_, 0, v_decl_7626_);
                    return v___x_7661_;
                }
            }
            2 => {
                v___x_7640_ = lean_st_ref_take(v_a_7629_);
                v_lctx_7641_ = crate::leanh::lean_ctor_get(v___x_7640_, 0);
                v_nextIdx_7642_ = crate::leanh::lean_ctor_get(v___x_7640_, 1);
                v_isSharedCheck_7655_ = (!crate::leanh::lean_is_exclusive(v___x_7640_)) as u8;
                if v_isSharedCheck_7655_ == 0 {
                    v___x_7644_ = v___x_7640_;
                    v_isShared_7645_ = v_isSharedCheck_7655_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7642_);
                    crate::leanh::lean_inc(v_lctx_7641_);
                    crate::leanh::lean_dec(v___x_7640_);
                    v___x_7644_ = crate::leanh::lean_box(0);
                    v_isShared_7645_ = v_isSharedCheck_7655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7638_, 3, v_value_7628_);
                    crate::leanh::lean_ctor_set(v___x_7638_, 2, v_type_7627_);
                    v_decl_7647_ = v___x_7638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7654_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7654_, 0, v_fvarId_7631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7654_, 1, v_binderName_7632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7654_, 2, v_type_7627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7654_, 3, v_value_7628_);
                    v_decl_7647_ = v_reuseFailAlloc_7654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_decl_7647_);
                v___x_7648_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_7625_, v_lctx_7641_, v_decl_7647_);
                if v_isShared_7645_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7644_, 0, v___x_7648_);
                    v___x_7650_ = v___x_7644_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7653_, 0, v___x_7648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7653_, 1, v_nextIdx_7642_);
                    v___x_7650_ = v_reuseFailAlloc_7653_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7651_ = lean_st_ref_set(v_a_7629_, v___x_7650_);
                v___x_7652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7652_, 0, v_decl_7647_);
                return v___x_7652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(
    mut v_pu_7668_: *mut crate::leanh::LeanObject,
    mut v_decl_7669_: *mut crate::leanh::LeanObject,
    mut v_type_7670_: *mut crate::leanh::LeanObject,
    mut v_value_7671_: *mut crate::leanh::LeanObject,
    mut v_a_7672_: *mut crate::leanh::LeanObject,
    mut v_a_7673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7674_ = (crate::leanh::lean_unbox(v_pu_7668_) as u8);
    v_res_7675_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_boxed_7674_,
            v_decl_7669_,
            v_type_7670_,
            v_value_7671_,
            v_a_7672_,
        );
    crate::leanh::lean_dec(v_a_7672_);
    return v_res_7675_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(
    mut v_pu_7676_: u8,
    mut v_decl_7677_: *mut crate::leanh::LeanObject,
    mut v_type_7678_: *mut crate::leanh::LeanObject,
    mut v_value_7679_: *mut crate::leanh::LeanObject,
    mut v_a_7680_: *mut crate::leanh::LeanObject,
    mut v_a_7681_: *mut crate::leanh::LeanObject,
    mut v_a_7682_: *mut crate::leanh::LeanObject,
    mut v_a_7683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7685_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_7676_,
            v_decl_7677_,
            v_type_7678_,
            v_value_7679_,
            v_a_7681_,
        );
    return v___x_7685_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed(
    mut v_pu_7686_: *mut crate::leanh::LeanObject,
    mut v_decl_7687_: *mut crate::leanh::LeanObject,
    mut v_type_7688_: *mut crate::leanh::LeanObject,
    mut v_value_7689_: *mut crate::leanh::LeanObject,
    mut v_a_7690_: *mut crate::leanh::LeanObject,
    mut v_a_7691_: *mut crate::leanh::LeanObject,
    mut v_a_7692_: *mut crate::leanh::LeanObject,
    mut v_a_7693_: *mut crate::leanh::LeanObject,
    mut v_a_7694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7695_: u8 = 0;
    let mut v_res_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7695_ = (crate::leanh::lean_unbox(v_pu_7686_) as u8);
    v_res_7696_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(
        v_pu_boxed_7695_,
        v_decl_7687_,
        v_type_7688_,
        v_value_7689_,
        v_a_7690_,
        v_a_7691_,
        v_a_7692_,
        v_a_7693_,
    );
    crate::leanh::lean_dec(v_a_7693_);
    crate::leanh::lean_dec_ref(v_a_7692_);
    crate::leanh::lean_dec(v_a_7691_);
    crate::leanh::lean_dec_ref(v_a_7690_);
    return v_res_7696_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
    mut v_pu_7697_: u8,
    mut v_decl_7698_: *mut crate::leanh::LeanObject,
    mut v_value_7699_: *mut crate::leanh::LeanObject,
    mut v_a_7700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_7702_ = crate::leanh::lean_ctor_get(v_decl_7698_, 2);
    crate::leanh::lean_inc_ref(v_type_7702_);
    v___x_7703_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_7697_,
            v_decl_7698_,
            v_type_7702_,
            v_value_7699_,
            v_a_7700_,
        );
    return v___x_7703_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg___boxed(
    mut v_pu_7704_: *mut crate::leanh::LeanObject,
    mut v_decl_7705_: *mut crate::leanh::LeanObject,
    mut v_value_7706_: *mut crate::leanh::LeanObject,
    mut v_a_7707_: *mut crate::leanh::LeanObject,
    mut v_a_7708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7709_: u8 = 0;
    let mut v_res_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7709_ = (crate::leanh::lean_unbox(v_pu_7704_) as u8);
    v_res_7710_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
        v_pu_boxed_7709_,
        v_decl_7705_,
        v_value_7706_,
        v_a_7707_,
    );
    crate::leanh::lean_dec(v_a_7707_);
    return v_res_7710_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue(
    mut v_pu_7711_: u8,
    mut v_decl_7712_: *mut crate::leanh::LeanObject,
    mut v_value_7713_: *mut crate::leanh::LeanObject,
    mut v_a_7714_: *mut crate::leanh::LeanObject,
    mut v_a_7715_: *mut crate::leanh::LeanObject,
    mut v_a_7716_: *mut crate::leanh::LeanObject,
    mut v_a_7717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7719_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
        v_pu_7711_,
        v_decl_7712_,
        v_value_7713_,
        v_a_7715_,
    );
    return v___x_7719_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(
    mut v_pu_7720_: *mut crate::leanh::LeanObject,
    mut v_decl_7721_: *mut crate::leanh::LeanObject,
    mut v_value_7722_: *mut crate::leanh::LeanObject,
    mut v_a_7723_: *mut crate::leanh::LeanObject,
    mut v_a_7724_: *mut crate::leanh::LeanObject,
    mut v_a_7725_: *mut crate::leanh::LeanObject,
    mut v_a_7726_: *mut crate::leanh::LeanObject,
    mut v_a_7727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7728_: u8 = 0;
    let mut v_res_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7728_ = (crate::leanh::lean_unbox(v_pu_7720_) as u8);
    v_res_7729_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(
        v_pu_boxed_7728_,
        v_decl_7721_,
        v_value_7722_,
        v_a_7723_,
        v_a_7724_,
        v_a_7725_,
        v_a_7726_,
    );
    crate::leanh::lean_dec(v_a_7726_);
    crate::leanh::lean_dec_ref(v_a_7725_);
    crate::leanh::lean_dec(v_a_7724_);
    crate::leanh::lean_dec_ref(v_a_7723_);
    return v_res_7729_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
    mut v_pu_7730_: u8,
    mut v_decl_7731_: *mut crate::leanh::LeanObject,
    mut v_type_7732_: *mut crate::leanh::LeanObject,
    mut v_params_7733_: *mut crate::leanh::LeanObject,
    mut v_value_7734_: *mut crate::leanh::LeanObject,
    mut v_a_7735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7748_: u8 = 0;
    let mut v_decl_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7756_: u8 = 0;
    let mut v___y_7758_: u8 = 0;
    let mut v___x_7759_: usize = 0;
    let mut v___x_7760_: usize = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: usize = 0;
    let mut v___x_7764_: usize = 0;
    let mut v___x_7765_: u8 = 0;
    let mut v___x_7766_: usize = 0;
    let mut v___x_7767_: usize = 0;
    let mut v___x_7768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7737_ = crate::leanh::lean_ctor_get(v_decl_7731_, 0);
                v_binderName_7738_ = crate::leanh::lean_ctor_get(v_decl_7731_, 1);
                v_params_7739_ = crate::leanh::lean_ctor_get(v_decl_7731_, 2);
                v_type_7740_ = crate::leanh::lean_ctor_get(v_decl_7731_, 3);
                v_value_7741_ = crate::leanh::lean_ctor_get(v_decl_7731_, 4);
                v___x_7763_ = lean_ptr_addr(v_type_7732_);
                v___x_7764_ = lean_ptr_addr(v_type_7740_);
                v___x_7765_ = lean_usize_dec_eq(v___x_7763_, v___x_7764_);
                if v___x_7765_ == 0 {
                    v___y_7758_ = v___x_7765_;
                    state = 4;
                    continue;
                } else {
                    v___x_7766_ = lean_ptr_addr(v_params_7733_);
                    v___x_7767_ = lean_ptr_addr(v_params_7739_);
                    v___x_7768_ = lean_usize_dec_eq(v___x_7766_, v___x_7767_);
                    v___y_7758_ = v___x_7768_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_7743_ = lean_st_ref_take(v_a_7735_);
                v_lctx_7744_ = crate::leanh::lean_ctor_get(v___x_7743_, 0);
                v_nextIdx_7745_ = crate::leanh::lean_ctor_get(v___x_7743_, 1);
                v_isSharedCheck_7756_ = (!crate::leanh::lean_is_exclusive(v___x_7743_)) as u8;
                if v_isSharedCheck_7756_ == 0 {
                    v___x_7747_ = v___x_7743_;
                    v_isShared_7748_ = v_isSharedCheck_7756_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextIdx_7745_);
                    crate::leanh::lean_inc(v_lctx_7744_);
                    crate::leanh::lean_dec(v___x_7743_);
                    v___x_7747_ = crate::leanh::lean_box(0);
                    v_isShared_7748_ = v_isSharedCheck_7756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_decl_7749_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_decl_7749_, 0, v_fvarId_7737_);
                crate::leanh::lean_ctor_set(v_decl_7749_, 1, v_binderName_7738_);
                crate::leanh::lean_ctor_set(v_decl_7749_, 2, v_params_7733_);
                crate::leanh::lean_ctor_set(v_decl_7749_, 3, v_type_7732_);
                crate::leanh::lean_ctor_set(v_decl_7749_, 4, v_value_7734_);
                crate::leanh::lean_inc_ref(v_decl_7749_);
                v___x_7750_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_7730_, v_lctx_7744_, v_decl_7749_);
                if v_isShared_7748_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7747_, 0, v___x_7750_);
                    v___x_7752_ = v___x_7747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 0, v___x_7750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 1, v_nextIdx_7745_);
                    v___x_7752_ = v_reuseFailAlloc_7755_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7753_ = lean_st_ref_set(v_a_7735_, v___x_7752_);
                v___x_7754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7754_, 0, v_decl_7749_);
                return v___x_7754_;
            }
            4 => {
                if v___y_7758_ == 0 {
                    crate::leanh::lean_inc(v_binderName_7738_);
                    crate::leanh::lean_inc(v_fvarId_7737_);
                    crate::leanh::lean_dec_ref(v_decl_7731_);
                    state = 1;
                    continue;
                } else {
                    v___x_7759_ = lean_ptr_addr(v_value_7734_);
                    v___x_7760_ = lean_ptr_addr(v_value_7741_);
                    v___x_7761_ = lean_usize_dec_eq(v___x_7759_, v___x_7760_);
                    if v___x_7761_ == 0 {
                        crate::leanh::lean_inc(v_binderName_7738_);
                        crate::leanh::lean_inc(v_fvarId_7737_);
                        crate::leanh::lean_dec_ref(v_decl_7731_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_value_7734_);
                        crate::leanh::lean_dec_ref(v_params_7733_);
                        crate::leanh::lean_dec_ref(v_type_7732_);
                        v___x_7762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7762_, 0, v_decl_7731_);
                        return v___x_7762_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(
    mut v_pu_7769_: *mut crate::leanh::LeanObject,
    mut v_decl_7770_: *mut crate::leanh::LeanObject,
    mut v_type_7771_: *mut crate::leanh::LeanObject,
    mut v_params_7772_: *mut crate::leanh::LeanObject,
    mut v_value_7773_: *mut crate::leanh::LeanObject,
    mut v_a_7774_: *mut crate::leanh::LeanObject,
    mut v_a_7775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7776_: u8 = 0;
    let mut v_res_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7776_ = (crate::leanh::lean_unbox(v_pu_7769_) as u8);
    v_res_7777_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_boxed_7776_,
            v_decl_7770_,
            v_type_7771_,
            v_params_7772_,
            v_value_7773_,
            v_a_7774_,
        );
    crate::leanh::lean_dec(v_a_7774_);
    return v_res_7777_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(
    mut v_pu_7778_: u8,
    mut v_decl_7779_: *mut crate::leanh::LeanObject,
    mut v_type_7780_: *mut crate::leanh::LeanObject,
    mut v_params_7781_: *mut crate::leanh::LeanObject,
    mut v_value_7782_: *mut crate::leanh::LeanObject,
    mut v_a_7783_: *mut crate::leanh::LeanObject,
    mut v_a_7784_: *mut crate::leanh::LeanObject,
    mut v_a_7785_: *mut crate::leanh::LeanObject,
    mut v_a_7786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7788_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_7778_,
            v_decl_7779_,
            v_type_7780_,
            v_params_7781_,
            v_value_7782_,
            v_a_7784_,
        );
    return v___x_7788_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___boxed(
    mut v_pu_7789_: *mut crate::leanh::LeanObject,
    mut v_decl_7790_: *mut crate::leanh::LeanObject,
    mut v_type_7791_: *mut crate::leanh::LeanObject,
    mut v_params_7792_: *mut crate::leanh::LeanObject,
    mut v_value_7793_: *mut crate::leanh::LeanObject,
    mut v_a_7794_: *mut crate::leanh::LeanObject,
    mut v_a_7795_: *mut crate::leanh::LeanObject,
    mut v_a_7796_: *mut crate::leanh::LeanObject,
    mut v_a_7797_: *mut crate::leanh::LeanObject,
    mut v_a_7798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7799_: u8 = 0;
    let mut v_res_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7799_ = (crate::leanh::lean_unbox(v_pu_7789_) as u8);
    v_res_7800_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(
        v_pu_boxed_7799_,
        v_decl_7790_,
        v_type_7791_,
        v_params_7792_,
        v_value_7793_,
        v_a_7794_,
        v_a_7795_,
        v_a_7796_,
        v_a_7797_,
    );
    crate::leanh::lean_dec(v_a_7797_);
    crate::leanh::lean_dec_ref(v_a_7796_);
    crate::leanh::lean_dec(v_a_7795_);
    crate::leanh::lean_dec_ref(v_a_7794_);
    return v_res_7800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(
    mut v_pu_7801_: u8,
    mut v_decl_7802_: *mut crate::leanh::LeanObject,
    mut v_type_7803_: *mut crate::leanh::LeanObject,
    mut v_value_7804_: *mut crate::leanh::LeanObject,
    mut v_a_7805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_7807_ = crate::leanh::lean_ctor_get(v_decl_7802_, 2);
    crate::leanh::lean_inc_ref(v_params_7807_);
    v___x_7808_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_7801_,
            v_decl_7802_,
            v_type_7803_,
            v_params_7807_,
            v_value_7804_,
            v_a_7805_,
        );
    return v___x_7808_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg___boxed(
    mut v_pu_7809_: *mut crate::leanh::LeanObject,
    mut v_decl_7810_: *mut crate::leanh::LeanObject,
    mut v_type_7811_: *mut crate::leanh::LeanObject,
    mut v_value_7812_: *mut crate::leanh::LeanObject,
    mut v_a_7813_: *mut crate::leanh::LeanObject,
    mut v_a_7814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7815_: u8 = 0;
    let mut v_res_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7815_ = (crate::leanh::lean_unbox(v_pu_7809_) as u8);
    v_res_7816_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(
        v_pu_boxed_7815_,
        v_decl_7810_,
        v_type_7811_,
        v_value_7812_,
        v_a_7813_,
    );
    crate::leanh::lean_dec(v_a_7813_);
    return v_res_7816_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27(
    mut v_pu_7817_: u8,
    mut v_decl_7818_: *mut crate::leanh::LeanObject,
    mut v_type_7819_: *mut crate::leanh::LeanObject,
    mut v_value_7820_: *mut crate::leanh::LeanObject,
    mut v_a_7821_: *mut crate::leanh::LeanObject,
    mut v_a_7822_: *mut crate::leanh::LeanObject,
    mut v_a_7823_: *mut crate::leanh::LeanObject,
    mut v_a_7824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_7826_ = crate::leanh::lean_ctor_get(v_decl_7818_, 2);
    crate::leanh::lean_inc_ref(v_params_7826_);
    v___x_7827_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_7817_,
            v_decl_7818_,
            v_type_7819_,
            v_params_7826_,
            v_value_7820_,
            v_a_7822_,
        );
    return v___x_7827_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27___boxed(
    mut v_pu_7828_: *mut crate::leanh::LeanObject,
    mut v_decl_7829_: *mut crate::leanh::LeanObject,
    mut v_type_7830_: *mut crate::leanh::LeanObject,
    mut v_value_7831_: *mut crate::leanh::LeanObject,
    mut v_a_7832_: *mut crate::leanh::LeanObject,
    mut v_a_7833_: *mut crate::leanh::LeanObject,
    mut v_a_7834_: *mut crate::leanh::LeanObject,
    mut v_a_7835_: *mut crate::leanh::LeanObject,
    mut v_a_7836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7837_: u8 = 0;
    let mut v_res_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7837_ = (crate::leanh::lean_unbox(v_pu_7828_) as u8);
    v_res_7838_ = l_Lean_Compiler_LCNF_FunDecl_update_x27(
        v_pu_boxed_7837_,
        v_decl_7829_,
        v_type_7830_,
        v_value_7831_,
        v_a_7832_,
        v_a_7833_,
        v_a_7834_,
        v_a_7835_,
    );
    crate::leanh::lean_dec(v_a_7835_);
    crate::leanh::lean_dec_ref(v_a_7834_);
    crate::leanh::lean_dec(v_a_7833_);
    crate::leanh::lean_dec_ref(v_a_7832_);
    return v_res_7838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(
    mut v_pu_7839_: u8,
    mut v_decl_7840_: *mut crate::leanh::LeanObject,
    mut v_value_7841_: *mut crate::leanh::LeanObject,
    mut v_a_7842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_7844_ = crate::leanh::lean_ctor_get(v_decl_7840_, 2);
    crate::leanh::lean_inc_ref(v_params_7844_);
    v_type_7845_ = crate::leanh::lean_ctor_get(v_decl_7840_, 3);
    crate::leanh::lean_inc_ref(v_type_7845_);
    v___x_7846_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_7839_,
            v_decl_7840_,
            v_type_7845_,
            v_params_7844_,
            v_value_7841_,
            v_a_7842_,
        );
    return v___x_7846_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg___boxed(
    mut v_pu_7847_: *mut crate::leanh::LeanObject,
    mut v_decl_7848_: *mut crate::leanh::LeanObject,
    mut v_value_7849_: *mut crate::leanh::LeanObject,
    mut v_a_7850_: *mut crate::leanh::LeanObject,
    mut v_a_7851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7852_: u8 = 0;
    let mut v_res_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7852_ = (crate::leanh::lean_unbox(v_pu_7847_) as u8);
    v_res_7853_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(
        v_pu_boxed_7852_,
        v_decl_7848_,
        v_value_7849_,
        v_a_7850_,
    );
    crate::leanh::lean_dec(v_a_7850_);
    return v_res_7853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue(
    mut v_pu_7854_: u8,
    mut v_decl_7855_: *mut crate::leanh::LeanObject,
    mut v_value_7856_: *mut crate::leanh::LeanObject,
    mut v_a_7857_: *mut crate::leanh::LeanObject,
    mut v_a_7858_: *mut crate::leanh::LeanObject,
    mut v_a_7859_: *mut crate::leanh::LeanObject,
    mut v_a_7860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_7862_ = crate::leanh::lean_ctor_get(v_decl_7855_, 2);
    crate::leanh::lean_inc_ref(v_params_7862_);
    v_type_7863_ = crate::leanh::lean_ctor_get(v_decl_7855_, 3);
    crate::leanh::lean_inc_ref(v_type_7863_);
    v___x_7864_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_7854_,
            v_decl_7855_,
            v_type_7863_,
            v_params_7862_,
            v_value_7856_,
            v_a_7858_,
        );
    return v___x_7864_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue___boxed(
    mut v_pu_7865_: *mut crate::leanh::LeanObject,
    mut v_decl_7866_: *mut crate::leanh::LeanObject,
    mut v_value_7867_: *mut crate::leanh::LeanObject,
    mut v_a_7868_: *mut crate::leanh::LeanObject,
    mut v_a_7869_: *mut crate::leanh::LeanObject,
    mut v_a_7870_: *mut crate::leanh::LeanObject,
    mut v_a_7871_: *mut crate::leanh::LeanObject,
    mut v_a_7872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7873_: u8 = 0;
    let mut v_res_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7873_ = (crate::leanh::lean_unbox(v_pu_7865_) as u8);
    v_res_7874_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(
        v_pu_boxed_7873_,
        v_decl_7866_,
        v_value_7867_,
        v_a_7868_,
        v_a_7869_,
        v_a_7870_,
        v_a_7871_,
    );
    crate::leanh::lean_dec(v_a_7871_);
    crate::leanh::lean_dec_ref(v_a_7870_);
    crate::leanh::lean_dec(v_a_7869_);
    crate::leanh::lean_dec_ref(v_a_7868_);
    return v_res_7874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__0(
    mut v_pu_7875_: u8,
    mut v_p_7876_: *mut crate::leanh::LeanObject,
    mut v_inst_7877_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7879_ = crate::leanh::lean_box((v_pu_7875_) as usize);
    v___x_7880_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_7880_, 0, v___x_7879_);
    crate::leanh::lean_closure_set(v___x_7880_, 1, v_p_7876_);
    crate::leanh::lean_closure_set(v___x_7880_, 2, v_____do__lift_7878_);
    v___x_7881_ = crate::leanh::lean_apply_2(v_inst_7877_, crate::leanh::lean_box(0), v___x_7880_);
    return v___x_7881_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(
    mut v_pu_7882_: *mut crate::leanh::LeanObject,
    mut v_p_7883_: *mut crate::leanh::LeanObject,
    mut v_inst_7884_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7886_: u8 = 0;
    let mut v_res_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7886_ = (crate::leanh::lean_unbox(v_pu_7882_) as u8);
    v_res_7887_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__0(
        v_pu_boxed_7886_,
        v_p_7883_,
        v_inst_7884_,
        v_____do__lift_7885_,
    );
    return v_res_7887_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__1(
    mut v_pu_7888_: u8,
    mut v_t_7889_: u8,
    mut v_type_7890_: *mut crate::leanh::LeanObject,
    mut v_toPure_7891_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7893_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_7888_,
        v_____do__lift_7892_,
        v_t_7889_,
        v_type_7890_,
    );
    v___x_7894_ =
        crate::leanh::lean_apply_2(v_toPure_7891_, crate::leanh::lean_box(0), v___x_7893_);
    return v___x_7894_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(
    mut v_pu_7895_: *mut crate::leanh::LeanObject,
    mut v_t_7896_: *mut crate::leanh::LeanObject,
    mut v_type_7897_: *mut crate::leanh::LeanObject,
    mut v_toPure_7898_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7900_: u8 = 0;
    let mut v_t_boxed_7901_: u8 = 0;
    let mut v_res_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7900_ = (crate::leanh::lean_unbox(v_pu_7895_) as u8);
    v_t_boxed_7901_ = (crate::leanh::lean_unbox(v_t_7896_) as u8);
    v_res_7902_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(
        v_pu_boxed_7900_,
        v_t_boxed_7901_,
        v_type_7897_,
        v_toPure_7898_,
        v_____do__lift_7899_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_7899_);
    return v_res_7902_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg(
    mut v_pu_7903_: u8,
    mut v_t_7904_: u8,
    mut v_inst_7905_: *mut crate::leanh::LeanObject,
    mut v_inst_7906_: *mut crate::leanh::LeanObject,
    mut v_inst_7907_: *mut crate::leanh::LeanObject,
    mut v_p_7908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7909_ = crate::leanh::lean_ctor_get(v_inst_7906_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7909_);
    v_toBind_7910_ = crate::leanh::lean_ctor_get(v_inst_7906_, 1);
    crate::leanh::lean_inc_n(v_toBind_7910_, 2);
    crate::leanh::lean_dec_ref(v_inst_7906_);
    v_type_7911_ = crate::leanh::lean_ctor_get(v_p_7908_, 2);
    crate::leanh::lean_inc_ref(v_type_7911_);
    v_toPure_7912_ = crate::leanh::lean_ctor_get(v_toApplicative_7909_, 1);
    crate::leanh::lean_inc(v_toPure_7912_);
    crate::leanh::lean_dec_ref(v_toApplicative_7909_);
    v___x_7913_ = crate::leanh::lean_box((v_pu_7903_) as usize);
    v___f_7914_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7914_, 0, v___x_7913_);
    crate::leanh::lean_closure_set(v___f_7914_, 1, v_p_7908_);
    crate::leanh::lean_closure_set(v___f_7914_, 2, v_inst_7905_);
    v___x_7915_ = crate::leanh::lean_box((v_pu_7903_) as usize);
    v___x_7916_ = crate::leanh::lean_box((v_t_7904_) as usize);
    v___f_7917_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7917_, 0, v___x_7915_);
    crate::leanh::lean_closure_set(v___f_7917_, 1, v___x_7916_);
    crate::leanh::lean_closure_set(v___f_7917_, 2, v_type_7911_);
    crate::leanh::lean_closure_set(v___f_7917_, 3, v_toPure_7912_);
    v___x_7918_ = crate::leanh::lean_apply_4(
        v_toBind_7910_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7907_,
        v___f_7917_,
    );
    v___x_7919_ = crate::leanh::lean_apply_4(
        v_toBind_7910_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7918_,
        v___f_7914_,
    );
    return v___x_7919_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___boxed(
    mut v_pu_7920_: *mut crate::leanh::LeanObject,
    mut v_t_7921_: *mut crate::leanh::LeanObject,
    mut v_inst_7922_: *mut crate::leanh::LeanObject,
    mut v_inst_7923_: *mut crate::leanh::LeanObject,
    mut v_inst_7924_: *mut crate::leanh::LeanObject,
    mut v_p_7925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7926_: u8 = 0;
    let mut v_t_boxed_7927_: u8 = 0;
    let mut v_res_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7926_ = (crate::leanh::lean_unbox(v_pu_7920_) as u8);
    v_t_boxed_7927_ = (crate::leanh::lean_unbox(v_t_7921_) as u8);
    v_res_7928_ = l_Lean_Compiler_LCNF_normParam___redArg(
        v_pu_boxed_7926_,
        v_t_boxed_7927_,
        v_inst_7922_,
        v_inst_7923_,
        v_inst_7924_,
        v_p_7925_,
    );
    return v_res_7928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam(
    mut v_m_7929_: *mut crate::leanh::LeanObject,
    mut v_pu_7930_: u8,
    mut v_t_7931_: u8,
    mut v_inst_7932_: *mut crate::leanh::LeanObject,
    mut v_inst_7933_: *mut crate::leanh::LeanObject,
    mut v_inst_7934_: *mut crate::leanh::LeanObject,
    mut v_p_7935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_7936_ = crate::leanh::lean_ctor_get(v_inst_7933_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_7936_);
    v_toBind_7937_ = crate::leanh::lean_ctor_get(v_inst_7933_, 1);
    crate::leanh::lean_inc_n(v_toBind_7937_, 2);
    crate::leanh::lean_dec_ref(v_inst_7933_);
    v_type_7938_ = crate::leanh::lean_ctor_get(v_p_7935_, 2);
    crate::leanh::lean_inc_ref(v_type_7938_);
    v_toPure_7939_ = crate::leanh::lean_ctor_get(v_toApplicative_7936_, 1);
    crate::leanh::lean_inc(v_toPure_7939_);
    crate::leanh::lean_dec_ref(v_toApplicative_7936_);
    v___x_7940_ = crate::leanh::lean_box((v_pu_7930_) as usize);
    v___f_7941_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7941_, 0, v___x_7940_);
    crate::leanh::lean_closure_set(v___f_7941_, 1, v_p_7935_);
    crate::leanh::lean_closure_set(v___f_7941_, 2, v_inst_7932_);
    v___x_7942_ = crate::leanh::lean_box((v_pu_7930_) as usize);
    v___x_7943_ = crate::leanh::lean_box((v_t_7931_) as usize);
    v___f_7944_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7944_, 0, v___x_7942_);
    crate::leanh::lean_closure_set(v___f_7944_, 1, v___x_7943_);
    crate::leanh::lean_closure_set(v___f_7944_, 2, v_type_7938_);
    crate::leanh::lean_closure_set(v___f_7944_, 3, v_toPure_7939_);
    v___x_7945_ = crate::leanh::lean_apply_4(
        v_toBind_7937_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7934_,
        v___f_7944_,
    );
    v___x_7946_ = crate::leanh::lean_apply_4(
        v_toBind_7937_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7945_,
        v___f_7941_,
    );
    return v___x_7946_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___boxed(
    mut v_m_7947_: *mut crate::leanh::LeanObject,
    mut v_pu_7948_: *mut crate::leanh::LeanObject,
    mut v_t_7949_: *mut crate::leanh::LeanObject,
    mut v_inst_7950_: *mut crate::leanh::LeanObject,
    mut v_inst_7951_: *mut crate::leanh::LeanObject,
    mut v_inst_7952_: *mut crate::leanh::LeanObject,
    mut v_p_7953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7954_: u8 = 0;
    let mut v_t_boxed_7955_: u8 = 0;
    let mut v_res_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7954_ = (crate::leanh::lean_unbox(v_pu_7948_) as u8);
    v_t_boxed_7955_ = (crate::leanh::lean_unbox(v_t_7949_) as u8);
    v_res_7956_ = l_Lean_Compiler_LCNF_normParam(
        v_m_7947_,
        v_pu_boxed_7954_,
        v_t_boxed_7955_,
        v_inst_7950_,
        v_inst_7951_,
        v_inst_7952_,
        v_p_7953_,
    );
    return v_res_7956_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___redArg(
    mut v_pu_7957_: u8,
    mut v_t_7958_: u8,
    mut v_inst_7959_: *mut crate::leanh::LeanObject,
    mut v_inst_7960_: *mut crate::leanh::LeanObject,
    mut v_inst_7961_: *mut crate::leanh::LeanObject,
    mut v_ps_7962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7963_ = crate::leanh::lean_box((v_pu_7957_) as usize);
    v___x_7964_ = crate::leanh::lean_box((v_t_7958_) as usize);
    crate::leanh::lean_inc_ref(v_inst_7960_);
    v___x_7965_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___x_7965_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7965_, 1, v___x_7963_);
    crate::leanh::lean_closure_set(v___x_7965_, 2, v___x_7964_);
    crate::leanh::lean_closure_set(v___x_7965_, 3, v_inst_7959_);
    crate::leanh::lean_closure_set(v___x_7965_, 4, v_inst_7960_);
    crate::leanh::lean_closure_set(v___x_7965_, 5, v_inst_7961_);
    v___x_7966_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7967_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_7960_,
        v___x_7965_,
        v___x_7966_,
        v_ps_7962_,
    );
    return v___x_7967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___redArg___boxed(
    mut v_pu_7968_: *mut crate::leanh::LeanObject,
    mut v_t_7969_: *mut crate::leanh::LeanObject,
    mut v_inst_7970_: *mut crate::leanh::LeanObject,
    mut v_inst_7971_: *mut crate::leanh::LeanObject,
    mut v_inst_7972_: *mut crate::leanh::LeanObject,
    mut v_ps_7973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7974_: u8 = 0;
    let mut v_t_boxed_7975_: u8 = 0;
    let mut v_res_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7974_ = (crate::leanh::lean_unbox(v_pu_7968_) as u8);
    v_t_boxed_7975_ = (crate::leanh::lean_unbox(v_t_7969_) as u8);
    v_res_7976_ = l_Lean_Compiler_LCNF_normParams___redArg(
        v_pu_boxed_7974_,
        v_t_boxed_7975_,
        v_inst_7970_,
        v_inst_7971_,
        v_inst_7972_,
        v_ps_7973_,
    );
    return v_res_7976_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams(
    mut v_m_7977_: *mut crate::leanh::LeanObject,
    mut v_pu_7978_: u8,
    mut v_t_7979_: u8,
    mut v_inst_7980_: *mut crate::leanh::LeanObject,
    mut v_inst_7981_: *mut crate::leanh::LeanObject,
    mut v_inst_7982_: *mut crate::leanh::LeanObject,
    mut v_ps_7983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7984_ = l_Lean_Compiler_LCNF_normParams___redArg(
        v_pu_7978_,
        v_t_7979_,
        v_inst_7980_,
        v_inst_7981_,
        v_inst_7982_,
        v_ps_7983_,
    );
    return v___x_7984_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___boxed(
    mut v_m_7985_: *mut crate::leanh::LeanObject,
    mut v_pu_7986_: *mut crate::leanh::LeanObject,
    mut v_t_7987_: *mut crate::leanh::LeanObject,
    mut v_inst_7988_: *mut crate::leanh::LeanObject,
    mut v_inst_7989_: *mut crate::leanh::LeanObject,
    mut v_inst_7990_: *mut crate::leanh::LeanObject,
    mut v_ps_7991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7992_: u8 = 0;
    let mut v_t_boxed_7993_: u8 = 0;
    let mut v_res_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7992_ = (crate::leanh::lean_unbox(v_pu_7986_) as u8);
    v_t_boxed_7993_ = (crate::leanh::lean_unbox(v_t_7987_) as u8);
    v_res_7994_ = l_Lean_Compiler_LCNF_normParams(
        v_m_7985_,
        v_pu_boxed_7992_,
        v_t_boxed_7993_,
        v_inst_7988_,
        v_inst_7989_,
        v_inst_7990_,
        v_ps_7991_,
    );
    return v_res_7994_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(
    mut v_pu_7995_: u8,
    mut v_decl_7996_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7997_: *mut crate::leanh::LeanObject,
    mut v_inst_7998_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8000_ = crate::leanh::lean_box((v_pu_7995_) as usize);
    v___x_8001_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_8001_, 0, v___x_8000_);
    crate::leanh::lean_closure_set(v___x_8001_, 1, v_decl_7996_);
    crate::leanh::lean_closure_set(v___x_8001_, 2, v_____do__lift_7997_);
    crate::leanh::lean_closure_set(v___x_8001_, 3, v_____do__lift_7999_);
    v___x_8002_ = crate::leanh::lean_apply_2(v_inst_7998_, crate::leanh::lean_box(0), v___x_8001_);
    return v___x_8002_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(
    mut v_pu_8003_: *mut crate::leanh::LeanObject,
    mut v_decl_8004_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8005_: *mut crate::leanh::LeanObject,
    mut v_inst_8006_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8008_: u8 = 0;
    let mut v_res_8009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8008_ = (crate::leanh::lean_unbox(v_pu_8003_) as u8);
    v_res_8009_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0(
        v_pu_boxed_8008_,
        v_decl_8004_,
        v_____do__lift_8005_,
        v_inst_8006_,
        v_____do__lift_8007_,
    );
    return v_res_8009_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(
    mut v_pu_8010_: u8,
    mut v_value_8011_: *mut crate::leanh::LeanObject,
    mut v_t_8012_: u8,
    mut v_toPure_8013_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8015_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_8010_,
        v_____do__lift_8014_,
        v_value_8011_,
        v_t_8012_,
    );
    v___x_8016_ =
        crate::leanh::lean_apply_2(v_toPure_8013_, crate::leanh::lean_box(0), v___x_8015_);
    return v___x_8016_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(
    mut v_pu_8017_: *mut crate::leanh::LeanObject,
    mut v_value_8018_: *mut crate::leanh::LeanObject,
    mut v_t_8019_: *mut crate::leanh::LeanObject,
    mut v_toPure_8020_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8022_: u8 = 0;
    let mut v_t_boxed_8023_: u8 = 0;
    let mut v_res_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8022_ = (crate::leanh::lean_unbox(v_pu_8017_) as u8);
    v_t_boxed_8023_ = (crate::leanh::lean_unbox(v_t_8019_) as u8);
    v_res_8024_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(
        v_pu_boxed_8022_,
        v_value_8018_,
        v_t_boxed_8023_,
        v_toPure_8020_,
        v_____do__lift_8021_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_8021_);
    return v_res_8024_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(
    mut v_pu_8025_: u8,
    mut v_decl_8026_: *mut crate::leanh::LeanObject,
    mut v_inst_8027_: *mut crate::leanh::LeanObject,
    mut v_value_8028_: *mut crate::leanh::LeanObject,
    mut v_t_8029_: u8,
    mut v_toPure_8030_: *mut crate::leanh::LeanObject,
    mut v_toBind_8031_: *mut crate::leanh::LeanObject,
    mut v_inst_8032_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8034_ = crate::leanh::lean_box((v_pu_8025_) as usize);
    v___f_8035_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_8035_, 0, v___x_8034_);
    crate::leanh::lean_closure_set(v___f_8035_, 1, v_decl_8026_);
    crate::leanh::lean_closure_set(v___f_8035_, 2, v_____do__lift_8033_);
    crate::leanh::lean_closure_set(v___f_8035_, 3, v_inst_8027_);
    v___x_8036_ = crate::leanh::lean_box((v_pu_8025_) as usize);
    v___x_8037_ = crate::leanh::lean_box((v_t_8029_) as usize);
    v___f_8038_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_8038_, 0, v___x_8036_);
    crate::leanh::lean_closure_set(v___f_8038_, 1, v_value_8028_);
    crate::leanh::lean_closure_set(v___f_8038_, 2, v___x_8037_);
    crate::leanh::lean_closure_set(v___f_8038_, 3, v_toPure_8030_);
    crate::leanh::lean_inc(v_toBind_8031_);
    v___x_8039_ = crate::leanh::lean_apply_4(
        v_toBind_8031_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_8032_,
        v___f_8038_,
    );
    v___x_8040_ = crate::leanh::lean_apply_4(
        v_toBind_8031_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_8039_,
        v___f_8035_,
    );
    return v___x_8040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(
    mut v_pu_8041_: *mut crate::leanh::LeanObject,
    mut v_decl_8042_: *mut crate::leanh::LeanObject,
    mut v_inst_8043_: *mut crate::leanh::LeanObject,
    mut v_value_8044_: *mut crate::leanh::LeanObject,
    mut v_t_8045_: *mut crate::leanh::LeanObject,
    mut v_toPure_8046_: *mut crate::leanh::LeanObject,
    mut v_toBind_8047_: *mut crate::leanh::LeanObject,
    mut v_inst_8048_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8050_: u8 = 0;
    let mut v_t_boxed_8051_: u8 = 0;
    let mut v_res_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8050_ = (crate::leanh::lean_unbox(v_pu_8041_) as u8);
    v_t_boxed_8051_ = (crate::leanh::lean_unbox(v_t_8045_) as u8);
    v_res_8052_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(
        v_pu_boxed_8050_,
        v_decl_8042_,
        v_inst_8043_,
        v_value_8044_,
        v_t_boxed_8051_,
        v_toPure_8046_,
        v_toBind_8047_,
        v_inst_8048_,
        v_____do__lift_8049_,
    );
    return v_res_8052_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg(
    mut v_pu_8053_: u8,
    mut v_t_8054_: u8,
    mut v_inst_8055_: *mut crate::leanh::LeanObject,
    mut v_inst_8056_: *mut crate::leanh::LeanObject,
    mut v_inst_8057_: *mut crate::leanh::LeanObject,
    mut v_decl_8058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_8059_ = crate::leanh::lean_ctor_get(v_inst_8056_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_8059_);
    v_toBind_8060_ = crate::leanh::lean_ctor_get(v_inst_8056_, 1);
    crate::leanh::lean_inc_n(v_toBind_8060_, 3);
    crate::leanh::lean_dec_ref(v_inst_8056_);
    v_type_8061_ = crate::leanh::lean_ctor_get(v_decl_8058_, 2);
    crate::leanh::lean_inc_ref(v_type_8061_);
    v_value_8062_ = crate::leanh::lean_ctor_get(v_decl_8058_, 3);
    crate::leanh::lean_inc(v_value_8062_);
    v_toPure_8063_ = crate::leanh::lean_ctor_get(v_toApplicative_8059_, 1);
    crate::leanh::lean_inc_n(v_toPure_8063_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_8059_);
    v___x_8064_ = crate::leanh::lean_box((v_pu_8053_) as usize);
    v___x_8065_ = crate::leanh::lean_box((v_t_8054_) as usize);
    crate::leanh::lean_inc(v_inst_8057_);
    v___f_8066_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_8066_, 0, v___x_8064_);
    crate::leanh::lean_closure_set(v___f_8066_, 1, v_decl_8058_);
    crate::leanh::lean_closure_set(v___f_8066_, 2, v_inst_8055_);
    crate::leanh::lean_closure_set(v___f_8066_, 3, v_value_8062_);
    crate::leanh::lean_closure_set(v___f_8066_, 4, v___x_8065_);
    crate::leanh::lean_closure_set(v___f_8066_, 5, v_toPure_8063_);
    crate::leanh::lean_closure_set(v___f_8066_, 6, v_toBind_8060_);
    crate::leanh::lean_closure_set(v___f_8066_, 7, v_inst_8057_);
    v___x_8067_ = crate::leanh::lean_box((v_pu_8053_) as usize);
    v___x_8068_ = crate::leanh::lean_box((v_t_8054_) as usize);
    v___f_8069_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_8069_, 0, v___x_8067_);
    crate::leanh::lean_closure_set(v___f_8069_, 1, v___x_8068_);
    crate::leanh::lean_closure_set(v___f_8069_, 2, v_type_8061_);
    crate::leanh::lean_closure_set(v___f_8069_, 3, v_toPure_8063_);
    v___x_8070_ = crate::leanh::lean_apply_4(
        v_toBind_8060_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_8057_,
        v___f_8069_,
    );
    v___x_8071_ = crate::leanh::lean_apply_4(
        v_toBind_8060_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_8070_,
        v___f_8066_,
    );
    return v___x_8071_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(
    mut v_pu_8072_: *mut crate::leanh::LeanObject,
    mut v_t_8073_: *mut crate::leanh::LeanObject,
    mut v_inst_8074_: *mut crate::leanh::LeanObject,
    mut v_inst_8075_: *mut crate::leanh::LeanObject,
    mut v_inst_8076_: *mut crate::leanh::LeanObject,
    mut v_decl_8077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8078_: u8 = 0;
    let mut v_t_boxed_8079_: u8 = 0;
    let mut v_res_8080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8078_ = (crate::leanh::lean_unbox(v_pu_8072_) as u8);
    v_t_boxed_8079_ = (crate::leanh::lean_unbox(v_t_8073_) as u8);
    v_res_8080_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(
        v_pu_boxed_8078_,
        v_t_boxed_8079_,
        v_inst_8074_,
        v_inst_8075_,
        v_inst_8076_,
        v_decl_8077_,
    );
    return v_res_8080_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl(
    mut v_m_8081_: *mut crate::leanh::LeanObject,
    mut v_pu_8082_: u8,
    mut v_t_8083_: u8,
    mut v_inst_8084_: *mut crate::leanh::LeanObject,
    mut v_inst_8085_: *mut crate::leanh::LeanObject,
    mut v_inst_8086_: *mut crate::leanh::LeanObject,
    mut v_decl_8087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8088_ = l_Lean_Compiler_LCNF_normLetDecl___redArg(
        v_pu_8082_,
        v_t_8083_,
        v_inst_8084_,
        v_inst_8085_,
        v_inst_8086_,
        v_decl_8087_,
    );
    return v___x_8088_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___boxed(
    mut v_m_8089_: *mut crate::leanh::LeanObject,
    mut v_pu_8090_: *mut crate::leanh::LeanObject,
    mut v_t_8091_: *mut crate::leanh::LeanObject,
    mut v_inst_8092_: *mut crate::leanh::LeanObject,
    mut v_inst_8093_: *mut crate::leanh::LeanObject,
    mut v_inst_8094_: *mut crate::leanh::LeanObject,
    mut v_decl_8095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8096_: u8 = 0;
    let mut v_t_boxed_8097_: u8 = 0;
    let mut v_res_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8096_ = (crate::leanh::lean_unbox(v_pu_8090_) as u8);
    v_t_boxed_8097_ = (crate::leanh::lean_unbox(v_t_8091_) as u8);
    v_res_8098_ = l_Lean_Compiler_LCNF_normLetDecl(
        v_m_8089_,
        v_pu_boxed_8096_,
        v_t_boxed_8097_,
        v_inst_8092_,
        v_inst_8093_,
        v_inst_8094_,
        v_decl_8095_,
    );
    return v_res_8098_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(
    mut v_pu_8099_: u8,
    mut v_t_8100_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v_toFunctor_8122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8128_: u8 = 0;
    let mut v___f_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8144_: u8 = 0;
    let mut v_unused_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8146_: u8 = 0;
    let mut v_unused_8147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8101_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1,
                );
                v_toApplicative_8102_ = crate::leanh::lean_ctor_get(v___x_8101_, 0);
                v_toFunctor_8103_ = crate::leanh::lean_ctor_get(v_toApplicative_8102_, 0);
                v_toSeq_8104_ = crate::leanh::lean_ctor_get(v_toApplicative_8102_, 2);
                v_toSeqLeft_8105_ = crate::leanh::lean_ctor_get(v_toApplicative_8102_, 3);
                v_toSeqRight_8106_ = crate::leanh::lean_ctor_get(v_toApplicative_8102_, 4);
                v___f_8107_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2;
                v___f_8108_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_8103_, 2);
                v___f_8109_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8109_, 0, v_toFunctor_8103_);
                v___f_8110_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8110_, 0, v_toFunctor_8103_);
                v___x_8111_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8111_, 0, v___f_8109_);
                crate::leanh::lean_ctor_set(v___x_8111_, 1, v___f_8110_);
                crate::leanh::lean_inc(v_toSeqRight_8106_);
                v___f_8112_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8112_, 0, v_toSeqRight_8106_);
                crate::leanh::lean_inc(v_toSeqLeft_8105_);
                v___f_8113_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8113_, 0, v_toSeqLeft_8105_);
                crate::leanh::lean_inc(v_toSeq_8104_);
                v___f_8114_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8114_, 0, v_toSeq_8104_);
                v___x_8115_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8115_, 0, v___x_8111_);
                crate::leanh::lean_ctor_set(v___x_8115_, 1, v___f_8107_);
                crate::leanh::lean_ctor_set(v___x_8115_, 2, v___f_8114_);
                crate::leanh::lean_ctor_set(v___x_8115_, 3, v___f_8113_);
                crate::leanh::lean_ctor_set(v___x_8115_, 4, v___f_8112_);
                v___x_8116_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8116_, 0, v___x_8115_);
                crate::leanh::lean_ctor_set(v___x_8116_, 1, v___f_8108_);
                v___x_8117_ = l_StateRefT_x27_instMonad___redArg(v___x_8116_);
                v_toApplicative_8118_ = crate::leanh::lean_ctor_get(v___x_8117_, 0);
                v_isSharedCheck_8146_ = (!crate::leanh::lean_is_exclusive(v___x_8117_)) as u8;
                if v_isSharedCheck_8146_ == 0 {
                    v_unused_8147_ = crate::leanh::lean_ctor_get(v___x_8117_, 1);
                    crate::leanh::lean_dec(v_unused_8147_);
                    v___x_8120_ = v___x_8117_;
                    v_isShared_8121_ = v_isSharedCheck_8146_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_8118_);
                    crate::leanh::lean_dec(v___x_8117_);
                    v___x_8120_ = crate::leanh::lean_box(0);
                    v_isShared_8121_ = v_isSharedCheck_8146_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_8122_ = crate::leanh::lean_ctor_get(v_toApplicative_8118_, 0);
                v_toSeq_8123_ = crate::leanh::lean_ctor_get(v_toApplicative_8118_, 2);
                v_toSeqLeft_8124_ = crate::leanh::lean_ctor_get(v_toApplicative_8118_, 3);
                v_toSeqRight_8125_ = crate::leanh::lean_ctor_get(v_toApplicative_8118_, 4);
                v_isSharedCheck_8144_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_8118_)) as u8;
                if v_isSharedCheck_8144_ == 0 {
                    v_unused_8145_ = crate::leanh::lean_ctor_get(v_toApplicative_8118_, 1);
                    crate::leanh::lean_dec(v_unused_8145_);
                    v___x_8127_ = v_toApplicative_8118_;
                    v_isShared_8128_ = v_isSharedCheck_8144_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_8125_);
                    crate::leanh::lean_inc(v_toSeqLeft_8124_);
                    crate::leanh::lean_inc(v_toSeq_8123_);
                    crate::leanh::lean_inc(v_toFunctor_8122_);
                    crate::leanh::lean_dec(v_toApplicative_8118_);
                    v___x_8127_ = crate::leanh::lean_box(0);
                    v_isShared_8128_ = v_isSharedCheck_8144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_8129_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4;
                v___f_8130_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_8122_);
                v___f_8131_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8131_, 0, v_toFunctor_8122_);
                v___f_8132_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8132_, 0, v_toFunctor_8122_);
                v___x_8133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8133_, 0, v___f_8131_);
                crate::leanh::lean_ctor_set(v___x_8133_, 1, v___f_8132_);
                v___f_8134_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8134_, 0, v_toSeqRight_8125_);
                v___f_8135_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8135_, 0, v_toSeqLeft_8124_);
                v___f_8136_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8136_, 0, v_toSeq_8123_);
                if v_isShared_8128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8127_, 4, v___f_8134_);
                    crate::leanh::lean_ctor_set(v___x_8127_, 3, v___f_8135_);
                    crate::leanh::lean_ctor_set(v___x_8127_, 2, v___f_8136_);
                    crate::leanh::lean_ctor_set(v___x_8127_, 1, v___f_8129_);
                    crate::leanh::lean_ctor_set(v___x_8127_, 0, v___x_8133_);
                    v___x_8138_ = v___x_8127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8143_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 0, v___x_8133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 1, v___f_8129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 2, v___f_8136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 3, v___f_8135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 4, v___f_8134_);
                    v___x_8138_ = v_reuseFailAlloc_8143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8120_, 1, v___f_8130_);
                    crate::leanh::lean_ctor_set(v___x_8120_, 0, v___x_8138_);
                    v___x_8140_ = v___x_8120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8142_, 0, v___x_8138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8142_, 1, v___f_8130_);
                    v___x_8140_ = v_reuseFailAlloc_8142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8141_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_read___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_8141_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_8141_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_8141_, 2, v___x_8140_);
                return v___x_8141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(
    mut v_pu_8148_: *mut crate::leanh::LeanObject,
    mut v_t_8149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8150_: u8 = 0;
    let mut v_t_boxed_8151_: u8 = 0;
    let mut v_res_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8150_ = (crate::leanh::lean_unbox(v_pu_8148_) as u8);
    v_t_boxed_8151_ = (crate::leanh::lean_unbox(v_t_8149_) as u8);
    v_res_8152_ =
        l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_8150_, v_t_boxed_8151_);
    return v_res_8152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___redArg(
    mut v_pu_8153_: u8,
    mut v_inst_8154_: *mut crate::leanh::LeanObject,
    mut v_result_8155_: *mut crate::leanh::LeanObject,
    mut v_x_8156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_result_8155_) == 0 {
        let mut v_fvarId_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_8154_);
        v_fvarId_8157_ = crate::leanh::lean_ctor_get(v_result_8155_, 0);
        crate::leanh::lean_inc(v_fvarId_8157_);
        crate::leanh::lean_dec_ref_known(v_result_8155_, 1);
        v___x_8158_ = crate::leanh::lean_apply_1(v_x_8156_, v_fvarId_8157_);
        return v___x_8158_;
    } else {
        let mut v___x_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_8156_);
        v___x_8159_ = crate::leanh::lean_box((v_pu_8153_) as usize);
        v___x_8160_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_mkReturnErased___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        crate::leanh::lean_closure_set(v___x_8160_, 0, v___x_8159_);
        v___x_8161_ =
            crate::leanh::lean_apply_2(v_inst_8154_, crate::leanh::lean_box(0), v___x_8160_);
        return v___x_8161_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(
    mut v_pu_8162_: *mut crate::leanh::LeanObject,
    mut v_inst_8163_: *mut crate::leanh::LeanObject,
    mut v_result_8164_: *mut crate::leanh::LeanObject,
    mut v_x_8165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8166_: u8 = 0;
    let mut v_res_8167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8166_ = (crate::leanh::lean_unbox(v_pu_8162_) as u8);
    v_res_8167_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(
        v_pu_boxed_8166_,
        v_inst_8163_,
        v_result_8164_,
        v_x_8165_,
    );
    return v_res_8167_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult(
    mut v_m_8168_: *mut crate::leanh::LeanObject,
    mut v_pu_8169_: u8,
    mut v_inst_8170_: *mut crate::leanh::LeanObject,
    mut v_inst_8171_: *mut crate::leanh::LeanObject,
    mut v_result_8172_: *mut crate::leanh::LeanObject,
    mut v_x_8173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_result_8172_) == 0 {
        let mut v_fvarId_8174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_8170_);
        v_fvarId_8174_ = crate::leanh::lean_ctor_get(v_result_8172_, 0);
        crate::leanh::lean_inc(v_fvarId_8174_);
        crate::leanh::lean_dec_ref_known(v_result_8172_, 1);
        v___x_8175_ = crate::leanh::lean_apply_1(v_x_8173_, v_fvarId_8174_);
        return v___x_8175_;
    } else {
        let mut v___x_8176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_8173_);
        v___x_8176_ = crate::leanh::lean_box((v_pu_8169_) as usize);
        v___x_8177_ = crate::leanh::lean_alloc_closure(
            l_Lean_Compiler_LCNF_mkReturnErased___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        crate::leanh::lean_closure_set(v___x_8177_, 0, v___x_8176_);
        v___x_8178_ =
            crate::leanh::lean_apply_2(v_inst_8170_, crate::leanh::lean_box(0), v___x_8177_);
        return v___x_8178_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___boxed(
    mut v_m_8179_: *mut crate::leanh::LeanObject,
    mut v_pu_8180_: *mut crate::leanh::LeanObject,
    mut v_inst_8181_: *mut crate::leanh::LeanObject,
    mut v_inst_8182_: *mut crate::leanh::LeanObject,
    mut v_result_8183_: *mut crate::leanh::LeanObject,
    mut v_x_8184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8185_: u8 = 0;
    let mut v_res_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8185_ = (crate::leanh::lean_unbox(v_pu_8180_) as u8);
    v_res_8186_ = l_Lean_Compiler_LCNF_withNormFVarResult(
        v_m_8179_,
        v_pu_boxed_8185_,
        v_inst_8181_,
        v_inst_8182_,
        v_result_8183_,
        v_x_8184_,
    );
    crate::leanh::lean_dec_ref(v_inst_8182_);
    return v_res_8186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(
    mut v_pu_8187_: u8,
    mut v_t_8188_: u8,
    mut v_args_8189_: *mut crate::leanh::LeanObject,
    mut v___y_8190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8192_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_8187_,
        v___y_8190_,
        v_args_8189_,
        v_t_8188_,
    );
    v___x_8193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8193_, 0, v___x_8192_);
    return v___x_8193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(
    mut v_pu_8194_: *mut crate::leanh::LeanObject,
    mut v_t_8195_: *mut crate::leanh::LeanObject,
    mut v_args_8196_: *mut crate::leanh::LeanObject,
    mut v___y_8197_: *mut crate::leanh::LeanObject,
    mut v___y_8198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8199_: u8 = 0;
    let mut v_t_boxed_8200_: u8 = 0;
    let mut v_res_8201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8199_ = (crate::leanh::lean_unbox(v_pu_8194_) as u8);
    v_t_boxed_8200_ = (crate::leanh::lean_unbox(v_t_8195_) as u8);
    v_res_8201_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(
            v_pu_boxed_8199_,
            v_t_boxed_8200_,
            v_args_8196_,
            v___y_8197_,
        );
    crate::leanh::lean_dec_ref(v___y_8197_);
    return v_res_8201_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(
    mut v_pu_8202_: u8,
    mut v_t_8203_: u8,
    mut v_i_8204_: *mut crate::leanh::LeanObject,
    mut v_as_8205_: *mut crate::leanh::LeanObject,
    mut v___y_8206_: *mut crate::leanh::LeanObject,
    mut v___y_8207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: u8 = 0;
    let mut v___x_8211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: usize = 0;
    let mut v___x_8218_: usize = 0;
    let mut v___x_8219_: u8 = 0;
    let mut v___x_8220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8230_: u8 = 0;
    let mut v___x_8232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8209_ = lean_array_get_size(v_as_8205_);
                v___x_8210_ = lean_nat_dec_lt(v_i_8204_, v___x_8209_);
                if v___x_8210_ == 0 {
                    crate::leanh::lean_dec(v_i_8204_);
                    v___x_8211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8211_, 0, v_as_8205_);
                    return v___x_8211_;
                } else {
                    v_a_8212_ = lean_array_fget_borrowed(v_as_8205_, v_i_8204_);
                    v_type_8213_ = crate::leanh::lean_ctor_get(v_a_8212_, 2);
                    crate::leanh::lean_inc_ref(v_type_8213_);
                    v___x_8214_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8202_, v___y_8206_, v_t_8203_, v_type_8213_);
                    crate::leanh::lean_inc(v_a_8212_);
                    v___x_8215_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_8202_, v_a_8212_, v___x_8214_, v___y_8207_);
                    if crate::leanh::lean_obj_tag(v___x_8215_) == 0 {
                        v_a_8216_ = crate::leanh::lean_ctor_get(v___x_8215_, 0);
                        crate::leanh::lean_inc(v_a_8216_);
                        crate::leanh::lean_dec_ref_known(v___x_8215_, 1);
                        v___x_8217_ = lean_ptr_addr(v_a_8212_);
                        v___x_8218_ = lean_ptr_addr(v_a_8216_);
                        v___x_8219_ = lean_usize_dec_eq(v___x_8217_, v___x_8218_);
                        if v___x_8219_ == 0 {
                            v___x_8220_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_8221_ = lean_nat_add(v_i_8204_, v___x_8220_);
                            v___x_8222_ = lean_array_fset(v_as_8205_, v_i_8204_, v_a_8216_);
                            crate::leanh::lean_dec(v_i_8204_);
                            v_i_8204_ = v___x_8221_;
                            v_as_8205_ = v___x_8222_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_8216_);
                            v___x_8224_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_8225_ = lean_nat_add(v_i_8204_, v___x_8224_);
                            crate::leanh::lean_dec(v_i_8204_);
                            v_i_8204_ = v___x_8225_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_8205_);
                        crate::leanh::lean_dec(v_i_8204_);
                        v_a_8227_ = crate::leanh::lean_ctor_get(v___x_8215_, 0);
                        v_isSharedCheck_8234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8215_)) as u8;
                        if v_isSharedCheck_8234_ == 0 {
                            v___x_8229_ = v___x_8215_;
                            v_isShared_8230_ = v_isSharedCheck_8234_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8227_);
                            crate::leanh::lean_dec(v___x_8215_);
                            v___x_8229_ = crate::leanh::lean_box(0);
                            v_isShared_8230_ = v_isSharedCheck_8234_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8230_ == 0 {
                    v___x_8232_ = v___x_8229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8233_, 0, v_a_8227_);
                    v___x_8232_ = v_reuseFailAlloc_8233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg___boxed(
    mut v_pu_8235_: *mut crate::leanh::LeanObject,
    mut v_t_8236_: *mut crate::leanh::LeanObject,
    mut v_i_8237_: *mut crate::leanh::LeanObject,
    mut v_as_8238_: *mut crate::leanh::LeanObject,
    mut v___y_8239_: *mut crate::leanh::LeanObject,
    mut v___y_8240_: *mut crate::leanh::LeanObject,
    mut v___y_8241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8242_: u8 = 0;
    let mut v_t_boxed_8243_: u8 = 0;
    let mut v_res_8244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8242_ = (crate::leanh::lean_unbox(v_pu_8235_) as u8);
    v_t_boxed_8243_ = (crate::leanh::lean_unbox(v_t_8236_) as u8);
    v_res_8244_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_8242_, v_t_boxed_8243_, v_i_8237_, v_as_8238_, v___y_8239_, v___y_8240_);
    crate::leanh::lean_dec(v___y_8240_);
    crate::leanh::lean_dec_ref(v___y_8239_);
    return v_res_8244_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(
    mut v_pu_8245_: u8,
    mut v_t_8246_: u8,
    mut v_ps_8247_: *mut crate::leanh::LeanObject,
    mut v___y_8248_: *mut crate::leanh::LeanObject,
    mut v___y_8249_: *mut crate::leanh::LeanObject,
    mut v___y_8250_: *mut crate::leanh::LeanObject,
    mut v___y_8251_: *mut crate::leanh::LeanObject,
    mut v___y_8252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8254_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_8255_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_8245_, v_t_8246_, v___x_8254_, v_ps_8247_, v___y_8248_, v___y_8250_);
    return v___x_8255_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(
    mut v_pu_8256_: *mut crate::leanh::LeanObject,
    mut v_t_8257_: *mut crate::leanh::LeanObject,
    mut v_ps_8258_: *mut crate::leanh::LeanObject,
    mut v___y_8259_: *mut crate::leanh::LeanObject,
    mut v___y_8260_: *mut crate::leanh::LeanObject,
    mut v___y_8261_: *mut crate::leanh::LeanObject,
    mut v___y_8262_: *mut crate::leanh::LeanObject,
    mut v___y_8263_: *mut crate::leanh::LeanObject,
    mut v___y_8264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8265_: u8 = 0;
    let mut v_t_boxed_8266_: u8 = 0;
    let mut v_res_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8265_ = (crate::leanh::lean_unbox(v_pu_8256_) as u8);
    v_t_boxed_8266_ = (crate::leanh::lean_unbox(v_t_8257_) as u8);
    v_res_8267_ =
        l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(
            v_pu_boxed_8265_,
            v_t_boxed_8266_,
            v_ps_8258_,
            v___y_8259_,
            v___y_8260_,
            v___y_8261_,
            v___y_8262_,
            v___y_8263_,
        );
    crate::leanh::lean_dec(v___y_8263_);
    crate::leanh::lean_dec_ref(v___y_8262_);
    crate::leanh::lean_dec(v___y_8261_);
    crate::leanh::lean_dec_ref(v___y_8260_);
    crate::leanh::lean_dec_ref(v___y_8259_);
    return v_res_8267_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(
    mut v_pu_8268_: u8,
    mut v_t_8269_: u8,
    mut v_decl_8270_: *mut crate::leanh::LeanObject,
    mut v___y_8271_: *mut crate::leanh::LeanObject,
    mut v___y_8272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_8274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_8274_ = crate::leanh::lean_ctor_get(v_decl_8270_, 2);
    v_value_8275_ = crate::leanh::lean_ctor_get(v_decl_8270_, 3);
    crate::leanh::lean_inc_ref(v_type_8274_);
    v___x_8276_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_8268_,
        v___y_8271_,
        v_t_8269_,
        v_type_8274_,
    );
    crate::leanh::lean_inc(v_value_8275_);
    v___x_8277_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_8268_,
        v___y_8271_,
        v_value_8275_,
        v_t_8269_,
    );
    v___x_8278_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_8268_,
            v_decl_8270_,
            v___x_8276_,
            v___x_8277_,
            v___y_8272_,
        );
    return v___x_8278_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg___boxed(
    mut v_pu_8279_: *mut crate::leanh::LeanObject,
    mut v_t_8280_: *mut crate::leanh::LeanObject,
    mut v_decl_8281_: *mut crate::leanh::LeanObject,
    mut v___y_8282_: *mut crate::leanh::LeanObject,
    mut v___y_8283_: *mut crate::leanh::LeanObject,
    mut v___y_8284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8285_: u8 = 0;
    let mut v_t_boxed_8286_: u8 = 0;
    let mut v_res_8287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8285_ = (crate::leanh::lean_unbox(v_pu_8279_) as u8);
    v_t_boxed_8286_ = (crate::leanh::lean_unbox(v_t_8280_) as u8);
    v_res_8287_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(
            v_pu_boxed_8285_,
            v_t_boxed_8286_,
            v_decl_8281_,
            v___y_8282_,
            v___y_8283_,
        );
    crate::leanh::lean_dec(v___y_8283_);
    crate::leanh::lean_dec_ref(v___y_8282_);
    return v_res_8287_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(
    mut v_pu_8288_: u8,
    mut v_t_8289_: u8,
    mut v_i_8290_: *mut crate::leanh::LeanObject,
    mut v_as_8291_: *mut crate::leanh::LeanObject,
    mut v___y_8292_: *mut crate::leanh::LeanObject,
    mut v___y_8293_: *mut crate::leanh::LeanObject,
    mut v___y_8294_: *mut crate::leanh::LeanObject,
    mut v___y_8295_: *mut crate::leanh::LeanObject,
    mut v___y_8296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: u8 = 0;
    let mut v___x_8300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: usize = 0;
    let mut v___x_8305_: usize = 0;
    let mut v___x_8306_: u8 = 0;
    let mut v___x_8307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_8314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_8315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8324_: u8 = 0;
    let mut v___x_8326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8328_: u8 = 0;
    let mut v_a_8329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8332_: u8 = 0;
    let mut v___x_8334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8336_: u8 = 0;
    let mut v_code_8337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8344_: u8 = 0;
    let mut v___x_8346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8348_: u8 = 0;
    let mut v_code_8349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8356_: u8 = 0;
    let mut v___x_8358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8298_ = lean_array_get_size(v_as_8291_);
                v___x_8299_ = lean_nat_dec_lt(v_i_8290_, v___x_8298_);
                if v___x_8299_ == 0 {
                    crate::leanh::lean_dec(v_i_8290_);
                    v___x_8300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8300_, 0, v_as_8291_);
                    return v___x_8300_;
                } else {
                    v_a_8301_ = lean_array_fget_borrowed(v_as_8291_, v_i_8290_);
                    match crate::leanh::lean_obj_tag(v_a_8301_) {
                        0 => {
                            v_params_8314_ = crate::leanh::lean_ctor_get(v_a_8301_, 1);
                            v_code_8315_ = crate::leanh::lean_ctor_get(v_a_8301_, 2);
                            crate::leanh::lean_inc_ref(v_params_8314_);
                            v___x_8316_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_8288_, v_t_8289_, v_params_8314_, v___y_8292_, v___y_8293_, v___y_8294_, v___y_8295_, v___y_8296_);
                            if crate::leanh::lean_obj_tag(v___x_8316_) == 0 {
                                v_a_8317_ = crate::leanh::lean_ctor_get(v___x_8316_, 0);
                                crate::leanh::lean_inc(v_a_8317_);
                                crate::leanh::lean_dec_ref_known(v___x_8316_, 1);
                                crate::leanh::lean_inc_ref(v_code_8315_);
                                v___x_8318_ = l_Lean_Compiler_LCNF_normCodeImp(
                                    v_pu_8288_,
                                    v_t_8289_,
                                    v_code_8315_,
                                    v___y_8292_,
                                    v___y_8293_,
                                    v___y_8294_,
                                    v___y_8295_,
                                    v___y_8296_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_8318_) == 0 {
                                    v_a_8319_ = crate::leanh::lean_ctor_get(v___x_8318_, 0);
                                    crate::leanh::lean_inc(v_a_8319_);
                                    crate::leanh::lean_dec_ref_known(v___x_8318_, 1);
                                    crate::leanh::lean_inc_ref(v_a_8301_);
                                    v___x_8320_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_8288_, v_a_8301_, v_a_8317_, v_a_8319_);
                                    v_a_8303_ = v___x_8320_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_8317_);
                                    crate::leanh::lean_dec_ref(v_as_8291_);
                                    crate::leanh::lean_dec(v_i_8290_);
                                    v_a_8321_ = crate::leanh::lean_ctor_get(v___x_8318_, 0);
                                    v_isSharedCheck_8328_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_8318_)) as u8;
                                    if v_isSharedCheck_8328_ == 0 {
                                        v___x_8323_ = v___x_8318_;
                                        v_isShared_8324_ = v_isSharedCheck_8328_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_8321_);
                                        crate::leanh::lean_dec(v___x_8318_);
                                        v___x_8323_ = crate::leanh::lean_box(0);
                                        v_isShared_8324_ = v_isSharedCheck_8328_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_as_8291_);
                                crate::leanh::lean_dec(v_i_8290_);
                                v_a_8329_ = crate::leanh::lean_ctor_get(v___x_8316_, 0);
                                v_isSharedCheck_8336_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8316_)) as u8;
                                if v_isSharedCheck_8336_ == 0 {
                                    v___x_8331_ = v___x_8316_;
                                    v_isShared_8332_ = v_isSharedCheck_8336_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8329_);
                                    crate::leanh::lean_dec(v___x_8316_);
                                    v___x_8331_ = crate::leanh::lean_box(0);
                                    v_isShared_8332_ = v_isSharedCheck_8336_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_code_8337_ = crate::leanh::lean_ctor_get(v_a_8301_, 1);
                            crate::leanh::lean_inc_ref(v_code_8337_);
                            v___x_8338_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8288_,
                                v_t_8289_,
                                v_code_8337_,
                                v___y_8292_,
                                v___y_8293_,
                                v___y_8294_,
                                v___y_8295_,
                                v___y_8296_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_8338_) == 0 {
                                v_a_8339_ = crate::leanh::lean_ctor_get(v___x_8338_, 0);
                                crate::leanh::lean_inc(v_a_8339_);
                                crate::leanh::lean_dec_ref_known(v___x_8338_, 1);
                                crate::leanh::lean_inc_ref(v_a_8301_);
                                v___x_8340_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_8301_, v_a_8339_);
                                v_a_8303_ = v___x_8340_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_as_8291_);
                                crate::leanh::lean_dec(v_i_8290_);
                                v_a_8341_ = crate::leanh::lean_ctor_get(v___x_8338_, 0);
                                v_isSharedCheck_8348_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8338_)) as u8;
                                if v_isSharedCheck_8348_ == 0 {
                                    v___x_8343_ = v___x_8338_;
                                    v_isShared_8344_ = v_isSharedCheck_8348_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8341_);
                                    crate::leanh::lean_dec(v___x_8338_);
                                    v___x_8343_ = crate::leanh::lean_box(0);
                                    v_isShared_8344_ = v_isSharedCheck_8348_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_code_8349_ = crate::leanh::lean_ctor_get(v_a_8301_, 0);
                            crate::leanh::lean_inc_ref(v_code_8349_);
                            v___x_8350_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8288_,
                                v_t_8289_,
                                v_code_8349_,
                                v___y_8292_,
                                v___y_8293_,
                                v___y_8294_,
                                v___y_8295_,
                                v___y_8296_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_8350_) == 0 {
                                v_a_8351_ = crate::leanh::lean_ctor_get(v___x_8350_, 0);
                                crate::leanh::lean_inc(v_a_8351_);
                                crate::leanh::lean_dec_ref_known(v___x_8350_, 1);
                                crate::leanh::lean_inc_ref(v_a_8301_);
                                v___x_8352_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_8301_, v_a_8351_);
                                v_a_8303_ = v___x_8352_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_as_8291_);
                                crate::leanh::lean_dec(v_i_8290_);
                                v_a_8353_ = crate::leanh::lean_ctor_get(v___x_8350_, 0);
                                v_isSharedCheck_8360_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8350_)) as u8;
                                if v_isSharedCheck_8360_ == 0 {
                                    v___x_8355_ = v___x_8350_;
                                    v_isShared_8356_ = v_isSharedCheck_8360_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8353_);
                                    crate::leanh::lean_dec(v___x_8350_);
                                    v___x_8355_ = crate::leanh::lean_box(0);
                                    v_isShared_8356_ = v_isSharedCheck_8360_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_8304_ = lean_ptr_addr(v_a_8301_);
                v___x_8305_ = lean_ptr_addr(v_a_8303_);
                v___x_8306_ = lean_usize_dec_eq(v___x_8304_, v___x_8305_);
                if v___x_8306_ == 0 {
                    v___x_8307_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8308_ = lean_nat_add(v_i_8290_, v___x_8307_);
                    v___x_8309_ = lean_array_fset(v_as_8291_, v_i_8290_, v_a_8303_);
                    crate::leanh::lean_dec(v_i_8290_);
                    v_i_8290_ = v___x_8308_;
                    v_as_8291_ = v___x_8309_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_8303_);
                    v___x_8311_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8312_ = lean_nat_add(v_i_8290_, v___x_8311_);
                    crate::leanh::lean_dec(v_i_8290_);
                    v_i_8290_ = v___x_8312_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_8324_ == 0 {
                    v___x_8326_ = v___x_8323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8327_, 0, v_a_8321_);
                    v___x_8326_ = v_reuseFailAlloc_8327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8326_;
            }
            4 => {
                if v_isShared_8332_ == 0 {
                    v___x_8334_ = v___x_8331_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8335_, 0, v_a_8329_);
                    v___x_8334_ = v_reuseFailAlloc_8335_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8334_;
            }
            6 => {
                if v_isShared_8344_ == 0 {
                    v___x_8346_ = v___x_8343_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8347_, 0, v_a_8341_);
                    v___x_8346_ = v_reuseFailAlloc_8347_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8346_;
            }
            8 => {
                if v_isShared_8356_ == 0 {
                    v___x_8358_ = v___x_8355_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8359_, 0, v_a_8353_);
                    v___x_8358_ = v_reuseFailAlloc_8359_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normCodeImp(
    mut v_pu_8361_: u8,
    mut v_t_8362_: u8,
    mut v_code_8363_: *mut crate::leanh::LeanObject,
    mut v_a_8364_: *mut crate::leanh::LeanObject,
    mut v_a_8365_: *mut crate::leanh::LeanObject,
    mut v_a_8366_: *mut crate::leanh::LeanObject,
    mut v_a_8367_: *mut crate::leanh::LeanObject,
    mut v_a_8368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_8370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8378_: u8 = 0;
    let mut v___y_8380_: u8 = 0;
    let mut v___x_8382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8383_: u8 = 0;
    let mut v___x_8385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8390_: u8 = 0;
    let mut v_unused_8391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: usize = 0;
    let mut v___x_8397_: usize = 0;
    let mut v___x_8398_: u8 = 0;
    let mut v___x_8399_: usize = 0;
    let mut v___x_8400_: usize = 0;
    let mut v___x_8401_: u8 = 0;
    let mut v_isSharedCheck_8402_: u8 = 0;
    let mut v_a_8403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8406_: u8 = 0;
    let mut v___x_8408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8410_: u8 = 0;
    let mut v_decl_8411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8419_: u8 = 0;
    let mut v___y_8421_: u8 = 0;
    let mut v___x_8423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8424_: u8 = 0;
    let mut v___x_8426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8431_: u8 = 0;
    let mut v_unused_8432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: usize = 0;
    let mut v___x_8438_: usize = 0;
    let mut v___x_8439_: u8 = 0;
    let mut v___x_8440_: usize = 0;
    let mut v___x_8441_: usize = 0;
    let mut v___x_8442_: u8 = 0;
    let mut v_isSharedCheck_8443_: u8 = 0;
    let mut v_a_8444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8447_: u8 = 0;
    let mut v___x_8449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8451_: u8 = 0;
    let mut v_decl_8452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8460_: u8 = 0;
    let mut v___y_8462_: u8 = 0;
    let mut v___x_8464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8465_: u8 = 0;
    let mut v___x_8467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8472_: u8 = 0;
    let mut v_unused_8473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: usize = 0;
    let mut v___x_8479_: usize = 0;
    let mut v___x_8480_: u8 = 0;
    let mut v___x_8481_: usize = 0;
    let mut v___x_8482_: usize = 0;
    let mut v___x_8483_: u8 = 0;
    let mut v_isSharedCheck_8484_: u8 = 0;
    let mut v_a_8485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8488_: u8 = 0;
    let mut v___x_8490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8492_: u8 = 0;
    let mut v_fvarId_8493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_8494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8501_: u8 = 0;
    let mut v___y_8503_: u8 = 0;
    let mut v___x_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8506_: u8 = 0;
    let mut v___x_8508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8513_: u8 = 0;
    let mut v_unused_8514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8519_: u8 = 0;
    let mut v___x_8520_: usize = 0;
    let mut v___x_8521_: usize = 0;
    let mut v___x_8522_: u8 = 0;
    let mut v_isSharedCheck_8523_: u8 = 0;
    let mut v_a_8524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8527_: u8 = 0;
    let mut v___x_8529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8531_: u8 = 0;
    let mut v___x_8532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_8533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_8534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_8535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_8536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_8537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8540_: u8 = 0;
    let mut v___x_8541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8546_: u8 = 0;
    let mut v___x_8547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8552_: u8 = 0;
    let mut v___x_8555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8564_: u8 = 0;
    let mut v___x_8565_: u8 = 0;
    let mut v___x_8566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: usize = 0;
    let mut v___x_8568_: usize = 0;
    let mut v___x_8569_: u8 = 0;
    let mut v___x_8570_: usize = 0;
    let mut v___x_8571_: usize = 0;
    let mut v___x_8572_: u8 = 0;
    let mut v_isSharedCheck_8573_: u8 = 0;
    let mut v_a_8574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8577_: u8 = 0;
    let mut v___x_8579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8581_: u8 = 0;
    let mut v_isSharedCheck_8582_: u8 = 0;
    let mut v___x_8583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8584_: u8 = 0;
    let mut v_fvarId_8585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8590_: u8 = 0;
    let mut v___x_8591_: u8 = 0;
    let mut v___x_8593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8594_: u8 = 0;
    let mut v___x_8596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8601_: u8 = 0;
    let mut v_unused_8602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8606_: u8 = 0;
    let mut v___x_8607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8610_: usize = 0;
    let mut v___x_8611_: usize = 0;
    let mut v___x_8612_: u8 = 0;
    let mut v___x_8614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8615_: u8 = 0;
    let mut v___x_8617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8620_: u8 = 0;
    let mut v_unused_8621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_8624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_8625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8634_: u8 = 0;
    let mut v___y_8636_: u8 = 0;
    let mut v___x_8638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8639_: u8 = 0;
    let mut v___x_8641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8646_: u8 = 0;
    let mut v_unused_8647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: usize = 0;
    let mut v___x_8652_: usize = 0;
    let mut v___x_8653_: u8 = 0;
    let mut v___x_8655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8656_: u8 = 0;
    let mut v___x_8658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8663_: u8 = 0;
    let mut v_unused_8664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8668_: usize = 0;
    let mut v___x_8669_: usize = 0;
    let mut v___x_8670_: u8 = 0;
    let mut v___x_8672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8673_: u8 = 0;
    let mut v___x_8675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8680_: u8 = 0;
    let mut v_unused_8681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8688_: usize = 0;
    let mut v___x_8689_: usize = 0;
    let mut v___x_8690_: u8 = 0;
    let mut v___x_8691_: u8 = 0;
    let mut v_isSharedCheck_8692_: u8 = 0;
    let mut v___x_8693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_8695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_8696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8706_: u8 = 0;
    let mut v___y_8708_: u8 = 0;
    let mut v___x_8710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8711_: u8 = 0;
    let mut v___x_8713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8718_: u8 = 0;
    let mut v_unused_8719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: usize = 0;
    let mut v___x_8724_: usize = 0;
    let mut v___x_8725_: u8 = 0;
    let mut v___x_8727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8728_: u8 = 0;
    let mut v___x_8730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8735_: u8 = 0;
    let mut v_unused_8736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8740_: usize = 0;
    let mut v___x_8741_: usize = 0;
    let mut v___x_8742_: u8 = 0;
    let mut v___x_8744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8745_: u8 = 0;
    let mut v___x_8747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8752_: u8 = 0;
    let mut v_unused_8753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: usize = 0;
    let mut v___x_8761_: usize = 0;
    let mut v___x_8762_: u8 = 0;
    let mut v___x_8763_: u8 = 0;
    let mut v_isSharedCheck_8764_: u8 = 0;
    let mut v___x_8765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_8768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_8769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_8770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_8771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8782_: u8 = 0;
    let mut v___y_8784_: u8 = 0;
    let mut v___x_8786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8787_: u8 = 0;
    let mut v___x_8789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8794_: u8 = 0;
    let mut v_unused_8795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8801_: u8 = 0;
    let mut v___x_8803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8804_: u8 = 0;
    let mut v___x_8806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8811_: u8 = 0;
    let mut v_unused_8812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8818_: usize = 0;
    let mut v___x_8819_: usize = 0;
    let mut v___x_8820_: u8 = 0;
    let mut v___x_8822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8823_: u8 = 0;
    let mut v___x_8825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8830_: u8 = 0;
    let mut v_unused_8831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: usize = 0;
    let mut v___x_8838_: usize = 0;
    let mut v___x_8839_: u8 = 0;
    let mut v___x_8841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8842_: u8 = 0;
    let mut v___x_8844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8849_: u8 = 0;
    let mut v_unused_8850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8856_: usize = 0;
    let mut v___x_8857_: usize = 0;
    let mut v___x_8858_: u8 = 0;
    let mut v___x_8860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8861_: u8 = 0;
    let mut v___x_8863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8868_: u8 = 0;
    let mut v_unused_8869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: usize = 0;
    let mut v___x_8879_: usize = 0;
    let mut v___x_8880_: u8 = 0;
    let mut v___x_8881_: u8 = 0;
    let mut v_isSharedCheck_8882_: u8 = 0;
    let mut v___x_8883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_8886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8894_: u8 = 0;
    let mut v___y_8896_: u8 = 0;
    let mut v___x_8898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8899_: u8 = 0;
    let mut v___x_8901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8906_: u8 = 0;
    let mut v_unused_8907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8910_: usize = 0;
    let mut v___x_8911_: usize = 0;
    let mut v___x_8912_: u8 = 0;
    let mut v___x_8914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8915_: u8 = 0;
    let mut v___x_8917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8922_: u8 = 0;
    let mut v_unused_8923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8929_: usize = 0;
    let mut v___x_8930_: usize = 0;
    let mut v___x_8931_: u8 = 0;
    let mut v___x_8932_: u8 = 0;
    let mut v_isSharedCheck_8933_: u8 = 0;
    let mut v___x_8934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_8936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_8937_: u8 = 0;
    let mut v_persistent_8938_: u8 = 0;
    let mut v_k_8939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8946_: u8 = 0;
    let mut v___y_8948_: u8 = 0;
    let mut v___x_8950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8951_: u8 = 0;
    let mut v___x_8953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8958_: u8 = 0;
    let mut v_unused_8959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: usize = 0;
    let mut v___x_8963_: usize = 0;
    let mut v___x_8964_: u8 = 0;
    let mut v___x_8966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8967_: u8 = 0;
    let mut v___x_8969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8974_: u8 = 0;
    let mut v_unused_8975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8981_: usize = 0;
    let mut v___x_8982_: usize = 0;
    let mut v___x_8983_: u8 = 0;
    let mut v___x_8984_: u8 = 0;
    let mut v_isSharedCheck_8985_: u8 = 0;
    let mut v___x_8986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_8988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_8989_: u8 = 0;
    let mut v_persistent_8990_: u8 = 0;
    let mut v_objs_x3f_8991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_8992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8999_: u8 = 0;
    let mut v___y_9001_: u8 = 0;
    let mut v___x_9003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9004_: u8 = 0;
    let mut v___x_9006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9011_: u8 = 0;
    let mut v_unused_9012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9016_: usize = 0;
    let mut v___x_9017_: u8 = 0;
    let mut v___x_9019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9020_: u8 = 0;
    let mut v___x_9022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9027_: u8 = 0;
    let mut v_unused_9028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9032_: usize = 0;
    let mut v___x_9033_: usize = 0;
    let mut v___x_9034_: u8 = 0;
    let mut v___x_9036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9037_: u8 = 0;
    let mut v___x_9039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9044_: u8 = 0;
    let mut v_unused_9045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9052_: usize = 0;
    let mut v___x_9053_: usize = 0;
    let mut v___x_9054_: u8 = 0;
    let mut v___x_9055_: u8 = 0;
    let mut v_isSharedCheck_9056_: u8 = 0;
    let mut v___x_9057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_9058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_9059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_9061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9066_: u8 = 0;
    let mut v___y_9068_: u8 = 0;
    let mut v___x_9070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9071_: u8 = 0;
    let mut v___x_9073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9078_: u8 = 0;
    let mut v_unused_9079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_9080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9084_: usize = 0;
    let mut v___x_9085_: usize = 0;
    let mut v___x_9086_: u8 = 0;
    let mut v___x_9087_: usize = 0;
    let mut v___x_9088_: usize = 0;
    let mut v___x_9089_: u8 = 0;
    let mut v_isSharedCheck_9090_: u8 = 0;
    let mut v___x_9091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_8363_) {
                0 => {
                    v_decl_8370_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_k_8371_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    crate::leanh::lean_inc_ref(v_decl_8370_);
                    v___x_8372_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_8361_, v_t_8362_, v_decl_8370_, v_a_8364_, v_a_8366_);
                    if crate::leanh::lean_obj_tag(v___x_8372_) == 0 {
                        v_a_8373_ = crate::leanh::lean_ctor_get(v___x_8372_, 0);
                        crate::leanh::lean_inc(v_a_8373_);
                        crate::leanh::lean_dec_ref_known(v___x_8372_, 1);
                        crate::leanh::lean_inc_ref(v_k_8371_);
                        v___x_8374_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8371_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8374_) == 0 {
                            v_a_8375_ = crate::leanh::lean_ctor_get(v___x_8374_, 0);
                            v_isSharedCheck_8402_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8374_)) as u8;
                            if v_isSharedCheck_8402_ == 0 {
                                v___x_8377_ = v___x_8374_;
                                v_isShared_8378_ = v_isSharedCheck_8402_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8375_);
                                crate::leanh::lean_dec(v___x_8374_);
                                v___x_8377_ = crate::leanh::lean_box(0);
                                v_isShared_8378_ = v_isSharedCheck_8402_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8373_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8374_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8403_ = crate::leanh::lean_ctor_get(v___x_8372_, 0);
                        v_isSharedCheck_8410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8372_)) as u8;
                        if v_isSharedCheck_8410_ == 0 {
                            v___x_8405_ = v___x_8372_;
                            v_isShared_8406_ = v_isSharedCheck_8410_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8403_);
                            crate::leanh::lean_dec(v___x_8372_);
                            v___x_8405_ = crate::leanh::lean_box(0);
                            v_isShared_8406_ = v_isSharedCheck_8410_;
                            state = 7;
                            continue;
                        }
                    }
                }
                1 => {
                    v_decl_8411_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_k_8412_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    crate::leanh::lean_inc_ref(v_decl_8411_);
                    v___x_8413_ = l_Lean_Compiler_LCNF_normFunDeclImp(
                        v_pu_8361_,
                        v_t_8362_,
                        v_decl_8411_,
                        v_a_8364_,
                        v_a_8365_,
                        v_a_8366_,
                        v_a_8367_,
                        v_a_8368_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8413_) == 0 {
                        v_a_8414_ = crate::leanh::lean_ctor_get(v___x_8413_, 0);
                        crate::leanh::lean_inc(v_a_8414_);
                        crate::leanh::lean_dec_ref_known(v___x_8413_, 1);
                        crate::leanh::lean_inc_ref(v_k_8412_);
                        v___x_8415_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8412_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8415_) == 0 {
                            v_a_8416_ = crate::leanh::lean_ctor_get(v___x_8415_, 0);
                            v_isSharedCheck_8443_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8415_)) as u8;
                            if v_isSharedCheck_8443_ == 0 {
                                v___x_8418_ = v___x_8415_;
                                v_isShared_8419_ = v_isSharedCheck_8443_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8416_);
                                crate::leanh::lean_dec(v___x_8415_);
                                v___x_8418_ = crate::leanh::lean_box(0);
                                v_isShared_8419_ = v_isSharedCheck_8443_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8414_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8415_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8444_ = crate::leanh::lean_ctor_get(v___x_8413_, 0);
                        v_isSharedCheck_8451_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8413_)) as u8;
                        if v_isSharedCheck_8451_ == 0 {
                            v___x_8446_ = v___x_8413_;
                            v_isShared_8447_ = v_isSharedCheck_8451_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8444_);
                            crate::leanh::lean_dec(v___x_8413_);
                            v___x_8446_ = crate::leanh::lean_box(0);
                            v_isShared_8447_ = v_isSharedCheck_8451_;
                            state = 15;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_8452_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_k_8453_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    crate::leanh::lean_inc_ref(v_decl_8452_);
                    v___x_8454_ = l_Lean_Compiler_LCNF_normFunDeclImp(
                        v_pu_8361_,
                        v_t_8362_,
                        v_decl_8452_,
                        v_a_8364_,
                        v_a_8365_,
                        v_a_8366_,
                        v_a_8367_,
                        v_a_8368_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8454_) == 0 {
                        v_a_8455_ = crate::leanh::lean_ctor_get(v___x_8454_, 0);
                        crate::leanh::lean_inc(v_a_8455_);
                        crate::leanh::lean_dec_ref_known(v___x_8454_, 1);
                        crate::leanh::lean_inc_ref(v_k_8453_);
                        v___x_8456_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8453_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8456_) == 0 {
                            v_a_8457_ = crate::leanh::lean_ctor_get(v___x_8456_, 0);
                            v_isSharedCheck_8484_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8456_)) as u8;
                            if v_isSharedCheck_8484_ == 0 {
                                v___x_8459_ = v___x_8456_;
                                v_isShared_8460_ = v_isSharedCheck_8484_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8457_);
                                crate::leanh::lean_dec(v___x_8456_);
                                v___x_8459_ = crate::leanh::lean_box(0);
                                v_isShared_8460_ = v_isSharedCheck_8484_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8455_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8456_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8485_ = crate::leanh::lean_ctor_get(v___x_8454_, 0);
                        v_isSharedCheck_8492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8454_)) as u8;
                        if v_isSharedCheck_8492_ == 0 {
                            v___x_8487_ = v___x_8454_;
                            v_isShared_8488_ = v_isSharedCheck_8492_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8485_);
                            crate::leanh::lean_dec(v___x_8454_);
                            v___x_8487_ = crate::leanh::lean_box(0);
                            v_isShared_8488_ = v_isSharedCheck_8492_;
                            state = 23;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_8493_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_args_8494_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    crate::leanh::lean_inc(v_fvarId_8493_);
                    v___x_8495_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8493_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8495_) == 0 {
                        v_fvarId_8496_ = crate::leanh::lean_ctor_get(v___x_8495_, 0);
                        crate::leanh::lean_inc(v_fvarId_8496_);
                        crate::leanh::lean_dec_ref_known(v___x_8495_, 1);
                        crate::leanh::lean_inc_ref(v_args_8494_);
                        v___x_8497_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_8361_, v_t_8362_, v_args_8494_, v_a_8364_);
                        if crate::leanh::lean_obj_tag(v___x_8497_) == 0 {
                            v_a_8498_ = crate::leanh::lean_ctor_get(v___x_8497_, 0);
                            v_isSharedCheck_8523_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8497_)) as u8;
                            if v_isSharedCheck_8523_ == 0 {
                                v___x_8500_ = v___x_8497_;
                                v_isShared_8501_ = v_isSharedCheck_8523_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8498_);
                                crate::leanh::lean_dec(v___x_8497_);
                                v___x_8500_ = crate::leanh::lean_box(0);
                                v_isShared_8501_ = v_isSharedCheck_8523_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8496_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                            v_a_8524_ = crate::leanh::lean_ctor_get(v___x_8497_, 0);
                            v_isSharedCheck_8531_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8497_)) as u8;
                            if v_isSharedCheck_8531_ == 0 {
                                v___x_8526_ = v___x_8497_;
                                v_isShared_8527_ = v_isSharedCheck_8531_;
                                state = 31;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8524_);
                                crate::leanh::lean_dec(v___x_8497_);
                                v___x_8526_ = crate::leanh::lean_box(0);
                                v_isShared_8527_ = v_isSharedCheck_8531_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                        v___x_8532_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8532_;
                    }
                }
                4 => {
                    v_cases_8533_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    crate::leanh::lean_inc_ref(v_cases_8533_);
                    v_typeName_8534_ = crate::leanh::lean_ctor_get(v_cases_8533_, 0);
                    v_resultType_8535_ = crate::leanh::lean_ctor_get(v_cases_8533_, 1);
                    v_discr_8536_ = crate::leanh::lean_ctor_get(v_cases_8533_, 2);
                    v_alts_8537_ = crate::leanh::lean_ctor_get(v_cases_8533_, 3);
                    v_isSharedCheck_8584_ = (!crate::leanh::lean_is_exclusive(v_cases_8533_)) as u8;
                    if v_isSharedCheck_8584_ == 0 {
                        v___x_8539_ = v_cases_8533_;
                        v_isShared_8540_ = v_isSharedCheck_8584_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_8537_);
                        crate::leanh::lean_inc(v_discr_8536_);
                        crate::leanh::lean_inc(v_resultType_8535_);
                        crate::leanh::lean_inc(v_typeName_8534_);
                        crate::leanh::lean_dec(v_cases_8533_);
                        v___x_8539_ = crate::leanh::lean_box(0);
                        v_isShared_8540_ = v_isSharedCheck_8584_;
                        state = 33;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_8585_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    crate::leanh::lean_inc(v_fvarId_8585_);
                    v___x_8586_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8585_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8586_) == 0 {
                        v_fvarId_8587_ = crate::leanh::lean_ctor_get(v___x_8586_, 0);
                        v_isSharedCheck_8606_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8586_)) as u8;
                        if v_isSharedCheck_8606_ == 0 {
                            v___x_8589_ = v___x_8586_;
                            v_isShared_8590_ = v_isSharedCheck_8606_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_8587_);
                            crate::leanh::lean_dec(v___x_8586_);
                            v___x_8589_ = crate::leanh::lean_box(0);
                            v_isShared_8590_ = v_isSharedCheck_8606_;
                            state = 43;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 1);
                        v___x_8607_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8607_;
                    }
                }
                6 => {
                    v_type_8608_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    crate::leanh::lean_inc_ref(v_type_8608_);
                    v___x_8609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8361_, v_a_8364_, v_t_8362_, v_type_8608_);
                    v___x_8610_ = lean_ptr_addr(v_type_8608_);
                    v___x_8611_ = lean_ptr_addr(v___x_8609_);
                    v___x_8612_ = lean_usize_dec_eq(v___x_8610_, v___x_8611_);
                    if v___x_8612_ == 0 {
                        v_isSharedCheck_8620_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8620_ == 0 {
                            v_unused_8621_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8621_);
                            v___x_8614_ = v_code_8363_;
                            v_isShared_8615_ = v_isSharedCheck_8620_;
                            state = 48;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8614_ = crate::leanh::lean_box(0);
                            v_isShared_8615_ = v_isSharedCheck_8620_;
                            state = 48;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_8609_);
                        v___x_8622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8622_, 0, v_code_8363_);
                        return v___x_8622_;
                    }
                }
                7 => {
                    v_fvarId_8623_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_i_8624_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_y_8625_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    v_k_8626_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                    crate::leanh::lean_inc(v_fvarId_8623_);
                    v___x_8627_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8623_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8627_) == 0 {
                        v_fvarId_8628_ = crate::leanh::lean_ctor_get(v___x_8627_, 0);
                        crate::leanh::lean_inc(v_fvarId_8628_);
                        crate::leanh::lean_dec_ref_known(v___x_8627_, 1);
                        crate::leanh::lean_inc(v_y_8625_);
                        v___x_8629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_8361_, v_a_8364_, v_y_8625_, v_t_8362_);
                        crate::leanh::lean_inc_ref(v_k_8626_);
                        v___x_8630_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8626_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8630_) == 0 {
                            v_a_8631_ = crate::leanh::lean_ctor_get(v___x_8630_, 0);
                            v_isSharedCheck_8692_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8630_)) as u8;
                            if v_isSharedCheck_8692_ == 0 {
                                v___x_8633_ = v___x_8630_;
                                v_isShared_8634_ = v_isSharedCheck_8692_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8631_);
                                crate::leanh::lean_dec(v___x_8630_);
                                v___x_8633_ = crate::leanh::lean_box(0);
                                v_isShared_8634_ = v_isSharedCheck_8692_;
                                state = 50;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_8629_);
                            crate::leanh::lean_dec(v_fvarId_8628_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                            return v___x_8630_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                        v___x_8693_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8693_;
                    }
                }
                8 => {
                    v_fvarId_8694_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_i_8695_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_y_8696_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    v_k_8697_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                    crate::leanh::lean_inc(v_fvarId_8694_);
                    v___x_8698_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8694_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8698_) == 0 {
                        v_fvarId_8699_ = crate::leanh::lean_ctor_get(v___x_8698_, 0);
                        crate::leanh::lean_inc(v_fvarId_8699_);
                        crate::leanh::lean_dec_ref_known(v___x_8698_, 1);
                        crate::leanh::lean_inc(v_y_8696_);
                        v___x_8700_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_a_8364_, v_y_8696_, v_t_8362_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8700_) == 0 {
                            v_fvarId_8701_ = crate::leanh::lean_ctor_get(v___x_8700_, 0);
                            crate::leanh::lean_inc(v_fvarId_8701_);
                            crate::leanh::lean_dec_ref_known(v___x_8700_, 1);
                            crate::leanh::lean_inc_ref(v_k_8697_);
                            v___x_8702_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8361_, v_t_8362_, v_k_8697_, v_a_8364_, v_a_8365_, v_a_8366_,
                                v_a_8367_, v_a_8368_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_8702_) == 0 {
                                v_a_8703_ = crate::leanh::lean_ctor_get(v___x_8702_, 0);
                                v_isSharedCheck_8764_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8702_)) as u8;
                                if v_isSharedCheck_8764_ == 0 {
                                    v___x_8705_ = v___x_8702_;
                                    v_isShared_8706_ = v_isSharedCheck_8764_;
                                    state = 62;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8703_);
                                    crate::leanh::lean_dec(v___x_8702_);
                                    v___x_8705_ = crate::leanh::lean_box(0);
                                    v_isShared_8706_ = v_isSharedCheck_8764_;
                                    state = 62;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fvarId_8701_);
                                crate::leanh::lean_dec(v_fvarId_8699_);
                                crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                                return v___x_8702_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8699_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                            v___x_8765_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                            );
                            return v___x_8765_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                        v___x_8766_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8766_;
                    }
                }
                9 => {
                    v_fvarId_8767_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_i_8768_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_offset_8769_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    v_y_8770_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                    v_ty_8771_ = crate::leanh::lean_ctor_get(v_code_8363_, 4);
                    v_k_8772_ = crate::leanh::lean_ctor_get(v_code_8363_, 5);
                    crate::leanh::lean_inc(v_fvarId_8767_);
                    v___x_8773_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8767_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8773_) == 0 {
                        v_fvarId_8774_ = crate::leanh::lean_ctor_get(v___x_8773_, 0);
                        crate::leanh::lean_inc(v_fvarId_8774_);
                        crate::leanh::lean_dec_ref_known(v___x_8773_, 1);
                        crate::leanh::lean_inc(v_y_8770_);
                        v___x_8775_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_a_8364_, v_y_8770_, v_t_8362_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8775_) == 0 {
                            v_fvarId_8776_ = crate::leanh::lean_ctor_get(v___x_8775_, 0);
                            crate::leanh::lean_inc(v_fvarId_8776_);
                            crate::leanh::lean_dec_ref_known(v___x_8775_, 1);
                            crate::leanh::lean_inc_ref(v_ty_8771_);
                            v___x_8777_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8361_, v_a_8364_, v_t_8362_, v_ty_8771_);
                            crate::leanh::lean_inc_ref(v_k_8772_);
                            v___x_8778_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8361_, v_t_8362_, v_k_8772_, v_a_8364_, v_a_8365_, v_a_8366_,
                                v_a_8367_, v_a_8368_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_8778_) == 0 {
                                v_a_8779_ = crate::leanh::lean_ctor_get(v___x_8778_, 0);
                                v_isSharedCheck_8882_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8778_)) as u8;
                                if v_isSharedCheck_8882_ == 0 {
                                    v___x_8781_ = v___x_8778_;
                                    v_isShared_8782_ = v_isSharedCheck_8882_;
                                    state = 74;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8779_);
                                    crate::leanh::lean_dec(v___x_8778_);
                                    v___x_8781_ = crate::leanh::lean_box(0);
                                    v_isShared_8782_ = v_isSharedCheck_8882_;
                                    state = 74;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_8777_);
                                crate::leanh::lean_dec(v_fvarId_8776_);
                                crate::leanh::lean_dec(v_fvarId_8774_);
                                crate::leanh::lean_dec_ref_known(v_code_8363_, 6);
                                return v___x_8778_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8774_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 6);
                            v___x_8883_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                            );
                            return v___x_8883_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 6);
                        v___x_8884_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8884_;
                    }
                }
                10 => {
                    v_fvarId_8885_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_cidx_8886_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_k_8887_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    crate::leanh::lean_inc(v_fvarId_8885_);
                    v___x_8888_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8885_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8888_) == 0 {
                        v_fvarId_8889_ = crate::leanh::lean_ctor_get(v___x_8888_, 0);
                        crate::leanh::lean_inc(v_fvarId_8889_);
                        crate::leanh::lean_dec_ref_known(v___x_8888_, 1);
                        crate::leanh::lean_inc_ref(v_k_8887_);
                        v___x_8890_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8887_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8890_) == 0 {
                            v_a_8891_ = crate::leanh::lean_ctor_get(v___x_8890_, 0);
                            v_isSharedCheck_8933_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8890_)) as u8;
                            if v_isSharedCheck_8933_ == 0 {
                                v___x_8893_ = v___x_8890_;
                                v_isShared_8894_ = v_isSharedCheck_8933_;
                                state = 92;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8891_);
                                crate::leanh::lean_dec(v___x_8890_);
                                v___x_8893_ = crate::leanh::lean_box(0);
                                v_isShared_8894_ = v_isSharedCheck_8933_;
                                state = 92;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8889_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 3);
                            return v___x_8890_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 3);
                        v___x_8934_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8934_;
                    }
                }
                11 => {
                    v_fvarId_8935_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_n_8936_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_check_8937_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_8938_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_8939_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    crate::leanh::lean_inc(v_fvarId_8935_);
                    v___x_8940_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8935_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8940_) == 0 {
                        v_fvarId_8941_ = crate::leanh::lean_ctor_get(v___x_8940_, 0);
                        crate::leanh::lean_inc(v_fvarId_8941_);
                        crate::leanh::lean_dec_ref_known(v___x_8940_, 1);
                        crate::leanh::lean_inc_ref(v_k_8939_);
                        v___x_8942_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8939_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8942_) == 0 {
                            v_a_8943_ = crate::leanh::lean_ctor_get(v___x_8942_, 0);
                            v_isSharedCheck_8985_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8942_)) as u8;
                            if v_isSharedCheck_8985_ == 0 {
                                v___x_8945_ = v___x_8942_;
                                v_isShared_8946_ = v_isSharedCheck_8985_;
                                state = 101;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8943_);
                                crate::leanh::lean_dec(v___x_8942_);
                                v___x_8945_ = crate::leanh::lean_box(0);
                                v_isShared_8946_ = v_isSharedCheck_8985_;
                                state = 101;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8941_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 3);
                            return v___x_8942_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 3);
                        v___x_8986_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8986_;
                    }
                }
                12 => {
                    v_fvarId_8987_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_n_8988_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    v_check_8989_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_8990_ = crate::leanh::lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_8991_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                    v_k_8992_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                    crate::leanh::lean_inc(v_fvarId_8987_);
                    v___x_8993_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8987_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8993_) == 0 {
                        v_fvarId_8994_ = crate::leanh::lean_ctor_get(v___x_8993_, 0);
                        crate::leanh::lean_inc(v_fvarId_8994_);
                        crate::leanh::lean_dec_ref_known(v___x_8993_, 1);
                        crate::leanh::lean_inc_ref(v_k_8992_);
                        v___x_8995_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8992_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8995_) == 0 {
                            v_a_8996_ = crate::leanh::lean_ctor_get(v___x_8995_, 0);
                            v_isSharedCheck_9056_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8995_)) as u8;
                            if v_isSharedCheck_9056_ == 0 {
                                v___x_8998_ = v___x_8995_;
                                v_isShared_8999_ = v_isSharedCheck_9056_;
                                state = 110;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8996_);
                                crate::leanh::lean_dec(v___x_8995_);
                                v___x_8998_ = crate::leanh::lean_box(0);
                                v_isShared_8999_ = v_isSharedCheck_9056_;
                                state = 110;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_8994_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                            return v___x_8995_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 4);
                        v___x_9057_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_9057_;
                    }
                }
                _ => {
                    v_fvarId_9058_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                    v_k_9059_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                    crate::leanh::lean_inc(v_fvarId_9058_);
                    v___x_9060_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_9058_,
                        v_t_8362_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_9060_) == 0 {
                        v_fvarId_9061_ = crate::leanh::lean_ctor_get(v___x_9060_, 0);
                        crate::leanh::lean_inc(v_fvarId_9061_);
                        crate::leanh::lean_dec_ref_known(v___x_9060_, 1);
                        crate::leanh::lean_inc_ref(v_k_9059_);
                        v___x_9062_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_9059_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_9062_) == 0 {
                            v_a_9063_ = crate::leanh::lean_ctor_get(v___x_9062_, 0);
                            v_isSharedCheck_9090_ =
                                (!crate::leanh::lean_is_exclusive(v___x_9062_)) as u8;
                            if v_isSharedCheck_9090_ == 0 {
                                v___x_9065_ = v___x_9062_;
                                v_isShared_9066_ = v_isSharedCheck_9090_;
                                state = 122;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_9063_);
                                crate::leanh::lean_dec(v___x_9062_);
                                v___x_9065_ = crate::leanh::lean_box(0);
                                v_isShared_9066_ = v_isSharedCheck_9090_;
                                state = 122;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_9061_);
                            crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_9062_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 2);
                        v___x_9091_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_9091_;
                    }
                }
            },
            1 => {
                v___x_8396_ = lean_ptr_addr(v_k_8371_);
                v___x_8397_ = lean_ptr_addr(v_a_8375_);
                v___x_8398_ = lean_usize_dec_eq(v___x_8396_, v___x_8397_);
                if v___x_8398_ == 0 {
                    v___y_8380_ = v___x_8398_;
                    state = 2;
                    continue;
                } else {
                    v___x_8399_ = lean_ptr_addr(v_decl_8370_);
                    v___x_8400_ = lean_ptr_addr(v_a_8373_);
                    v___x_8401_ = lean_usize_dec_eq(v___x_8399_, v___x_8400_);
                    v___y_8380_ = v___x_8401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_8380_ == 0 {
                    v_isSharedCheck_8390_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8390_ == 0 {
                        v_unused_8391_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8391_);
                        v_unused_8392_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8392_);
                        v___x_8382_ = v_code_8363_;
                        v_isShared_8383_ = v_isSharedCheck_8390_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8382_ = crate::leanh::lean_box(0);
                        v_isShared_8383_ = v_isSharedCheck_8390_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8375_);
                    crate::leanh::lean_dec(v_a_8373_);
                    if v_isShared_8378_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8377_, 0, v_code_8363_);
                        v___x_8394_ = v___x_8377_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8395_, 0, v_code_8363_);
                        v___x_8394_ = v_reuseFailAlloc_8395_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8382_, 1, v_a_8375_);
                    crate::leanh::lean_ctor_set(v___x_8382_, 0, v_a_8373_);
                    v___x_8385_ = v___x_8382_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8389_, 0, v_a_8373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8389_, 1, v_a_8375_);
                    v___x_8385_ = v_reuseFailAlloc_8389_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8377_, 0, v___x_8385_);
                    v___x_8387_ = v___x_8377_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8388_, 0, v___x_8385_);
                    v___x_8387_ = v_reuseFailAlloc_8388_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8387_;
            }
            6 => {
                return v___x_8394_;
            }
            7 => {
                if v_isShared_8406_ == 0 {
                    v___x_8408_ = v___x_8405_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8409_, 0, v_a_8403_);
                    v___x_8408_ = v_reuseFailAlloc_8409_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8408_;
            }
            9 => {
                v___x_8437_ = lean_ptr_addr(v_k_8412_);
                v___x_8438_ = lean_ptr_addr(v_a_8416_);
                v___x_8439_ = lean_usize_dec_eq(v___x_8437_, v___x_8438_);
                if v___x_8439_ == 0 {
                    v___y_8421_ = v___x_8439_;
                    state = 10;
                    continue;
                } else {
                    v___x_8440_ = lean_ptr_addr(v_decl_8411_);
                    v___x_8441_ = lean_ptr_addr(v_a_8414_);
                    v___x_8442_ = lean_usize_dec_eq(v___x_8440_, v___x_8441_);
                    v___y_8421_ = v___x_8442_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_8421_ == 0 {
                    v_isSharedCheck_8431_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8431_ == 0 {
                        v_unused_8432_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8432_);
                        v_unused_8433_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8433_);
                        v___x_8423_ = v_code_8363_;
                        v_isShared_8424_ = v_isSharedCheck_8431_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8423_ = crate::leanh::lean_box(0);
                        v_isShared_8424_ = v_isSharedCheck_8431_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8416_);
                    crate::leanh::lean_dec(v_a_8414_);
                    if v_isShared_8419_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8418_, 0, v_code_8363_);
                        v___x_8435_ = v___x_8418_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_8436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8436_, 0, v_code_8363_);
                        v___x_8435_ = v_reuseFailAlloc_8436_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_8424_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8423_, 1, v_a_8416_);
                    crate::leanh::lean_ctor_set(v___x_8423_, 0, v_a_8414_);
                    v___x_8426_ = v___x_8423_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8430_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8430_, 0, v_a_8414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8430_, 1, v_a_8416_);
                    v___x_8426_ = v_reuseFailAlloc_8430_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_8419_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8418_, 0, v___x_8426_);
                    v___x_8428_ = v___x_8418_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8429_, 0, v___x_8426_);
                    v___x_8428_ = v_reuseFailAlloc_8429_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_8428_;
            }
            14 => {
                return v___x_8435_;
            }
            15 => {
                if v_isShared_8447_ == 0 {
                    v___x_8449_ = v___x_8446_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_8450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8450_, 0, v_a_8444_);
                    v___x_8449_ = v_reuseFailAlloc_8450_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_8449_;
            }
            17 => {
                v___x_8478_ = lean_ptr_addr(v_k_8453_);
                v___x_8479_ = lean_ptr_addr(v_a_8457_);
                v___x_8480_ = lean_usize_dec_eq(v___x_8478_, v___x_8479_);
                if v___x_8480_ == 0 {
                    v___y_8462_ = v___x_8480_;
                    state = 18;
                    continue;
                } else {
                    v___x_8481_ = lean_ptr_addr(v_decl_8452_);
                    v___x_8482_ = lean_ptr_addr(v_a_8455_);
                    v___x_8483_ = lean_usize_dec_eq(v___x_8481_, v___x_8482_);
                    v___y_8462_ = v___x_8483_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_8462_ == 0 {
                    v_isSharedCheck_8472_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8472_ == 0 {
                        v_unused_8473_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8473_);
                        v_unused_8474_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8474_);
                        v___x_8464_ = v_code_8363_;
                        v_isShared_8465_ = v_isSharedCheck_8472_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8464_ = crate::leanh::lean_box(0);
                        v_isShared_8465_ = v_isSharedCheck_8472_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8457_);
                    crate::leanh::lean_dec(v_a_8455_);
                    if v_isShared_8460_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8459_, 0, v_code_8363_);
                        v___x_8476_ = v___x_8459_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_8477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8477_, 0, v_code_8363_);
                        v___x_8476_ = v_reuseFailAlloc_8477_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_8465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8464_, 1, v_a_8457_);
                    crate::leanh::lean_ctor_set(v___x_8464_, 0, v_a_8455_);
                    v___x_8467_ = v___x_8464_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8471_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8471_, 0, v_a_8455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8471_, 1, v_a_8457_);
                    v___x_8467_ = v_reuseFailAlloc_8471_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_8460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8459_, 0, v___x_8467_);
                    v___x_8469_ = v___x_8459_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8470_, 0, v___x_8467_);
                    v___x_8469_ = v_reuseFailAlloc_8470_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_8469_;
            }
            22 => {
                return v___x_8476_;
            }
            23 => {
                if v_isShared_8488_ == 0 {
                    v___x_8490_ = v___x_8487_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_8491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8491_, 0, v_a_8485_);
                    v___x_8490_ = v_reuseFailAlloc_8491_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_8490_;
            }
            25 => {
                v___x_8519_ = l_Lean_instBEqFVarId_beq(v_fvarId_8493_, v_fvarId_8496_);
                if v___x_8519_ == 0 {
                    v___y_8503_ = v___x_8519_;
                    state = 26;
                    continue;
                } else {
                    v___x_8520_ = lean_ptr_addr(v_args_8494_);
                    v___x_8521_ = lean_ptr_addr(v_a_8498_);
                    v___x_8522_ = lean_usize_dec_eq(v___x_8520_, v___x_8521_);
                    v___y_8503_ = v___x_8522_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v___y_8503_ == 0 {
                    v_isSharedCheck_8513_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8513_ == 0 {
                        v_unused_8514_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8514_);
                        v_unused_8515_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8515_);
                        v___x_8505_ = v_code_8363_;
                        v_isShared_8506_ = v_isSharedCheck_8513_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8505_ = crate::leanh::lean_box(0);
                        v_isShared_8506_ = v_isSharedCheck_8513_;
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_8498_);
                    crate::leanh::lean_dec(v_fvarId_8496_);
                    if v_isShared_8501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8500_, 0, v_code_8363_);
                        v___x_8517_ = v___x_8500_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_8518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8518_, 0, v_code_8363_);
                        v___x_8517_ = v_reuseFailAlloc_8518_;
                        state = 30;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_8506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8505_, 1, v_a_8498_);
                    crate::leanh::lean_ctor_set(v___x_8505_, 0, v_fvarId_8496_);
                    v___x_8508_ = v___x_8505_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_8512_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8512_, 0, v_fvarId_8496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8512_, 1, v_a_8498_);
                    v___x_8508_ = v_reuseFailAlloc_8512_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_8501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8500_, 0, v___x_8508_);
                    v___x_8510_ = v___x_8500_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_8511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8511_, 0, v___x_8508_);
                    v___x_8510_ = v_reuseFailAlloc_8511_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_8510_;
            }
            30 => {
                return v___x_8517_;
            }
            31 => {
                if v_isShared_8527_ == 0 {
                    v___x_8529_ = v___x_8526_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_8530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8530_, 0, v_a_8524_);
                    v___x_8529_ = v_reuseFailAlloc_8530_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_8529_;
            }
            33 => {
                crate::leanh::lean_inc_ref(v_resultType_8535_);
                v___x_8541_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v_pu_8361_,
                        v_a_8364_,
                        v_t_8362_,
                        v_resultType_8535_,
                    );
                crate::leanh::lean_inc(v_discr_8536_);
                v___x_8542_ =
                    l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_8364_, v_discr_8536_, v_t_8362_);
                if crate::leanh::lean_obj_tag(v___x_8542_) == 0 {
                    v_fvarId_8543_ = crate::leanh::lean_ctor_get(v___x_8542_, 0);
                    v_isSharedCheck_8582_ = (!crate::leanh::lean_is_exclusive(v___x_8542_)) as u8;
                    if v_isSharedCheck_8582_ == 0 {
                        v___x_8545_ = v___x_8542_;
                        v_isShared_8546_ = v_isSharedCheck_8582_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_8543_);
                        crate::leanh::lean_dec(v___x_8542_);
                        v___x_8545_ = crate::leanh::lean_box(0);
                        v_isShared_8546_ = v_isSharedCheck_8582_;
                        state = 34;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_8541_);
                    crate::leanh::lean_del_object(v___x_8539_);
                    crate::leanh::lean_dec_ref(v_alts_8537_);
                    crate::leanh::lean_dec(v_discr_8536_);
                    crate::leanh::lean_dec_ref(v_resultType_8535_);
                    crate::leanh::lean_dec(v_typeName_8534_);
                    crate::leanh::lean_dec_ref_known(v_code_8363_, 1);
                    v___x_8583_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                    );
                    return v___x_8583_;
                }
            }
            34 => {
                v___x_8547_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_8537_);
                v___x_8548_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_8361_, v_t_8362_, v___x_8547_, v_alts_8537_, v_a_8364_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_);
                if crate::leanh::lean_obj_tag(v___x_8548_) == 0 {
                    v_a_8549_ = crate::leanh::lean_ctor_get(v___x_8548_, 0);
                    v_isSharedCheck_8573_ = (!crate::leanh::lean_is_exclusive(v___x_8548_)) as u8;
                    if v_isSharedCheck_8573_ == 0 {
                        v___x_8551_ = v___x_8548_;
                        v_isShared_8552_ = v_isSharedCheck_8573_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8549_);
                        crate::leanh::lean_dec(v___x_8548_);
                        v___x_8551_ = crate::leanh::lean_box(0);
                        v_isShared_8552_ = v_isSharedCheck_8573_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8545_);
                    crate::leanh::lean_dec(v_fvarId_8543_);
                    crate::leanh::lean_dec_ref(v___x_8541_);
                    crate::leanh::lean_del_object(v___x_8539_);
                    crate::leanh::lean_dec_ref(v_alts_8537_);
                    crate::leanh::lean_dec(v_discr_8536_);
                    crate::leanh::lean_dec_ref(v_resultType_8535_);
                    crate::leanh::lean_dec(v_typeName_8534_);
                    crate::leanh::lean_dec_ref_known(v_code_8363_, 1);
                    v_a_8574_ = crate::leanh::lean_ctor_get(v___x_8548_, 0);
                    v_isSharedCheck_8581_ = (!crate::leanh::lean_is_exclusive(v___x_8548_)) as u8;
                    if v_isSharedCheck_8581_ == 0 {
                        v___x_8576_ = v___x_8548_;
                        v_isShared_8577_ = v_isSharedCheck_8581_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8574_);
                        crate::leanh::lean_dec(v___x_8548_);
                        v___x_8576_ = crate::leanh::lean_box(0);
                        v_isShared_8577_ = v_isSharedCheck_8581_;
                        state = 41;
                        continue;
                    }
                }
            }
            35 => {
                v___x_8567_ = lean_ptr_addr(v_alts_8537_);
                crate::leanh::lean_dec_ref(v_alts_8537_);
                v___x_8568_ = lean_ptr_addr(v_a_8549_);
                v___x_8569_ = lean_usize_dec_eq(v___x_8567_, v___x_8568_);
                if v___x_8569_ == 0 {
                    crate::leanh::lean_dec_ref(v_resultType_8535_);
                    v___y_8564_ = v___x_8569_;
                    state = 40;
                    continue;
                } else {
                    v___x_8570_ = lean_ptr_addr(v_resultType_8535_);
                    crate::leanh::lean_dec_ref(v_resultType_8535_);
                    v___x_8571_ = lean_ptr_addr(v___x_8541_);
                    v___x_8572_ = lean_usize_dec_eq(v___x_8570_, v___x_8571_);
                    v___y_8564_ = v___x_8572_;
                    state = 40;
                    continue;
                }
            }
            36 => {
                if v_isShared_8540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8539_, 3, v_a_8549_);
                    crate::leanh::lean_ctor_set(v___x_8539_, 2, v_fvarId_8543_);
                    crate::leanh::lean_ctor_set(v___x_8539_, 1, v___x_8541_);
                    v___x_8555_ = v___x_8539_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8562_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8562_, 0, v_typeName_8534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8562_, 1, v___x_8541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8562_, 2, v_fvarId_8543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8562_, 3, v_a_8549_);
                    v___x_8555_ = v_reuseFailAlloc_8562_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_8546_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_8545_, 4);
                    crate::leanh::lean_ctor_set(v___x_8545_, 0, v___x_8555_);
                    v___x_8557_ = v___x_8545_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_8561_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8561_, 0, v___x_8555_);
                    v___x_8557_ = v_reuseFailAlloc_8561_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_8552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8551_, 0, v___x_8557_);
                    v___x_8559_ = v___x_8551_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_8560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8560_, 0, v___x_8557_);
                    v___x_8559_ = v_reuseFailAlloc_8560_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_8559_;
            }
            40 => {
                if v___y_8564_ == 0 {
                    crate::leanh::lean_dec(v_discr_8536_);
                    crate::leanh::lean_dec_ref_known(v_code_8363_, 1);
                    state = 36;
                    continue;
                } else {
                    v___x_8565_ = l_Lean_instBEqFVarId_beq(v_discr_8536_, v_fvarId_8543_);
                    crate::leanh::lean_dec(v_discr_8536_);
                    if v___x_8565_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_code_8363_, 1);
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_8551_);
                        crate::leanh::lean_dec(v_a_8549_);
                        crate::leanh::lean_del_object(v___x_8545_);
                        crate::leanh::lean_dec(v_fvarId_8543_);
                        crate::leanh::lean_dec_ref(v___x_8541_);
                        crate::leanh::lean_del_object(v___x_8539_);
                        crate::leanh::lean_dec(v_typeName_8534_);
                        v___x_8566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8566_, 0, v_code_8363_);
                        return v___x_8566_;
                    }
                }
            }
            41 => {
                if v_isShared_8577_ == 0 {
                    v___x_8579_ = v___x_8576_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_8580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8580_, 0, v_a_8574_);
                    v___x_8579_ = v_reuseFailAlloc_8580_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_8579_;
            }
            43 => {
                v___x_8591_ = l_Lean_instBEqFVarId_beq(v_fvarId_8585_, v_fvarId_8587_);
                if v___x_8591_ == 0 {
                    v_isSharedCheck_8601_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8601_ == 0 {
                        v_unused_8602_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8602_);
                        v___x_8593_ = v_code_8363_;
                        v_isShared_8594_ = v_isSharedCheck_8601_;
                        state = 44;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8593_ = crate::leanh::lean_box(0);
                        v_isShared_8594_ = v_isSharedCheck_8601_;
                        state = 44;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_8587_);
                    if v_isShared_8590_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8589_, 0, v_code_8363_);
                        v___x_8604_ = v___x_8589_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_8605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8605_, 0, v_code_8363_);
                        v___x_8604_ = v_reuseFailAlloc_8605_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_8594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8593_, 0, v_fvarId_8587_);
                    v___x_8596_ = v___x_8593_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_8600_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8600_, 0, v_fvarId_8587_);
                    v___x_8596_ = v_reuseFailAlloc_8600_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_8590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8589_, 0, v___x_8596_);
                    v___x_8598_ = v___x_8589_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_8599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8599_, 0, v___x_8596_);
                    v___x_8598_ = v_reuseFailAlloc_8599_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_8598_;
            }
            47 => {
                return v___x_8604_;
            }
            48 => {
                if v_isShared_8615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8614_, 0, v___x_8609_);
                    v___x_8617_ = v___x_8614_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_8619_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8619_, 0, v___x_8609_);
                    v___x_8617_ = v_reuseFailAlloc_8619_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                v___x_8618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8618_, 0, v___x_8617_);
                return v___x_8618_;
            }
            50 => {
                v___x_8688_ = lean_ptr_addr(v_fvarId_8623_);
                v___x_8689_ = lean_ptr_addr(v_fvarId_8628_);
                v___x_8690_ = lean_usize_dec_eq(v___x_8688_, v___x_8689_);
                if v___x_8690_ == 0 {
                    v___y_8636_ = v___x_8690_;
                    state = 51;
                    continue;
                } else {
                    v___x_8691_ = lean_nat_dec_eq(v_i_8624_, v_i_8624_);
                    v___y_8636_ = v___x_8691_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v___y_8636_ == 0 {
                    crate::leanh::lean_inc(v_i_8624_);
                    v_isSharedCheck_8646_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8646_ == 0 {
                        v_unused_8647_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                        crate::leanh::lean_dec(v_unused_8647_);
                        v_unused_8648_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_8648_);
                        v_unused_8649_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8649_);
                        v_unused_8650_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8650_);
                        v___x_8638_ = v_code_8363_;
                        v_isShared_8639_ = v_isSharedCheck_8646_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8638_ = crate::leanh::lean_box(0);
                        v_isShared_8639_ = v_isSharedCheck_8646_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_8651_ = lean_ptr_addr(v_y_8625_);
                    v___x_8652_ = lean_ptr_addr(v___x_8629_);
                    v___x_8653_ = lean_usize_dec_eq(v___x_8651_, v___x_8652_);
                    if v___x_8653_ == 0 {
                        crate::leanh::lean_inc(v_i_8624_);
                        v_isSharedCheck_8663_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8663_ == 0 {
                            v_unused_8664_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                            crate::leanh::lean_dec(v_unused_8664_);
                            v_unused_8665_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_8665_);
                            v_unused_8666_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_8666_);
                            v_unused_8667_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8667_);
                            v___x_8655_ = v_code_8363_;
                            v_isShared_8656_ = v_isSharedCheck_8663_;
                            state = 55;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8655_ = crate::leanh::lean_box(0);
                            v_isShared_8656_ = v_isSharedCheck_8663_;
                            state = 55;
                            continue;
                        }
                    } else {
                        v___x_8668_ = lean_ptr_addr(v_k_8626_);
                        v___x_8669_ = lean_ptr_addr(v_a_8631_);
                        v___x_8670_ = lean_usize_dec_eq(v___x_8668_, v___x_8669_);
                        if v___x_8670_ == 0 {
                            crate::leanh::lean_inc(v_i_8624_);
                            v_isSharedCheck_8680_ =
                                (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8680_ == 0 {
                                v_unused_8681_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                crate::leanh::lean_dec(v_unused_8681_);
                                v_unused_8682_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                crate::leanh::lean_dec(v_unused_8682_);
                                v_unused_8683_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                crate::leanh::lean_dec(v_unused_8683_);
                                v_unused_8684_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                crate::leanh::lean_dec(v_unused_8684_);
                                v___x_8672_ = v_code_8363_;
                                v_isShared_8673_ = v_isSharedCheck_8680_;
                                state = 58;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_code_8363_);
                                v___x_8672_ = crate::leanh::lean_box(0);
                                v_isShared_8673_ = v_isSharedCheck_8680_;
                                state = 58;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8631_);
                            crate::leanh::lean_dec(v___x_8629_);
                            crate::leanh::lean_dec(v_fvarId_8628_);
                            if v_isShared_8634_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_8633_, 0, v_code_8363_);
                                v___x_8686_ = v___x_8633_;
                                state = 61;
                                continue;
                            } else {
                                v_reuseFailAlloc_8687_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_8687_,
                                    0,
                                    v_code_8363_,
                                );
                                v___x_8686_ = v_reuseFailAlloc_8687_;
                                state = 61;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                if v_isShared_8639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8638_, 3, v_a_8631_);
                    crate::leanh::lean_ctor_set(v___x_8638_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v___x_8638_, 0, v_fvarId_8628_);
                    v___x_8641_ = v___x_8638_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_8645_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 0, v_fvarId_8628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 1, v_i_8624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 3, v_a_8631_);
                    v___x_8641_ = v_reuseFailAlloc_8645_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_8634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8633_, 0, v___x_8641_);
                    v___x_8643_ = v___x_8633_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_8644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8644_, 0, v___x_8641_);
                    v___x_8643_ = v_reuseFailAlloc_8644_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_8643_;
            }
            55 => {
                if v_isShared_8656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8655_, 3, v_a_8631_);
                    crate::leanh::lean_ctor_set(v___x_8655_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v___x_8655_, 0, v_fvarId_8628_);
                    v___x_8658_ = v___x_8655_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_8662_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8662_, 0, v_fvarId_8628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8662_, 1, v_i_8624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8662_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8662_, 3, v_a_8631_);
                    v___x_8658_ = v_reuseFailAlloc_8662_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_8634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8633_, 0, v___x_8658_);
                    v___x_8660_ = v___x_8633_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_8661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8661_, 0, v___x_8658_);
                    v___x_8660_ = v_reuseFailAlloc_8661_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_8660_;
            }
            58 => {
                if v_isShared_8673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8672_, 3, v_a_8631_);
                    crate::leanh::lean_ctor_set(v___x_8672_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v___x_8672_, 0, v_fvarId_8628_);
                    v___x_8675_ = v___x_8672_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_8679_ = crate::leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8679_, 0, v_fvarId_8628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8679_, 1, v_i_8624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8679_, 2, v___x_8629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8679_, 3, v_a_8631_);
                    v___x_8675_ = v_reuseFailAlloc_8679_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_8634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8633_, 0, v___x_8675_);
                    v___x_8677_ = v___x_8633_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_8678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8678_, 0, v___x_8675_);
                    v___x_8677_ = v_reuseFailAlloc_8678_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_8677_;
            }
            61 => {
                return v___x_8686_;
            }
            62 => {
                v___x_8760_ = lean_ptr_addr(v_fvarId_8694_);
                v___x_8761_ = lean_ptr_addr(v_fvarId_8699_);
                v___x_8762_ = lean_usize_dec_eq(v___x_8760_, v___x_8761_);
                if v___x_8762_ == 0 {
                    v___y_8708_ = v___x_8762_;
                    state = 63;
                    continue;
                } else {
                    v___x_8763_ = lean_nat_dec_eq(v_i_8695_, v_i_8695_);
                    v___y_8708_ = v___x_8763_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v___y_8708_ == 0 {
                    crate::leanh::lean_inc(v_i_8695_);
                    v_isSharedCheck_8718_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8718_ == 0 {
                        v_unused_8719_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                        crate::leanh::lean_dec(v_unused_8719_);
                        v_unused_8720_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_8720_);
                        v_unused_8721_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8721_);
                        v_unused_8722_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8722_);
                        v___x_8710_ = v_code_8363_;
                        v_isShared_8711_ = v_isSharedCheck_8718_;
                        state = 64;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8710_ = crate::leanh::lean_box(0);
                        v_isShared_8711_ = v_isSharedCheck_8718_;
                        state = 64;
                        continue;
                    }
                } else {
                    v___x_8723_ = lean_ptr_addr(v_y_8696_);
                    v___x_8724_ = lean_ptr_addr(v_fvarId_8701_);
                    v___x_8725_ = lean_usize_dec_eq(v___x_8723_, v___x_8724_);
                    if v___x_8725_ == 0 {
                        crate::leanh::lean_inc(v_i_8695_);
                        v_isSharedCheck_8735_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8735_ == 0 {
                            v_unused_8736_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                            crate::leanh::lean_dec(v_unused_8736_);
                            v_unused_8737_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_8737_);
                            v_unused_8738_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_8738_);
                            v_unused_8739_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8739_);
                            v___x_8727_ = v_code_8363_;
                            v_isShared_8728_ = v_isSharedCheck_8735_;
                            state = 67;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8727_ = crate::leanh::lean_box(0);
                            v_isShared_8728_ = v_isSharedCheck_8735_;
                            state = 67;
                            continue;
                        }
                    } else {
                        v___x_8740_ = lean_ptr_addr(v_k_8697_);
                        v___x_8741_ = lean_ptr_addr(v_a_8703_);
                        v___x_8742_ = lean_usize_dec_eq(v___x_8740_, v___x_8741_);
                        if v___x_8742_ == 0 {
                            crate::leanh::lean_inc(v_i_8695_);
                            v_isSharedCheck_8752_ =
                                (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8752_ == 0 {
                                v_unused_8753_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                crate::leanh::lean_dec(v_unused_8753_);
                                v_unused_8754_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                crate::leanh::lean_dec(v_unused_8754_);
                                v_unused_8755_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                crate::leanh::lean_dec(v_unused_8755_);
                                v_unused_8756_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                crate::leanh::lean_dec(v_unused_8756_);
                                v___x_8744_ = v_code_8363_;
                                v_isShared_8745_ = v_isSharedCheck_8752_;
                                state = 70;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_code_8363_);
                                v___x_8744_ = crate::leanh::lean_box(0);
                                v_isShared_8745_ = v_isSharedCheck_8752_;
                                state = 70;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8703_);
                            crate::leanh::lean_dec(v_fvarId_8701_);
                            crate::leanh::lean_dec(v_fvarId_8699_);
                            if v_isShared_8706_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_8705_, 0, v_code_8363_);
                                v___x_8758_ = v___x_8705_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_8759_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_8759_,
                                    0,
                                    v_code_8363_,
                                );
                                v___x_8758_ = v_reuseFailAlloc_8759_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            64 => {
                if v_isShared_8711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8710_, 3, v_a_8703_);
                    crate::leanh::lean_ctor_set(v___x_8710_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v___x_8710_, 0, v_fvarId_8699_);
                    v___x_8713_ = v___x_8710_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_8717_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8717_, 0, v_fvarId_8699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8717_, 1, v_i_8695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8717_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8717_, 3, v_a_8703_);
                    v___x_8713_ = v_reuseFailAlloc_8717_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                if v_isShared_8706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8705_, 0, v___x_8713_);
                    v___x_8715_ = v___x_8705_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_8716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8716_, 0, v___x_8713_);
                    v___x_8715_ = v_reuseFailAlloc_8716_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_8715_;
            }
            67 => {
                if v_isShared_8728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8727_, 3, v_a_8703_);
                    crate::leanh::lean_ctor_set(v___x_8727_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v___x_8727_, 0, v_fvarId_8699_);
                    v___x_8730_ = v___x_8727_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_8734_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 0, v_fvarId_8699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 1, v_i_8695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8734_, 3, v_a_8703_);
                    v___x_8730_ = v_reuseFailAlloc_8734_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_8706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8705_, 0, v___x_8730_);
                    v___x_8732_ = v___x_8705_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_8733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8733_, 0, v___x_8730_);
                    v___x_8732_ = v_reuseFailAlloc_8733_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_8732_;
            }
            70 => {
                if v_isShared_8745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8744_, 3, v_a_8703_);
                    crate::leanh::lean_ctor_set(v___x_8744_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v___x_8744_, 0, v_fvarId_8699_);
                    v___x_8747_ = v___x_8744_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_8751_ = crate::leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8751_, 0, v_fvarId_8699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8751_, 1, v_i_8695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8751_, 2, v_fvarId_8701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8751_, 3, v_a_8703_);
                    v___x_8747_ = v_reuseFailAlloc_8751_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_8706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8705_, 0, v___x_8747_);
                    v___x_8749_ = v___x_8705_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_8750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8750_, 0, v___x_8747_);
                    v___x_8749_ = v_reuseFailAlloc_8750_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_8749_;
            }
            73 => {
                return v___x_8758_;
            }
            74 => {
                v___x_8878_ = lean_ptr_addr(v_fvarId_8767_);
                v___x_8879_ = lean_ptr_addr(v_fvarId_8774_);
                v___x_8880_ = lean_usize_dec_eq(v___x_8878_, v___x_8879_);
                if v___x_8880_ == 0 {
                    v___y_8784_ = v___x_8880_;
                    state = 75;
                    continue;
                } else {
                    v___x_8881_ = lean_nat_dec_eq(v_i_8768_, v_i_8768_);
                    v___y_8784_ = v___x_8881_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v___y_8784_ == 0 {
                    crate::leanh::lean_inc(v_offset_8769_);
                    crate::leanh::lean_inc(v_i_8768_);
                    v_isSharedCheck_8794_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8794_ == 0 {
                        v_unused_8795_ = crate::leanh::lean_ctor_get(v_code_8363_, 5);
                        crate::leanh::lean_dec(v_unused_8795_);
                        v_unused_8796_ = crate::leanh::lean_ctor_get(v_code_8363_, 4);
                        crate::leanh::lean_dec(v_unused_8796_);
                        v_unused_8797_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                        crate::leanh::lean_dec(v_unused_8797_);
                        v_unused_8798_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_8798_);
                        v_unused_8799_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8799_);
                        v_unused_8800_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8800_);
                        v___x_8786_ = v_code_8363_;
                        v_isShared_8787_ = v_isSharedCheck_8794_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8786_ = crate::leanh::lean_box(0);
                        v_isShared_8787_ = v_isSharedCheck_8794_;
                        state = 76;
                        continue;
                    }
                } else {
                    v___x_8801_ = lean_nat_dec_eq(v_offset_8769_, v_offset_8769_);
                    if v___x_8801_ == 0 {
                        crate::leanh::lean_inc(v_offset_8769_);
                        crate::leanh::lean_inc(v_i_8768_);
                        v_isSharedCheck_8811_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8811_ == 0 {
                            v_unused_8812_ = crate::leanh::lean_ctor_get(v_code_8363_, 5);
                            crate::leanh::lean_dec(v_unused_8812_);
                            v_unused_8813_ = crate::leanh::lean_ctor_get(v_code_8363_, 4);
                            crate::leanh::lean_dec(v_unused_8813_);
                            v_unused_8814_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                            crate::leanh::lean_dec(v_unused_8814_);
                            v_unused_8815_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_8815_);
                            v_unused_8816_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_8816_);
                            v_unused_8817_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8817_);
                            v___x_8803_ = v_code_8363_;
                            v_isShared_8804_ = v_isSharedCheck_8811_;
                            state = 79;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8803_ = crate::leanh::lean_box(0);
                            v_isShared_8804_ = v_isSharedCheck_8811_;
                            state = 79;
                            continue;
                        }
                    } else {
                        v___x_8818_ = lean_ptr_addr(v_y_8770_);
                        v___x_8819_ = lean_ptr_addr(v_fvarId_8776_);
                        v___x_8820_ = lean_usize_dec_eq(v___x_8818_, v___x_8819_);
                        if v___x_8820_ == 0 {
                            crate::leanh::lean_inc(v_offset_8769_);
                            crate::leanh::lean_inc(v_i_8768_);
                            v_isSharedCheck_8830_ =
                                (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8830_ == 0 {
                                v_unused_8831_ = crate::leanh::lean_ctor_get(v_code_8363_, 5);
                                crate::leanh::lean_dec(v_unused_8831_);
                                v_unused_8832_ = crate::leanh::lean_ctor_get(v_code_8363_, 4);
                                crate::leanh::lean_dec(v_unused_8832_);
                                v_unused_8833_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                crate::leanh::lean_dec(v_unused_8833_);
                                v_unused_8834_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                crate::leanh::lean_dec(v_unused_8834_);
                                v_unused_8835_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                crate::leanh::lean_dec(v_unused_8835_);
                                v_unused_8836_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                crate::leanh::lean_dec(v_unused_8836_);
                                v___x_8822_ = v_code_8363_;
                                v_isShared_8823_ = v_isSharedCheck_8830_;
                                state = 82;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_code_8363_);
                                v___x_8822_ = crate::leanh::lean_box(0);
                                v_isShared_8823_ = v_isSharedCheck_8830_;
                                state = 82;
                                continue;
                            }
                        } else {
                            v___x_8837_ = lean_ptr_addr(v_ty_8771_);
                            v___x_8838_ = lean_ptr_addr(v___x_8777_);
                            v___x_8839_ = lean_usize_dec_eq(v___x_8837_, v___x_8838_);
                            if v___x_8839_ == 0 {
                                crate::leanh::lean_inc(v_offset_8769_);
                                crate::leanh::lean_inc(v_i_8768_);
                                v_isSharedCheck_8849_ =
                                    (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                                if v_isSharedCheck_8849_ == 0 {
                                    v_unused_8850_ = crate::leanh::lean_ctor_get(v_code_8363_, 5);
                                    crate::leanh::lean_dec(v_unused_8850_);
                                    v_unused_8851_ = crate::leanh::lean_ctor_get(v_code_8363_, 4);
                                    crate::leanh::lean_dec(v_unused_8851_);
                                    v_unused_8852_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                    crate::leanh::lean_dec(v_unused_8852_);
                                    v_unused_8853_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                    crate::leanh::lean_dec(v_unused_8853_);
                                    v_unused_8854_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                    crate::leanh::lean_dec(v_unused_8854_);
                                    v_unused_8855_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                    crate::leanh::lean_dec(v_unused_8855_);
                                    v___x_8841_ = v_code_8363_;
                                    v_isShared_8842_ = v_isSharedCheck_8849_;
                                    state = 85;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_code_8363_);
                                    v___x_8841_ = crate::leanh::lean_box(0);
                                    v_isShared_8842_ = v_isSharedCheck_8849_;
                                    state = 85;
                                    continue;
                                }
                            } else {
                                v___x_8856_ = lean_ptr_addr(v_k_8772_);
                                v___x_8857_ = lean_ptr_addr(v_a_8779_);
                                v___x_8858_ = lean_usize_dec_eq(v___x_8856_, v___x_8857_);
                                if v___x_8858_ == 0 {
                                    crate::leanh::lean_inc(v_offset_8769_);
                                    crate::leanh::lean_inc(v_i_8768_);
                                    v_isSharedCheck_8868_ =
                                        (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                                    if v_isSharedCheck_8868_ == 0 {
                                        v_unused_8869_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 5);
                                        crate::leanh::lean_dec(v_unused_8869_);
                                        v_unused_8870_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 4);
                                        crate::leanh::lean_dec(v_unused_8870_);
                                        v_unused_8871_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                        crate::leanh::lean_dec(v_unused_8871_);
                                        v_unused_8872_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                        crate::leanh::lean_dec(v_unused_8872_);
                                        v_unused_8873_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                        crate::leanh::lean_dec(v_unused_8873_);
                                        v_unused_8874_ =
                                            crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                        crate::leanh::lean_dec(v_unused_8874_);
                                        v___x_8860_ = v_code_8363_;
                                        v_isShared_8861_ = v_isSharedCheck_8868_;
                                        state = 88;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_code_8363_);
                                        v___x_8860_ = crate::leanh::lean_box(0);
                                        v_isShared_8861_ = v_isSharedCheck_8868_;
                                        state = 88;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_8779_);
                                    crate::leanh::lean_dec_ref(v___x_8777_);
                                    crate::leanh::lean_dec(v_fvarId_8776_);
                                    crate::leanh::lean_dec(v_fvarId_8774_);
                                    if v_isShared_8782_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_8781_, 0, v_code_8363_);
                                        v___x_8876_ = v___x_8781_;
                                        state = 91;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_8877_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_8877_,
                                            0,
                                            v_code_8363_,
                                        );
                                        v___x_8876_ = v_reuseFailAlloc_8877_;
                                        state = 91;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            76 => {
                if v_isShared_8787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8786_, 5, v_a_8779_);
                    crate::leanh::lean_ctor_set(v___x_8786_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v___x_8786_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v___x_8786_, 0, v_fvarId_8774_);
                    v___x_8789_ = v___x_8786_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_8793_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 0, v_fvarId_8774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 1, v_i_8768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 2, v_offset_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8793_, 5, v_a_8779_);
                    v___x_8789_ = v_reuseFailAlloc_8793_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                if v_isShared_8782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8781_, 0, v___x_8789_);
                    v___x_8791_ = v___x_8781_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_8792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8792_, 0, v___x_8789_);
                    v___x_8791_ = v_reuseFailAlloc_8792_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_8791_;
            }
            79 => {
                if v_isShared_8804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8803_, 5, v_a_8779_);
                    crate::leanh::lean_ctor_set(v___x_8803_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v___x_8803_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v___x_8803_, 0, v_fvarId_8774_);
                    v___x_8806_ = v___x_8803_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_8810_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 0, v_fvarId_8774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 1, v_i_8768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 2, v_offset_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8810_, 5, v_a_8779_);
                    v___x_8806_ = v_reuseFailAlloc_8810_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_8782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8781_, 0, v___x_8806_);
                    v___x_8808_ = v___x_8781_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_8809_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8809_, 0, v___x_8806_);
                    v___x_8808_ = v_reuseFailAlloc_8809_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_8808_;
            }
            82 => {
                if v_isShared_8823_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8822_, 5, v_a_8779_);
                    crate::leanh::lean_ctor_set(v___x_8822_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v___x_8822_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v___x_8822_, 0, v_fvarId_8774_);
                    v___x_8825_ = v___x_8822_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_8829_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 0, v_fvarId_8774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 1, v_i_8768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 2, v_offset_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 5, v_a_8779_);
                    v___x_8825_ = v_reuseFailAlloc_8829_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_8782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8781_, 0, v___x_8825_);
                    v___x_8827_ = v___x_8781_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_8828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8828_, 0, v___x_8825_);
                    v___x_8827_ = v_reuseFailAlloc_8828_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_8827_;
            }
            85 => {
                if v_isShared_8842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8841_, 5, v_a_8779_);
                    crate::leanh::lean_ctor_set(v___x_8841_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v___x_8841_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v___x_8841_, 0, v_fvarId_8774_);
                    v___x_8844_ = v___x_8841_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_8848_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 0, v_fvarId_8774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 1, v_i_8768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 2, v_offset_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8848_, 5, v_a_8779_);
                    v___x_8844_ = v_reuseFailAlloc_8848_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                if v_isShared_8782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8781_, 0, v___x_8844_);
                    v___x_8846_ = v___x_8781_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_8847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8847_, 0, v___x_8844_);
                    v___x_8846_ = v_reuseFailAlloc_8847_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                return v___x_8846_;
            }
            88 => {
                if v_isShared_8861_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8860_, 5, v_a_8779_);
                    crate::leanh::lean_ctor_set(v___x_8860_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v___x_8860_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v___x_8860_, 0, v_fvarId_8774_);
                    v___x_8863_ = v___x_8860_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_8867_ = crate::leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 0, v_fvarId_8774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 1, v_i_8768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 2, v_offset_8769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 3, v_fvarId_8776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 4, v___x_8777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8867_, 5, v_a_8779_);
                    v___x_8863_ = v_reuseFailAlloc_8867_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_8782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8781_, 0, v___x_8863_);
                    v___x_8865_ = v___x_8781_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_8866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8866_, 0, v___x_8863_);
                    v___x_8865_ = v_reuseFailAlloc_8866_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                return v___x_8865_;
            }
            91 => {
                return v___x_8876_;
            }
            92 => {
                v___x_8929_ = lean_ptr_addr(v_fvarId_8885_);
                v___x_8930_ = lean_ptr_addr(v_fvarId_8889_);
                v___x_8931_ = lean_usize_dec_eq(v___x_8929_, v___x_8930_);
                if v___x_8931_ == 0 {
                    v___y_8896_ = v___x_8931_;
                    state = 93;
                    continue;
                } else {
                    v___x_8932_ = lean_nat_dec_eq(v_cidx_8886_, v_cidx_8886_);
                    v___y_8896_ = v___x_8932_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v___y_8896_ == 0 {
                    crate::leanh::lean_inc(v_cidx_8886_);
                    v_isSharedCheck_8906_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8906_ == 0 {
                        v_unused_8907_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_8907_);
                        v_unused_8908_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8908_);
                        v_unused_8909_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8909_);
                        v___x_8898_ = v_code_8363_;
                        v_isShared_8899_ = v_isSharedCheck_8906_;
                        state = 94;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8898_ = crate::leanh::lean_box(0);
                        v_isShared_8899_ = v_isSharedCheck_8906_;
                        state = 94;
                        continue;
                    }
                } else {
                    v___x_8910_ = lean_ptr_addr(v_k_8887_);
                    v___x_8911_ = lean_ptr_addr(v_a_8891_);
                    v___x_8912_ = lean_usize_dec_eq(v___x_8910_, v___x_8911_);
                    if v___x_8912_ == 0 {
                        crate::leanh::lean_inc(v_cidx_8886_);
                        v_isSharedCheck_8922_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8922_ == 0 {
                            v_unused_8923_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_8923_);
                            v_unused_8924_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_8924_);
                            v_unused_8925_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8925_);
                            v___x_8914_ = v_code_8363_;
                            v_isShared_8915_ = v_isSharedCheck_8922_;
                            state = 97;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8914_ = crate::leanh::lean_box(0);
                            v_isShared_8915_ = v_isSharedCheck_8922_;
                            state = 97;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_8891_);
                        crate::leanh::lean_dec(v_fvarId_8889_);
                        if v_isShared_8894_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8893_, 0, v_code_8363_);
                            v___x_8927_ = v___x_8893_;
                            state = 100;
                            continue;
                        } else {
                            v_reuseFailAlloc_8928_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8928_, 0, v_code_8363_);
                            v___x_8927_ = v_reuseFailAlloc_8928_;
                            state = 100;
                            continue;
                        }
                    }
                }
            }
            94 => {
                if v_isShared_8899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8898_, 2, v_a_8891_);
                    crate::leanh::lean_ctor_set(v___x_8898_, 0, v_fvarId_8889_);
                    v___x_8901_ = v___x_8898_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_8905_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8905_, 0, v_fvarId_8889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8905_, 1, v_cidx_8886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8905_, 2, v_a_8891_);
                    v___x_8901_ = v_reuseFailAlloc_8905_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_8894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8893_, 0, v___x_8901_);
                    v___x_8903_ = v___x_8893_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_8904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8904_, 0, v___x_8901_);
                    v___x_8903_ = v_reuseFailAlloc_8904_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_8903_;
            }
            97 => {
                if v_isShared_8915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8914_, 2, v_a_8891_);
                    crate::leanh::lean_ctor_set(v___x_8914_, 0, v_fvarId_8889_);
                    v___x_8917_ = v___x_8914_;
                    state = 98;
                    continue;
                } else {
                    v_reuseFailAlloc_8921_ = crate::leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8921_, 0, v_fvarId_8889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8921_, 1, v_cidx_8886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8921_, 2, v_a_8891_);
                    v___x_8917_ = v_reuseFailAlloc_8921_;
                    state = 98;
                    continue;
                }
            }
            98 => {
                if v_isShared_8894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8893_, 0, v___x_8917_);
                    v___x_8919_ = v___x_8893_;
                    state = 99;
                    continue;
                } else {
                    v_reuseFailAlloc_8920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8920_, 0, v___x_8917_);
                    v___x_8919_ = v_reuseFailAlloc_8920_;
                    state = 99;
                    continue;
                }
            }
            99 => {
                return v___x_8919_;
            }
            100 => {
                return v___x_8927_;
            }
            101 => {
                v___x_8981_ = lean_ptr_addr(v_fvarId_8935_);
                v___x_8982_ = lean_ptr_addr(v_fvarId_8941_);
                v___x_8983_ = lean_usize_dec_eq(v___x_8981_, v___x_8982_);
                if v___x_8983_ == 0 {
                    v___y_8948_ = v___x_8983_;
                    state = 102;
                    continue;
                } else {
                    v___x_8984_ = lean_nat_dec_eq(v_n_8936_, v_n_8936_);
                    v___y_8948_ = v___x_8984_;
                    state = 102;
                    continue;
                }
            }
            102 => {
                if v___y_8948_ == 0 {
                    crate::leanh::lean_inc(v_n_8936_);
                    v_isSharedCheck_8958_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8958_ == 0 {
                        v_unused_8959_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_8959_);
                        v_unused_8960_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_8960_);
                        v_unused_8961_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_8961_);
                        v___x_8950_ = v_code_8363_;
                        v_isShared_8951_ = v_isSharedCheck_8958_;
                        state = 103;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_8950_ = crate::leanh::lean_box(0);
                        v_isShared_8951_ = v_isSharedCheck_8958_;
                        state = 103;
                        continue;
                    }
                } else {
                    v___x_8962_ = lean_ptr_addr(v_k_8939_);
                    v___x_8963_ = lean_ptr_addr(v_a_8943_);
                    v___x_8964_ = lean_usize_dec_eq(v___x_8962_, v___x_8963_);
                    if v___x_8964_ == 0 {
                        crate::leanh::lean_inc(v_n_8936_);
                        v_isSharedCheck_8974_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8974_ == 0 {
                            v_unused_8975_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_8975_);
                            v_unused_8976_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_8976_);
                            v_unused_8977_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_8977_);
                            v___x_8966_ = v_code_8363_;
                            v_isShared_8967_ = v_isSharedCheck_8974_;
                            state = 106;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_8966_ = crate::leanh::lean_box(0);
                            v_isShared_8967_ = v_isSharedCheck_8974_;
                            state = 106;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_8943_);
                        crate::leanh::lean_dec(v_fvarId_8941_);
                        if v_isShared_8946_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_8945_, 0, v_code_8363_);
                            v___x_8979_ = v___x_8945_;
                            state = 109;
                            continue;
                        } else {
                            v_reuseFailAlloc_8980_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_8980_, 0, v_code_8363_);
                            v___x_8979_ = v_reuseFailAlloc_8980_;
                            state = 109;
                            continue;
                        }
                    }
                }
            }
            103 => {
                if v_isShared_8951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8950_, 2, v_a_8943_);
                    crate::leanh::lean_ctor_set(v___x_8950_, 0, v_fvarId_8941_);
                    v___x_8953_ = v___x_8950_;
                    state = 104;
                    continue;
                } else {
                    v_reuseFailAlloc_8957_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8957_, 0, v_fvarId_8941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8957_, 1, v_n_8936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8957_, 2, v_a_8943_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8957_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_8937_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8957_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_8938_,
                    );
                    v___x_8953_ = v_reuseFailAlloc_8957_;
                    state = 104;
                    continue;
                }
            }
            104 => {
                if v_isShared_8946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8945_, 0, v___x_8953_);
                    v___x_8955_ = v___x_8945_;
                    state = 105;
                    continue;
                } else {
                    v_reuseFailAlloc_8956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8956_, 0, v___x_8953_);
                    v___x_8955_ = v_reuseFailAlloc_8956_;
                    state = 105;
                    continue;
                }
            }
            105 => {
                return v___x_8955_;
            }
            106 => {
                if v_isShared_8967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8966_, 2, v_a_8943_);
                    crate::leanh::lean_ctor_set(v___x_8966_, 0, v_fvarId_8941_);
                    v___x_8969_ = v___x_8966_;
                    state = 107;
                    continue;
                } else {
                    v_reuseFailAlloc_8973_ = crate::leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8973_, 0, v_fvarId_8941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8973_, 1, v_n_8936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8973_, 2, v_a_8943_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8973_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_check_8937_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8973_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_8938_,
                    );
                    v___x_8969_ = v_reuseFailAlloc_8973_;
                    state = 107;
                    continue;
                }
            }
            107 => {
                if v_isShared_8946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8945_, 0, v___x_8969_);
                    v___x_8971_ = v___x_8945_;
                    state = 108;
                    continue;
                } else {
                    v_reuseFailAlloc_8972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8972_, 0, v___x_8969_);
                    v___x_8971_ = v_reuseFailAlloc_8972_;
                    state = 108;
                    continue;
                }
            }
            108 => {
                return v___x_8971_;
            }
            109 => {
                return v___x_8979_;
            }
            110 => {
                v___x_9052_ = lean_ptr_addr(v_fvarId_8987_);
                v___x_9053_ = lean_ptr_addr(v_fvarId_8994_);
                v___x_9054_ = lean_usize_dec_eq(v___x_9052_, v___x_9053_);
                if v___x_9054_ == 0 {
                    v___y_9001_ = v___x_9054_;
                    state = 111;
                    continue;
                } else {
                    v___x_9055_ = lean_nat_dec_eq(v_n_8988_, v_n_8988_);
                    v___y_9001_ = v___x_9055_;
                    state = 111;
                    continue;
                }
            }
            111 => {
                if v___y_9001_ == 0 {
                    crate::leanh::lean_inc(v_objs_x3f_8991_);
                    crate::leanh::lean_inc(v_n_8988_);
                    v_isSharedCheck_9011_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_9011_ == 0 {
                        v_unused_9012_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                        crate::leanh::lean_dec(v_unused_9012_);
                        v_unused_9013_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                        crate::leanh::lean_dec(v_unused_9013_);
                        v_unused_9014_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_9014_);
                        v_unused_9015_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_9015_);
                        v___x_9003_ = v_code_8363_;
                        v_isShared_9004_ = v_isSharedCheck_9011_;
                        state = 112;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_9003_ = crate::leanh::lean_box(0);
                        v_isShared_9004_ = v_isSharedCheck_9011_;
                        state = 112;
                        continue;
                    }
                } else {
                    v___x_9016_ = lean_ptr_addr(v_objs_x3f_8991_);
                    v___x_9017_ = lean_usize_dec_eq(v___x_9016_, v___x_9016_);
                    if v___x_9017_ == 0 {
                        crate::leanh::lean_inc(v_objs_x3f_8991_);
                        crate::leanh::lean_inc(v_n_8988_);
                        v_isSharedCheck_9027_ =
                            (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_9027_ == 0 {
                            v_unused_9028_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                            crate::leanh::lean_dec(v_unused_9028_);
                            v_unused_9029_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                            crate::leanh::lean_dec(v_unused_9029_);
                            v_unused_9030_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                            crate::leanh::lean_dec(v_unused_9030_);
                            v_unused_9031_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                            crate::leanh::lean_dec(v_unused_9031_);
                            v___x_9019_ = v_code_8363_;
                            v_isShared_9020_ = v_isSharedCheck_9027_;
                            state = 115;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_8363_);
                            v___x_9019_ = crate::leanh::lean_box(0);
                            v_isShared_9020_ = v_isSharedCheck_9027_;
                            state = 115;
                            continue;
                        }
                    } else {
                        v___x_9032_ = lean_ptr_addr(v_k_8992_);
                        v___x_9033_ = lean_ptr_addr(v_a_8996_);
                        v___x_9034_ = lean_usize_dec_eq(v___x_9032_, v___x_9033_);
                        if v___x_9034_ == 0 {
                            crate::leanh::lean_inc(v_objs_x3f_8991_);
                            crate::leanh::lean_inc(v_n_8988_);
                            v_isSharedCheck_9044_ =
                                (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_9044_ == 0 {
                                v_unused_9045_ = crate::leanh::lean_ctor_get(v_code_8363_, 3);
                                crate::leanh::lean_dec(v_unused_9045_);
                                v_unused_9046_ = crate::leanh::lean_ctor_get(v_code_8363_, 2);
                                crate::leanh::lean_dec(v_unused_9046_);
                                v_unused_9047_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                                crate::leanh::lean_dec(v_unused_9047_);
                                v_unused_9048_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                                crate::leanh::lean_dec(v_unused_9048_);
                                v___x_9036_ = v_code_8363_;
                                v_isShared_9037_ = v_isSharedCheck_9044_;
                                state = 118;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_code_8363_);
                                v___x_9036_ = crate::leanh::lean_box(0);
                                v_isShared_9037_ = v_isSharedCheck_9044_;
                                state = 118;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_8996_);
                            crate::leanh::lean_dec(v_fvarId_8994_);
                            if v_isShared_8999_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_8998_, 0, v_code_8363_);
                                v___x_9050_ = v___x_8998_;
                                state = 121;
                                continue;
                            } else {
                                v_reuseFailAlloc_9051_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_9051_,
                                    0,
                                    v_code_8363_,
                                );
                                v___x_9050_ = v_reuseFailAlloc_9051_;
                                state = 121;
                                continue;
                            }
                        }
                    }
                }
            }
            112 => {
                if v_isShared_9004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9003_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set(v___x_9003_, 0, v_fvarId_8994_);
                    v___x_9006_ = v___x_9003_;
                    state = 113;
                    continue;
                } else {
                    v_reuseFailAlloc_9010_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9010_, 0, v_fvarId_8994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9010_, 1, v_n_8988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9010_, 2, v_objs_x3f_8991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9010_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9006_ = v_reuseFailAlloc_9010_;
                    state = 113;
                    continue;
                }
            }
            113 => {
                if v_isShared_8999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8998_, 0, v___x_9006_);
                    v___x_9008_ = v___x_8998_;
                    state = 114;
                    continue;
                } else {
                    v_reuseFailAlloc_9009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9009_, 0, v___x_9006_);
                    v___x_9008_ = v_reuseFailAlloc_9009_;
                    state = 114;
                    continue;
                }
            }
            114 => {
                return v___x_9008_;
            }
            115 => {
                if v_isShared_9020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9019_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set(v___x_9019_, 0, v_fvarId_8994_);
                    v___x_9022_ = v___x_9019_;
                    state = 116;
                    continue;
                } else {
                    v_reuseFailAlloc_9026_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9026_, 0, v_fvarId_8994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9026_, 1, v_n_8988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9026_, 2, v_objs_x3f_8991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9026_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9026_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9026_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9022_ = v_reuseFailAlloc_9026_;
                    state = 116;
                    continue;
                }
            }
            116 => {
                if v_isShared_8999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8998_, 0, v___x_9022_);
                    v___x_9024_ = v___x_8998_;
                    state = 117;
                    continue;
                } else {
                    v_reuseFailAlloc_9025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9025_, 0, v___x_9022_);
                    v___x_9024_ = v_reuseFailAlloc_9025_;
                    state = 117;
                    continue;
                }
            }
            117 => {
                return v___x_9024_;
            }
            118 => {
                if v_isShared_9037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9036_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set(v___x_9036_, 0, v_fvarId_8994_);
                    v___x_9039_ = v___x_9036_;
                    state = 119;
                    continue;
                } else {
                    v_reuseFailAlloc_9043_ = crate::leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9043_, 0, v_fvarId_8994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9043_, 1, v_n_8988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9043_, 2, v_objs_x3f_8991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9043_, 3, v_a_8996_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_9043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9039_ = v_reuseFailAlloc_9043_;
                    state = 119;
                    continue;
                }
            }
            119 => {
                if v_isShared_8999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8998_, 0, v___x_9039_);
                    v___x_9041_ = v___x_8998_;
                    state = 120;
                    continue;
                } else {
                    v_reuseFailAlloc_9042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9042_, 0, v___x_9039_);
                    v___x_9041_ = v_reuseFailAlloc_9042_;
                    state = 120;
                    continue;
                }
            }
            120 => {
                return v___x_9041_;
            }
            121 => {
                return v___x_9050_;
            }
            122 => {
                v___x_9084_ = lean_ptr_addr(v_fvarId_9058_);
                v___x_9085_ = lean_ptr_addr(v_fvarId_9061_);
                v___x_9086_ = lean_usize_dec_eq(v___x_9084_, v___x_9085_);
                if v___x_9086_ == 0 {
                    v___y_9068_ = v___x_9086_;
                    state = 123;
                    continue;
                } else {
                    v___x_9087_ = lean_ptr_addr(v_k_9059_);
                    v___x_9088_ = lean_ptr_addr(v_a_9063_);
                    v___x_9089_ = lean_usize_dec_eq(v___x_9087_, v___x_9088_);
                    v___y_9068_ = v___x_9089_;
                    state = 123;
                    continue;
                }
            }
            123 => {
                if v___y_9068_ == 0 {
                    v_isSharedCheck_9078_ = (!crate::leanh::lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_9078_ == 0 {
                        v_unused_9079_ = crate::leanh::lean_ctor_get(v_code_8363_, 1);
                        crate::leanh::lean_dec(v_unused_9079_);
                        v_unused_9080_ = crate::leanh::lean_ctor_get(v_code_8363_, 0);
                        crate::leanh::lean_dec(v_unused_9080_);
                        v___x_9070_ = v_code_8363_;
                        v_isShared_9071_ = v_isSharedCheck_9078_;
                        state = 124;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_8363_);
                        v___x_9070_ = crate::leanh::lean_box(0);
                        v_isShared_9071_ = v_isSharedCheck_9078_;
                        state = 124;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_9063_);
                    crate::leanh::lean_dec(v_fvarId_9061_);
                    if v_isShared_9066_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_9065_, 0, v_code_8363_);
                        v___x_9082_ = v___x_9065_;
                        state = 127;
                        continue;
                    } else {
                        v_reuseFailAlloc_9083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_9083_, 0, v_code_8363_);
                        v___x_9082_ = v_reuseFailAlloc_9083_;
                        state = 127;
                        continue;
                    }
                }
            }
            124 => {
                if v_isShared_9071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9070_, 1, v_a_9063_);
                    crate::leanh::lean_ctor_set(v___x_9070_, 0, v_fvarId_9061_);
                    v___x_9073_ = v___x_9070_;
                    state = 125;
                    continue;
                } else {
                    v_reuseFailAlloc_9077_ = crate::leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9077_, 0, v_fvarId_9061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9077_, 1, v_a_9063_);
                    v___x_9073_ = v_reuseFailAlloc_9077_;
                    state = 125;
                    continue;
                }
            }
            125 => {
                if v_isShared_9066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9065_, 0, v___x_9073_);
                    v___x_9075_ = v___x_9065_;
                    state = 126;
                    continue;
                } else {
                    v_reuseFailAlloc_9076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9076_, 0, v___x_9073_);
                    v___x_9075_ = v_reuseFailAlloc_9076_;
                    state = 126;
                    continue;
                }
            }
            126 => {
                return v___x_9075_;
            }
            127 => {
                return v___x_9082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDeclImp(
    mut v_pu_9092_: u8,
    mut v_t_9093_: u8,
    mut v_decl_9094_: *mut crate::leanh::LeanObject,
    mut v_a_9095_: *mut crate::leanh::LeanObject,
    mut v_a_9096_: *mut crate::leanh::LeanObject,
    mut v_a_9097_: *mut crate::leanh::LeanObject,
    mut v_a_9098_: *mut crate::leanh::LeanObject,
    mut v_a_9099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_9101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_9102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_9103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9113_: u8 = 0;
    let mut v___x_9115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9117_: u8 = 0;
    let mut v_a_9118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9121_: u8 = 0;
    let mut v___x_9123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_9101_ = crate::leanh::lean_ctor_get(v_decl_9094_, 2);
                v_type_9102_ = crate::leanh::lean_ctor_get(v_decl_9094_, 3);
                v_value_9103_ = crate::leanh::lean_ctor_get(v_decl_9094_, 4);
                crate::leanh::lean_inc_ref(v_type_9102_);
                v___x_9104_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v_pu_9092_,
                        v_a_9095_,
                        v_t_9093_,
                        v_type_9102_,
                    );
                crate::leanh::lean_inc_ref(v_params_9101_);
                v___x_9105_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_9092_, v_t_9093_, v_params_9101_, v_a_9095_, v_a_9096_, v_a_9097_, v_a_9098_, v_a_9099_);
                if crate::leanh::lean_obj_tag(v___x_9105_) == 0 {
                    v_a_9106_ = crate::leanh::lean_ctor_get(v___x_9105_, 0);
                    crate::leanh::lean_inc(v_a_9106_);
                    crate::leanh::lean_dec_ref_known(v___x_9105_, 1);
                    crate::leanh::lean_inc_ref(v_value_9103_);
                    v___x_9107_ = l_Lean_Compiler_LCNF_normCodeImp(
                        v_pu_9092_,
                        v_t_9093_,
                        v_value_9103_,
                        v_a_9095_,
                        v_a_9096_,
                        v_a_9097_,
                        v_a_9098_,
                        v_a_9099_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_9107_) == 0 {
                        v_a_9108_ = crate::leanh::lean_ctor_get(v___x_9107_, 0);
                        crate::leanh::lean_inc(v_a_9108_);
                        crate::leanh::lean_dec_ref_known(v___x_9107_, 1);
                        v___x_9109_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_9092_, v_decl_9094_, v___x_9104_, v_a_9106_, v_a_9108_, v_a_9097_);
                        return v___x_9109_;
                    } else {
                        crate::leanh::lean_dec(v_a_9106_);
                        crate::leanh::lean_dec_ref(v___x_9104_);
                        crate::leanh::lean_dec_ref(v_decl_9094_);
                        v_a_9110_ = crate::leanh::lean_ctor_get(v___x_9107_, 0);
                        v_isSharedCheck_9117_ =
                            (!crate::leanh::lean_is_exclusive(v___x_9107_)) as u8;
                        if v_isSharedCheck_9117_ == 0 {
                            v___x_9112_ = v___x_9107_;
                            v_isShared_9113_ = v_isSharedCheck_9117_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_9110_);
                            crate::leanh::lean_dec(v___x_9107_);
                            v___x_9112_ = crate::leanh::lean_box(0);
                            v_isShared_9113_ = v_isSharedCheck_9117_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_9104_);
                    crate::leanh::lean_dec_ref(v_decl_9094_);
                    v_a_9118_ = crate::leanh::lean_ctor_get(v___x_9105_, 0);
                    v_isSharedCheck_9125_ = (!crate::leanh::lean_is_exclusive(v___x_9105_)) as u8;
                    if v_isSharedCheck_9125_ == 0 {
                        v___x_9120_ = v___x_9105_;
                        v_isShared_9121_ = v_isSharedCheck_9125_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_9118_);
                        crate::leanh::lean_dec(v___x_9105_);
                        v___x_9120_ = crate::leanh::lean_box(0);
                        v_isShared_9121_ = v_isSharedCheck_9125_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9113_ == 0 {
                    v___x_9115_ = v___x_9112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9116_, 0, v_a_9110_);
                    v___x_9115_ = v_reuseFailAlloc_9116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9115_;
            }
            3 => {
                if v_isShared_9121_ == 0 {
                    v___x_9123_ = v___x_9120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9124_, 0, v_a_9118_);
                    v___x_9123_ = v_reuseFailAlloc_9124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDeclImp___boxed(
    mut v_pu_9126_: *mut crate::leanh::LeanObject,
    mut v_t_9127_: *mut crate::leanh::LeanObject,
    mut v_decl_9128_: *mut crate::leanh::LeanObject,
    mut v_a_9129_: *mut crate::leanh::LeanObject,
    mut v_a_9130_: *mut crate::leanh::LeanObject,
    mut v_a_9131_: *mut crate::leanh::LeanObject,
    mut v_a_9132_: *mut crate::leanh::LeanObject,
    mut v_a_9133_: *mut crate::leanh::LeanObject,
    mut v_a_9134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9135_: u8 = 0;
    let mut v_t_boxed_9136_: u8 = 0;
    let mut v_res_9137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9135_ = (crate::leanh::lean_unbox(v_pu_9126_) as u8);
    v_t_boxed_9136_ = (crate::leanh::lean_unbox(v_t_9127_) as u8);
    v_res_9137_ = l_Lean_Compiler_LCNF_normFunDeclImp(
        v_pu_boxed_9135_,
        v_t_boxed_9136_,
        v_decl_9128_,
        v_a_9129_,
        v_a_9130_,
        v_a_9131_,
        v_a_9132_,
        v_a_9133_,
    );
    crate::leanh::lean_dec(v_a_9133_);
    crate::leanh::lean_dec_ref(v_a_9132_);
    crate::leanh::lean_dec(v_a_9131_);
    crate::leanh::lean_dec_ref(v_a_9130_);
    crate::leanh::lean_dec_ref(v_a_9129_);
    return v_res_9137_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(
    mut v_pu_9138_: *mut crate::leanh::LeanObject,
    mut v_t_9139_: *mut crate::leanh::LeanObject,
    mut v_i_9140_: *mut crate::leanh::LeanObject,
    mut v_as_9141_: *mut crate::leanh::LeanObject,
    mut v___y_9142_: *mut crate::leanh::LeanObject,
    mut v___y_9143_: *mut crate::leanh::LeanObject,
    mut v___y_9144_: *mut crate::leanh::LeanObject,
    mut v___y_9145_: *mut crate::leanh::LeanObject,
    mut v___y_9146_: *mut crate::leanh::LeanObject,
    mut v___y_9147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9148_: u8 = 0;
    let mut v_t_boxed_9149_: u8 = 0;
    let mut v_res_9150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9148_ = (crate::leanh::lean_unbox(v_pu_9138_) as u8);
    v_t_boxed_9149_ = (crate::leanh::lean_unbox(v_t_9139_) as u8);
    v_res_9150_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_9148_, v_t_boxed_9149_, v_i_9140_, v_as_9141_, v___y_9142_, v___y_9143_, v___y_9144_, v___y_9145_, v___y_9146_);
    crate::leanh::lean_dec(v___y_9146_);
    crate::leanh::lean_dec_ref(v___y_9145_);
    crate::leanh::lean_dec(v___y_9144_);
    crate::leanh::lean_dec_ref(v___y_9143_);
    crate::leanh::lean_dec_ref(v___y_9142_);
    return v_res_9150_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCodeImp___boxed(
    mut v_pu_9151_: *mut crate::leanh::LeanObject,
    mut v_t_9152_: *mut crate::leanh::LeanObject,
    mut v_code_9153_: *mut crate::leanh::LeanObject,
    mut v_a_9154_: *mut crate::leanh::LeanObject,
    mut v_a_9155_: *mut crate::leanh::LeanObject,
    mut v_a_9156_: *mut crate::leanh::LeanObject,
    mut v_a_9157_: *mut crate::leanh::LeanObject,
    mut v_a_9158_: *mut crate::leanh::LeanObject,
    mut v_a_9159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9160_: u8 = 0;
    let mut v_t_boxed_9161_: u8 = 0;
    let mut v_res_9162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9160_ = (crate::leanh::lean_unbox(v_pu_9151_) as u8);
    v_t_boxed_9161_ = (crate::leanh::lean_unbox(v_t_9152_) as u8);
    v_res_9162_ = l_Lean_Compiler_LCNF_normCodeImp(
        v_pu_boxed_9160_,
        v_t_boxed_9161_,
        v_code_9153_,
        v_a_9154_,
        v_a_9155_,
        v_a_9156_,
        v_a_9157_,
        v_a_9158_,
    );
    crate::leanh::lean_dec(v_a_9158_);
    crate::leanh::lean_dec_ref(v_a_9157_);
    crate::leanh::lean_dec(v_a_9156_);
    crate::leanh::lean_dec_ref(v_a_9155_);
    crate::leanh::lean_dec_ref(v_a_9154_);
    return v_res_9162_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(
    mut v_pu_9163_: u8,
    mut v_t_9164_: u8,
    mut v_pu_9165_: u8,
    mut v_t_9166_: u8,
    mut v_decl_9167_: *mut crate::leanh::LeanObject,
    mut v___y_9168_: *mut crate::leanh::LeanObject,
    mut v___y_9169_: *mut crate::leanh::LeanObject,
    mut v___y_9170_: *mut crate::leanh::LeanObject,
    mut v___y_9171_: *mut crate::leanh::LeanObject,
    mut v___y_9172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9174_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(
            v_pu_9165_,
            v_t_9166_,
            v_decl_9167_,
            v___y_9168_,
            v___y_9170_,
        );
    return v___x_9174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___boxed(
    mut v_pu_9175_: *mut crate::leanh::LeanObject,
    mut v_t_9176_: *mut crate::leanh::LeanObject,
    mut v_pu_9177_: *mut crate::leanh::LeanObject,
    mut v_t_9178_: *mut crate::leanh::LeanObject,
    mut v_decl_9179_: *mut crate::leanh::LeanObject,
    mut v___y_9180_: *mut crate::leanh::LeanObject,
    mut v___y_9181_: *mut crate::leanh::LeanObject,
    mut v___y_9182_: *mut crate::leanh::LeanObject,
    mut v___y_9183_: *mut crate::leanh::LeanObject,
    mut v___y_9184_: *mut crate::leanh::LeanObject,
    mut v___y_9185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9186_: u8 = 0;
    let mut v_t_boxed_9187_: u8 = 0;
    let mut v_pu_boxed_9188_: u8 = 0;
    let mut v_t_boxed_9189_: u8 = 0;
    let mut v_res_9190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9186_ = (crate::leanh::lean_unbox(v_pu_9175_) as u8);
    v_t_boxed_9187_ = (crate::leanh::lean_unbox(v_t_9176_) as u8);
    v_pu_boxed_9188_ = (crate::leanh::lean_unbox(v_pu_9177_) as u8);
    v_t_boxed_9189_ = (crate::leanh::lean_unbox(v_t_9178_) as u8);
    v_res_9190_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(
        v_pu_boxed_9186_,
        v_t_boxed_9187_,
        v_pu_boxed_9188_,
        v_t_boxed_9189_,
        v_decl_9179_,
        v___y_9180_,
        v___y_9181_,
        v___y_9182_,
        v___y_9183_,
        v___y_9184_,
    );
    crate::leanh::lean_dec(v___y_9184_);
    crate::leanh::lean_dec_ref(v___y_9183_);
    crate::leanh::lean_dec(v___y_9182_);
    crate::leanh::lean_dec_ref(v___y_9181_);
    crate::leanh::lean_dec_ref(v___y_9180_);
    return v_res_9190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(
    mut v_pu_9191_: u8,
    mut v_t_9192_: u8,
    mut v_pu_9193_: u8,
    mut v_t_9194_: u8,
    mut v_args_9195_: *mut crate::leanh::LeanObject,
    mut v___y_9196_: *mut crate::leanh::LeanObject,
    mut v___y_9197_: *mut crate::leanh::LeanObject,
    mut v___y_9198_: *mut crate::leanh::LeanObject,
    mut v___y_9199_: *mut crate::leanh::LeanObject,
    mut v___y_9200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9202_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(
            v_pu_9193_,
            v_t_9194_,
            v_args_9195_,
            v___y_9196_,
        );
    return v___x_9202_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___boxed(
    mut v_pu_9203_: *mut crate::leanh::LeanObject,
    mut v_t_9204_: *mut crate::leanh::LeanObject,
    mut v_pu_9205_: *mut crate::leanh::LeanObject,
    mut v_t_9206_: *mut crate::leanh::LeanObject,
    mut v_args_9207_: *mut crate::leanh::LeanObject,
    mut v___y_9208_: *mut crate::leanh::LeanObject,
    mut v___y_9209_: *mut crate::leanh::LeanObject,
    mut v___y_9210_: *mut crate::leanh::LeanObject,
    mut v___y_9211_: *mut crate::leanh::LeanObject,
    mut v___y_9212_: *mut crate::leanh::LeanObject,
    mut v___y_9213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9214_: u8 = 0;
    let mut v_t_boxed_9215_: u8 = 0;
    let mut v_pu_boxed_9216_: u8 = 0;
    let mut v_t_boxed_9217_: u8 = 0;
    let mut v_res_9218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9214_ = (crate::leanh::lean_unbox(v_pu_9203_) as u8);
    v_t_boxed_9215_ = (crate::leanh::lean_unbox(v_t_9204_) as u8);
    v_pu_boxed_9216_ = (crate::leanh::lean_unbox(v_pu_9205_) as u8);
    v_t_boxed_9217_ = (crate::leanh::lean_unbox(v_t_9206_) as u8);
    v_res_9218_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(
        v_pu_boxed_9214_,
        v_t_boxed_9215_,
        v_pu_boxed_9216_,
        v_t_boxed_9217_,
        v_args_9207_,
        v___y_9208_,
        v___y_9209_,
        v___y_9210_,
        v___y_9211_,
        v___y_9212_,
    );
    crate::leanh::lean_dec(v___y_9212_);
    crate::leanh::lean_dec_ref(v___y_9211_);
    crate::leanh::lean_dec(v___y_9210_);
    crate::leanh::lean_dec_ref(v___y_9209_);
    crate::leanh::lean_dec_ref(v___y_9208_);
    return v_res_9218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(
    mut v_pu_9219_: u8,
    mut v_t_9220_: u8,
    mut v_pu_9221_: u8,
    mut v_t_9222_: u8,
    mut v_ps_9223_: *mut crate::leanh::LeanObject,
    mut v___y_9224_: *mut crate::leanh::LeanObject,
    mut v___y_9225_: *mut crate::leanh::LeanObject,
    mut v___y_9226_: *mut crate::leanh::LeanObject,
    mut v___y_9227_: *mut crate::leanh::LeanObject,
    mut v___y_9228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9230_ =
        l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(
            v_pu_9221_,
            v_t_9222_,
            v_ps_9223_,
            v___y_9224_,
            v___y_9225_,
            v___y_9226_,
            v___y_9227_,
            v___y_9228_,
        );
    return v___x_9230_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___boxed(
    mut v_pu_9231_: *mut crate::leanh::LeanObject,
    mut v_t_9232_: *mut crate::leanh::LeanObject,
    mut v_pu_9233_: *mut crate::leanh::LeanObject,
    mut v_t_9234_: *mut crate::leanh::LeanObject,
    mut v_ps_9235_: *mut crate::leanh::LeanObject,
    mut v___y_9236_: *mut crate::leanh::LeanObject,
    mut v___y_9237_: *mut crate::leanh::LeanObject,
    mut v___y_9238_: *mut crate::leanh::LeanObject,
    mut v___y_9239_: *mut crate::leanh::LeanObject,
    mut v___y_9240_: *mut crate::leanh::LeanObject,
    mut v___y_9241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9242_: u8 = 0;
    let mut v_t_boxed_9243_: u8 = 0;
    let mut v_pu_boxed_9244_: u8 = 0;
    let mut v_t_boxed_9245_: u8 = 0;
    let mut v_res_9246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9242_ = (crate::leanh::lean_unbox(v_pu_9231_) as u8);
    v_t_boxed_9243_ = (crate::leanh::lean_unbox(v_t_9232_) as u8);
    v_pu_boxed_9244_ = (crate::leanh::lean_unbox(v_pu_9233_) as u8);
    v_t_boxed_9245_ = (crate::leanh::lean_unbox(v_t_9234_) as u8);
    v_res_9246_ =
        l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(
            v_pu_boxed_9242_,
            v_t_boxed_9243_,
            v_pu_boxed_9244_,
            v_t_boxed_9245_,
            v_ps_9235_,
            v___y_9236_,
            v___y_9237_,
            v___y_9238_,
            v___y_9239_,
            v___y_9240_,
        );
    crate::leanh::lean_dec(v___y_9240_);
    crate::leanh::lean_dec_ref(v___y_9239_);
    crate::leanh::lean_dec(v___y_9238_);
    crate::leanh::lean_dec_ref(v___y_9237_);
    crate::leanh::lean_dec_ref(v___y_9236_);
    return v_res_9246_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(
    mut v_pu_9247_: u8,
    mut v_t_9248_: u8,
    mut v_i_9249_: *mut crate::leanh::LeanObject,
    mut v_as_9250_: *mut crate::leanh::LeanObject,
    mut v___y_9251_: *mut crate::leanh::LeanObject,
    mut v___y_9252_: *mut crate::leanh::LeanObject,
    mut v___y_9253_: *mut crate::leanh::LeanObject,
    mut v___y_9254_: *mut crate::leanh::LeanObject,
    mut v___y_9255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9257_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_9247_, v_t_9248_, v_i_9249_, v_as_9250_, v___y_9251_, v___y_9253_);
    return v___x_9257_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(
    mut v_pu_9258_: *mut crate::leanh::LeanObject,
    mut v_t_9259_: *mut crate::leanh::LeanObject,
    mut v_i_9260_: *mut crate::leanh::LeanObject,
    mut v_as_9261_: *mut crate::leanh::LeanObject,
    mut v___y_9262_: *mut crate::leanh::LeanObject,
    mut v___y_9263_: *mut crate::leanh::LeanObject,
    mut v___y_9264_: *mut crate::leanh::LeanObject,
    mut v___y_9265_: *mut crate::leanh::LeanObject,
    mut v___y_9266_: *mut crate::leanh::LeanObject,
    mut v___y_9267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9268_: u8 = 0;
    let mut v_t_boxed_9269_: u8 = 0;
    let mut v_res_9270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9268_ = (crate::leanh::lean_unbox(v_pu_9258_) as u8);
    v_t_boxed_9269_ = (crate::leanh::lean_unbox(v_t_9259_) as u8);
    v_res_9270_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_9268_, v_t_boxed_9269_, v_i_9260_, v_as_9261_, v___y_9262_, v___y_9263_, v___y_9264_, v___y_9265_, v___y_9266_);
    crate::leanh::lean_dec(v___y_9266_);
    crate::leanh::lean_dec_ref(v___y_9265_);
    crate::leanh::lean_dec(v___y_9264_);
    crate::leanh::lean_dec_ref(v___y_9263_);
    crate::leanh::lean_dec_ref(v___y_9262_);
    return v_res_9270_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(
    mut v_pu_9271_: u8,
    mut v_t_9272_: u8,
    mut v_decl_9273_: *mut crate::leanh::LeanObject,
    mut v_inst_9274_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_9275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9276_ = crate::leanh::lean_box((v_pu_9271_) as usize);
    v___x_9277_ = crate::leanh::lean_box((v_t_9272_) as usize);
    v___x_9278_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDeclImp___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_9278_, 0, v___x_9276_);
    crate::leanh::lean_closure_set(v___x_9278_, 1, v___x_9277_);
    crate::leanh::lean_closure_set(v___x_9278_, 2, v_decl_9273_);
    crate::leanh::lean_closure_set(v___x_9278_, 3, v_____do__lift_9275_);
    v___x_9279_ = crate::leanh::lean_apply_2(v_inst_9274_, crate::leanh::lean_box(0), v___x_9278_);
    return v___x_9279_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(
    mut v_pu_9280_: *mut crate::leanh::LeanObject,
    mut v_t_9281_: *mut crate::leanh::LeanObject,
    mut v_decl_9282_: *mut crate::leanh::LeanObject,
    mut v_inst_9283_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_9284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9285_: u8 = 0;
    let mut v_t_boxed_9286_: u8 = 0;
    let mut v_res_9287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9285_ = (crate::leanh::lean_unbox(v_pu_9280_) as u8);
    v_t_boxed_9286_ = (crate::leanh::lean_unbox(v_t_9281_) as u8);
    v_res_9287_ = l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(
        v_pu_boxed_9285_,
        v_t_boxed_9286_,
        v_decl_9282_,
        v_inst_9283_,
        v_____do__lift_9284_,
    );
    return v_res_9287_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg(
    mut v_pu_9288_: u8,
    mut v_t_9289_: u8,
    mut v_inst_9290_: *mut crate::leanh::LeanObject,
    mut v_inst_9291_: *mut crate::leanh::LeanObject,
    mut v_inst_9292_: *mut crate::leanh::LeanObject,
    mut v_decl_9293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_9294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_9294_ = crate::leanh::lean_ctor_get(v_inst_9291_, 1);
    crate::leanh::lean_inc(v_toBind_9294_);
    crate::leanh::lean_dec_ref(v_inst_9291_);
    v___x_9295_ = crate::leanh::lean_box((v_pu_9288_) as usize);
    v___x_9296_ = crate::leanh::lean_box((v_t_9289_) as usize);
    v___f_9297_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_9297_, 0, v___x_9295_);
    crate::leanh::lean_closure_set(v___f_9297_, 1, v___x_9296_);
    crate::leanh::lean_closure_set(v___f_9297_, 2, v_decl_9293_);
    crate::leanh::lean_closure_set(v___f_9297_, 3, v_inst_9290_);
    v___x_9298_ = crate::leanh::lean_apply_4(
        v_toBind_9294_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_9292_,
        v___f_9297_,
    );
    return v___x_9298_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(
    mut v_pu_9299_: *mut crate::leanh::LeanObject,
    mut v_t_9300_: *mut crate::leanh::LeanObject,
    mut v_inst_9301_: *mut crate::leanh::LeanObject,
    mut v_inst_9302_: *mut crate::leanh::LeanObject,
    mut v_inst_9303_: *mut crate::leanh::LeanObject,
    mut v_decl_9304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9305_: u8 = 0;
    let mut v_t_boxed_9306_: u8 = 0;
    let mut v_res_9307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9305_ = (crate::leanh::lean_unbox(v_pu_9299_) as u8);
    v_t_boxed_9306_ = (crate::leanh::lean_unbox(v_t_9300_) as u8);
    v_res_9307_ = l_Lean_Compiler_LCNF_normFunDecl___redArg(
        v_pu_boxed_9305_,
        v_t_boxed_9306_,
        v_inst_9301_,
        v_inst_9302_,
        v_inst_9303_,
        v_decl_9304_,
    );
    return v_res_9307_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl(
    mut v_m_9308_: *mut crate::leanh::LeanObject,
    mut v_pu_9309_: u8,
    mut v_t_9310_: u8,
    mut v_inst_9311_: *mut crate::leanh::LeanObject,
    mut v_inst_9312_: *mut crate::leanh::LeanObject,
    mut v_inst_9313_: *mut crate::leanh::LeanObject,
    mut v_decl_9314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_9315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_9315_ = crate::leanh::lean_ctor_get(v_inst_9312_, 1);
    crate::leanh::lean_inc(v_toBind_9315_);
    crate::leanh::lean_dec_ref(v_inst_9312_);
    v___x_9316_ = crate::leanh::lean_box((v_pu_9309_) as usize);
    v___x_9317_ = crate::leanh::lean_box((v_t_9310_) as usize);
    v___f_9318_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_9318_, 0, v___x_9316_);
    crate::leanh::lean_closure_set(v___f_9318_, 1, v___x_9317_);
    crate::leanh::lean_closure_set(v___f_9318_, 2, v_decl_9314_);
    crate::leanh::lean_closure_set(v___f_9318_, 3, v_inst_9311_);
    v___x_9319_ = crate::leanh::lean_apply_4(
        v_toBind_9315_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_9313_,
        v___f_9318_,
    );
    return v___x_9319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___boxed(
    mut v_m_9320_: *mut crate::leanh::LeanObject,
    mut v_pu_9321_: *mut crate::leanh::LeanObject,
    mut v_t_9322_: *mut crate::leanh::LeanObject,
    mut v_inst_9323_: *mut crate::leanh::LeanObject,
    mut v_inst_9324_: *mut crate::leanh::LeanObject,
    mut v_inst_9325_: *mut crate::leanh::LeanObject,
    mut v_decl_9326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9327_: u8 = 0;
    let mut v_t_boxed_9328_: u8 = 0;
    let mut v_res_9329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9327_ = (crate::leanh::lean_unbox(v_pu_9321_) as u8);
    v_t_boxed_9328_ = (crate::leanh::lean_unbox(v_t_9322_) as u8);
    v_res_9329_ = l_Lean_Compiler_LCNF_normFunDecl(
        v_m_9320_,
        v_pu_boxed_9327_,
        v_t_boxed_9328_,
        v_inst_9323_,
        v_inst_9324_,
        v_inst_9325_,
        v_decl_9326_,
    );
    return v_res_9329_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg___lam__0(
    mut v_pu_9330_: u8,
    mut v_t_9331_: u8,
    mut v_code_9332_: *mut crate::leanh::LeanObject,
    mut v_inst_9333_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_9334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9335_ = crate::leanh::lean_box((v_pu_9330_) as usize);
    v___x_9336_ = crate::leanh::lean_box((v_t_9331_) as usize);
    v___x_9337_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCodeImp___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_9337_, 0, v___x_9335_);
    crate::leanh::lean_closure_set(v___x_9337_, 1, v___x_9336_);
    crate::leanh::lean_closure_set(v___x_9337_, 2, v_code_9332_);
    crate::leanh::lean_closure_set(v___x_9337_, 3, v_____do__lift_9334_);
    v___x_9338_ = crate::leanh::lean_apply_2(v_inst_9333_, crate::leanh::lean_box(0), v___x_9337_);
    return v___x_9338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(
    mut v_pu_9339_: *mut crate::leanh::LeanObject,
    mut v_t_9340_: *mut crate::leanh::LeanObject,
    mut v_code_9341_: *mut crate::leanh::LeanObject,
    mut v_inst_9342_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_9343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9344_: u8 = 0;
    let mut v_t_boxed_9345_: u8 = 0;
    let mut v_res_9346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9344_ = (crate::leanh::lean_unbox(v_pu_9339_) as u8);
    v_t_boxed_9345_ = (crate::leanh::lean_unbox(v_t_9340_) as u8);
    v_res_9346_ = l_Lean_Compiler_LCNF_normCode___redArg___lam__0(
        v_pu_boxed_9344_,
        v_t_boxed_9345_,
        v_code_9341_,
        v_inst_9342_,
        v_____do__lift_9343_,
    );
    return v_res_9346_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg(
    mut v_pu_9347_: u8,
    mut v_t_9348_: u8,
    mut v_inst_9349_: *mut crate::leanh::LeanObject,
    mut v_inst_9350_: *mut crate::leanh::LeanObject,
    mut v_inst_9351_: *mut crate::leanh::LeanObject,
    mut v_code_9352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_9353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_9353_ = crate::leanh::lean_ctor_get(v_inst_9350_, 1);
    crate::leanh::lean_inc(v_toBind_9353_);
    crate::leanh::lean_dec_ref(v_inst_9350_);
    v___x_9354_ = crate::leanh::lean_box((v_pu_9347_) as usize);
    v___x_9355_ = crate::leanh::lean_box((v_t_9348_) as usize);
    v___f_9356_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_9356_, 0, v___x_9354_);
    crate::leanh::lean_closure_set(v___f_9356_, 1, v___x_9355_);
    crate::leanh::lean_closure_set(v___f_9356_, 2, v_code_9352_);
    crate::leanh::lean_closure_set(v___f_9356_, 3, v_inst_9349_);
    v___x_9357_ = crate::leanh::lean_apply_4(
        v_toBind_9353_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_9351_,
        v___f_9356_,
    );
    return v___x_9357_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg___boxed(
    mut v_pu_9358_: *mut crate::leanh::LeanObject,
    mut v_t_9359_: *mut crate::leanh::LeanObject,
    mut v_inst_9360_: *mut crate::leanh::LeanObject,
    mut v_inst_9361_: *mut crate::leanh::LeanObject,
    mut v_inst_9362_: *mut crate::leanh::LeanObject,
    mut v_code_9363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9364_: u8 = 0;
    let mut v_t_boxed_9365_: u8 = 0;
    let mut v_res_9366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9364_ = (crate::leanh::lean_unbox(v_pu_9358_) as u8);
    v_t_boxed_9365_ = (crate::leanh::lean_unbox(v_t_9359_) as u8);
    v_res_9366_ = l_Lean_Compiler_LCNF_normCode___redArg(
        v_pu_boxed_9364_,
        v_t_boxed_9365_,
        v_inst_9360_,
        v_inst_9361_,
        v_inst_9362_,
        v_code_9363_,
    );
    return v_res_9366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode(
    mut v_m_9367_: *mut crate::leanh::LeanObject,
    mut v_pu_9368_: u8,
    mut v_t_9369_: u8,
    mut v_inst_9370_: *mut crate::leanh::LeanObject,
    mut v_inst_9371_: *mut crate::leanh::LeanObject,
    mut v_inst_9372_: *mut crate::leanh::LeanObject,
    mut v_code_9373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_9374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_9374_ = crate::leanh::lean_ctor_get(v_inst_9371_, 1);
    crate::leanh::lean_inc(v_toBind_9374_);
    crate::leanh::lean_dec_ref(v_inst_9371_);
    v___x_9375_ = crate::leanh::lean_box((v_pu_9368_) as usize);
    v___x_9376_ = crate::leanh::lean_box((v_t_9369_) as usize);
    v___f_9377_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_9377_, 0, v___x_9375_);
    crate::leanh::lean_closure_set(v___f_9377_, 1, v___x_9376_);
    crate::leanh::lean_closure_set(v___f_9377_, 2, v_code_9373_);
    crate::leanh::lean_closure_set(v___f_9377_, 3, v_inst_9370_);
    v___x_9378_ = crate::leanh::lean_apply_4(
        v_toBind_9374_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_9372_,
        v___f_9377_,
    );
    return v___x_9378_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___boxed(
    mut v_m_9379_: *mut crate::leanh::LeanObject,
    mut v_pu_9380_: *mut crate::leanh::LeanObject,
    mut v_t_9381_: *mut crate::leanh::LeanObject,
    mut v_inst_9382_: *mut crate::leanh::LeanObject,
    mut v_inst_9383_: *mut crate::leanh::LeanObject,
    mut v_inst_9384_: *mut crate::leanh::LeanObject,
    mut v_code_9385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9386_: u8 = 0;
    let mut v_t_boxed_9387_: u8 = 0;
    let mut v_res_9388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9386_ = (crate::leanh::lean_unbox(v_pu_9380_) as u8);
    v_t_boxed_9387_ = (crate::leanh::lean_unbox(v_t_9381_) as u8);
    v_res_9388_ = l_Lean_Compiler_LCNF_normCode(
        v_m_9379_,
        v_pu_boxed_9386_,
        v_t_boxed_9387_,
        v_inst_9382_,
        v_inst_9383_,
        v_inst_9384_,
        v_code_9385_,
    );
    return v_res_9388_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
    mut v_pu_9389_: u8,
    mut v_e_9390_: *mut crate::leanh::LeanObject,
    mut v_s_9391_: *mut crate::leanh::LeanObject,
    mut v_translator_9392_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9394_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_9389_,
        v_s_9391_,
        v_translator_9392_,
        v_e_9390_,
    );
    v___x_9395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9395_, 0, v___x_9394_);
    return v___x_9395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(
    mut v_pu_9396_: *mut crate::leanh::LeanObject,
    mut v_e_9397_: *mut crate::leanh::LeanObject,
    mut v_s_9398_: *mut crate::leanh::LeanObject,
    mut v_translator_9399_: *mut crate::leanh::LeanObject,
    mut v_a_9400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9401_: u8 = 0;
    let mut v_translator_boxed_9402_: u8 = 0;
    let mut v_res_9403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9401_ = (crate::leanh::lean_unbox(v_pu_9396_) as u8);
    v_translator_boxed_9402_ = (crate::leanh::lean_unbox(v_translator_9399_) as u8);
    v_res_9403_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
        v_pu_boxed_9401_,
        v_e_9397_,
        v_s_9398_,
        v_translator_boxed_9402_,
    );
    crate::leanh::lean_dec_ref(v_s_9398_);
    return v_res_9403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars(
    mut v_pu_9404_: u8,
    mut v_e_9405_: *mut crate::leanh::LeanObject,
    mut v_s_9406_: *mut crate::leanh::LeanObject,
    mut v_translator_9407_: u8,
    mut v_a_9408_: *mut crate::leanh::LeanObject,
    mut v_a_9409_: *mut crate::leanh::LeanObject,
    mut v_a_9410_: *mut crate::leanh::LeanObject,
    mut v_a_9411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9413_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
        v_pu_9404_,
        v_e_9405_,
        v_s_9406_,
        v_translator_9407_,
    );
    return v___x_9413_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars___boxed(
    mut v_pu_9414_: *mut crate::leanh::LeanObject,
    mut v_e_9415_: *mut crate::leanh::LeanObject,
    mut v_s_9416_: *mut crate::leanh::LeanObject,
    mut v_translator_9417_: *mut crate::leanh::LeanObject,
    mut v_a_9418_: *mut crate::leanh::LeanObject,
    mut v_a_9419_: *mut crate::leanh::LeanObject,
    mut v_a_9420_: *mut crate::leanh::LeanObject,
    mut v_a_9421_: *mut crate::leanh::LeanObject,
    mut v_a_9422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9423_: u8 = 0;
    let mut v_translator_boxed_9424_: u8 = 0;
    let mut v_res_9425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9423_ = (crate::leanh::lean_unbox(v_pu_9414_) as u8);
    v_translator_boxed_9424_ = (crate::leanh::lean_unbox(v_translator_9417_) as u8);
    v_res_9425_ = l_Lean_Compiler_LCNF_replaceExprFVars(
        v_pu_boxed_9423_,
        v_e_9415_,
        v_s_9416_,
        v_translator_boxed_9424_,
        v_a_9418_,
        v_a_9419_,
        v_a_9420_,
        v_a_9421_,
    );
    crate::leanh::lean_dec(v_a_9421_);
    crate::leanh::lean_dec_ref(v_a_9420_);
    crate::leanh::lean_dec(v_a_9419_);
    crate::leanh::lean_dec_ref(v_a_9418_);
    crate::leanh::lean_dec_ref(v_s_9416_);
    return v_res_9425_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceFVars(
    mut v_pu_9426_: u8,
    mut v_code_9427_: *mut crate::leanh::LeanObject,
    mut v_s_9428_: *mut crate::leanh::LeanObject,
    mut v_translator_9429_: u8,
    mut v_a_9430_: *mut crate::leanh::LeanObject,
    mut v_a_9431_: *mut crate::leanh::LeanObject,
    mut v_a_9432_: *mut crate::leanh::LeanObject,
    mut v_a_9433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9435_ = l_Lean_Compiler_LCNF_normCodeImp(
        v_pu_9426_,
        v_translator_9429_,
        v_code_9427_,
        v_s_9428_,
        v_a_9430_,
        v_a_9431_,
        v_a_9432_,
        v_a_9433_,
    );
    return v___x_9435_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceFVars___boxed(
    mut v_pu_9436_: *mut crate::leanh::LeanObject,
    mut v_code_9437_: *mut crate::leanh::LeanObject,
    mut v_s_9438_: *mut crate::leanh::LeanObject,
    mut v_translator_9439_: *mut crate::leanh::LeanObject,
    mut v_a_9440_: *mut crate::leanh::LeanObject,
    mut v_a_9441_: *mut crate::leanh::LeanObject,
    mut v_a_9442_: *mut crate::leanh::LeanObject,
    mut v_a_9443_: *mut crate::leanh::LeanObject,
    mut v_a_9444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9445_: u8 = 0;
    let mut v_translator_boxed_9446_: u8 = 0;
    let mut v_res_9447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9445_ = (crate::leanh::lean_unbox(v_pu_9436_) as u8);
    v_translator_boxed_9446_ = (crate::leanh::lean_unbox(v_translator_9439_) as u8);
    v_res_9447_ = l_Lean_Compiler_LCNF_replaceFVars(
        v_pu_boxed_9445_,
        v_code_9437_,
        v_s_9438_,
        v_translator_boxed_9446_,
        v_a_9440_,
        v_a_9441_,
        v_a_9442_,
        v_a_9443_,
    );
    crate::leanh::lean_dec(v_a_9443_);
    crate::leanh::lean_dec_ref(v_a_9442_);
    crate::leanh::lean_dec(v_a_9441_);
    crate::leanh::lean_dec_ref(v_a_9440_);
    crate::leanh::lean_dec_ref(v_s_9438_);
    return v_res_9447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___redArg(
    mut v_a_9451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9453_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1;
    v___x_9454_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_9453_, v_a_9451_);
    return v___x_9454_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(
    mut v_a_9455_: *mut crate::leanh::LeanObject,
    mut v_a_9456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9457_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_9455_);
    crate::leanh::lean_dec(v_a_9455_);
    return v_res_9457_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName(
    mut v_a_9458_: *mut crate::leanh::LeanObject,
    mut v_a_9459_: *mut crate::leanh::LeanObject,
    mut v_a_9460_: *mut crate::leanh::LeanObject,
    mut v_a_9461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9463_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_9459_);
    return v___x_9463_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___boxed(
    mut v_a_9464_: *mut crate::leanh::LeanObject,
    mut v_a_9465_: *mut crate::leanh::LeanObject,
    mut v_a_9466_: *mut crate::leanh::LeanObject,
    mut v_a_9467_: *mut crate::leanh::LeanObject,
    mut v_a_9468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9469_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_9464_, v_a_9465_, v_a_9466_, v_a_9467_);
    crate::leanh::lean_dec(v_a_9467_);
    crate::leanh::lean_dec_ref(v_a_9466_);
    crate::leanh::lean_dec(v_a_9465_);
    crate::leanh::lean_dec_ref(v_a_9464_);
    return v_res_9469_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxParam(
    mut v_pu_9470_: u8,
    mut v_type_9471_: *mut crate::leanh::LeanObject,
    mut v_borrow_9472_: u8,
    mut v_a_9473_: *mut crate::leanh::LeanObject,
    mut v_a_9474_: *mut crate::leanh::LeanObject,
    mut v_a_9475_: *mut crate::leanh::LeanObject,
    mut v_a_9476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9478_ = l_Lean_Compiler_LCNF_mkParam___closed__1;
    v___x_9479_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_9478_, v_a_9474_);
    v_a_9480_ = crate::leanh::lean_ctor_get(v___x_9479_, 0);
    crate::leanh::lean_inc(v_a_9480_);
    crate::leanh::lean_dec_ref(v___x_9479_);
    v___x_9481_ = l_Lean_Compiler_LCNF_mkParam(
        v_pu_9470_,
        v_a_9480_,
        v_type_9471_,
        v_borrow_9472_,
        v_a_9473_,
        v_a_9474_,
        v_a_9475_,
        v_a_9476_,
    );
    return v___x_9481_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxParam___boxed(
    mut v_pu_9482_: *mut crate::leanh::LeanObject,
    mut v_type_9483_: *mut crate::leanh::LeanObject,
    mut v_borrow_9484_: *mut crate::leanh::LeanObject,
    mut v_a_9485_: *mut crate::leanh::LeanObject,
    mut v_a_9486_: *mut crate::leanh::LeanObject,
    mut v_a_9487_: *mut crate::leanh::LeanObject,
    mut v_a_9488_: *mut crate::leanh::LeanObject,
    mut v_a_9489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_9490_: u8 = 0;
    let mut v_borrow_boxed_9491_: u8 = 0;
    let mut v_res_9492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_9490_ = (crate::leanh::lean_unbox(v_pu_9482_) as u8);
    v_borrow_boxed_9491_ = (crate::leanh::lean_unbox(v_borrow_9484_) as u8);
    v_res_9492_ = l_Lean_Compiler_LCNF_mkAuxParam(
        v_pu_boxed_9490_,
        v_type_9483_,
        v_borrow_boxed_9491_,
        v_a_9485_,
        v_a_9486_,
        v_a_9487_,
        v_a_9488_,
    );
    crate::leanh::lean_dec(v_a_9488_);
    crate::leanh::lean_dec_ref(v_a_9487_);
    crate::leanh::lean_dec(v_a_9486_);
    crate::leanh::lean_dec_ref(v_a_9485_);
    return v_res_9492_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___redArg(
    mut v_a_9493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_9495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_9495_ = crate::leanh::lean_ctor_get(v_a_9493_, 0);
    crate::leanh::lean_inc_ref(v_config_9495_);
    v___x_9496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9496_, 0, v_config_9495_);
    return v___x_9496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___redArg___boxed(
    mut v_a_9497_: *mut crate::leanh::LeanObject,
    mut v_a_9498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9499_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_9497_);
    crate::leanh::lean_dec_ref(v_a_9497_);
    return v_res_9499_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig(
    mut v_a_9500_: *mut crate::leanh::LeanObject,
    mut v_a_9501_: *mut crate::leanh::LeanObject,
    mut v_a_9502_: *mut crate::leanh::LeanObject,
    mut v_a_9503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9505_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_9500_);
    return v___x_9505_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___boxed(
    mut v_a_9506_: *mut crate::leanh::LeanObject,
    mut v_a_9507_: *mut crate::leanh::LeanObject,
    mut v_a_9508_: *mut crate::leanh::LeanObject,
    mut v_a_9509_: *mut crate::leanh::LeanObject,
    mut v_a_9510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9511_ = l_Lean_Compiler_LCNF_getConfig(v_a_9506_, v_a_9507_, v_a_9508_, v_a_9509_);
    crate::leanh::lean_dec(v_a_9509_);
    crate::leanh::lean_dec_ref(v_a_9508_);
    crate::leanh::lean_dec(v_a_9507_);
    crate::leanh::lean_dec_ref(v_a_9506_);
    return v_res_9511_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run___redArg(
    mut v_x_9512_: *mut crate::leanh::LeanObject,
    mut v_s_9513_: *mut crate::leanh::LeanObject,
    mut v_phase_9514_: u8,
    mut v_a_9515_: *mut crate::leanh::LeanObject,
    mut v_a_9516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_9519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9526_: u8 = 0;
    let mut v___x_9527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9518_ = lean_st_mk_ref(v_s_9513_);
                v_options_9519_ = crate::leanh::lean_ctor_get(v_a_9515_, 2);
                v___x_9520_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_9519_);
                v___x_9521_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_9521_, 0, v___x_9520_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_9521_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_phase_9514_,
                );
                crate::leanh::lean_inc(v_a_9516_);
                crate::leanh::lean_inc_ref(v_a_9515_);
                crate::leanh::lean_inc(v___x_9518_);
                v___x_9522_ = crate::leanh::lean_apply_5(
                    v_x_9512_,
                    v___x_9521_,
                    v___x_9518_,
                    v_a_9515_,
                    v_a_9516_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_9522_) == 0 {
                    v_a_9523_ = crate::leanh::lean_ctor_get(v___x_9522_, 0);
                    v_isSharedCheck_9531_ = (!crate::leanh::lean_is_exclusive(v___x_9522_)) as u8;
                    if v_isSharedCheck_9531_ == 0 {
                        v___x_9525_ = v___x_9522_;
                        v_isShared_9526_ = v_isSharedCheck_9531_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_9523_);
                        crate::leanh::lean_dec(v___x_9522_);
                        v___x_9525_ = crate::leanh::lean_box(0);
                        v_isShared_9526_ = v_isSharedCheck_9531_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_9518_);
                    return v___x_9522_;
                }
            }
            1 => {
                v___x_9527_ = lean_st_ref_get(v___x_9518_);
                crate::leanh::lean_dec(v___x_9518_);
                crate::leanh::lean_dec(v___x_9527_);
                if v_isShared_9526_ == 0 {
                    v___x_9529_ = v___x_9525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9530_, 0, v_a_9523_);
                    v___x_9529_ = v_reuseFailAlloc_9530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run___redArg___boxed(
    mut v_x_9532_: *mut crate::leanh::LeanObject,
    mut v_s_9533_: *mut crate::leanh::LeanObject,
    mut v_phase_9534_: *mut crate::leanh::LeanObject,
    mut v_a_9535_: *mut crate::leanh::LeanObject,
    mut v_a_9536_: *mut crate::leanh::LeanObject,
    mut v_a_9537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_9538_: u8 = 0;
    let mut v_res_9539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_9538_ = (crate::leanh::lean_unbox(v_phase_9534_) as u8);
    v_res_9539_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
        v_x_9532_,
        v_s_9533_,
        v_phase_boxed_9538_,
        v_a_9535_,
        v_a_9536_,
    );
    crate::leanh::lean_dec(v_a_9536_);
    crate::leanh::lean_dec_ref(v_a_9535_);
    return v_res_9539_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run(
    mut v_00_u03b1_9540_: *mut crate::leanh::LeanObject,
    mut v_x_9541_: *mut crate::leanh::LeanObject,
    mut v_s_9542_: *mut crate::leanh::LeanObject,
    mut v_phase_9543_: u8,
    mut v_a_9544_: *mut crate::leanh::LeanObject,
    mut v_a_9545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9547_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
        v_x_9541_,
        v_s_9542_,
        v_phase_9543_,
        v_a_9544_,
        v_a_9545_,
    );
    return v___x_9547_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run___boxed(
    mut v_00_u03b1_9548_: *mut crate::leanh::LeanObject,
    mut v_x_9549_: *mut crate::leanh::LeanObject,
    mut v_s_9550_: *mut crate::leanh::LeanObject,
    mut v_phase_9551_: *mut crate::leanh::LeanObject,
    mut v_a_9552_: *mut crate::leanh::LeanObject,
    mut v_a_9553_: *mut crate::leanh::LeanObject,
    mut v_a_9554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_9555_: u8 = 0;
    let mut v_res_9556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_9555_ = (crate::leanh::lean_unbox(v_phase_9551_) as u8);
    v_res_9556_ = l_Lean_Compiler_LCNF_CompilerM_run(
        v_00_u03b1_9548_,
        v_x_9549_,
        v_s_9550_,
        v_phase_boxed_9555_,
        v_a_9552_,
        v_a_9553_,
    );
    crate::leanh::lean_dec(v_a_9553_);
    crate::leanh::lean_dec_ref(v_a_9552_);
    return v_res_9556_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9557_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_9557_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(
    mut v_00_u03b1_9558_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9559_: *mut crate::leanh::LeanObject,
    mut v_inst_9560_: *mut crate::leanh::LeanObject,
    mut v_inst_9561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9562_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0,
    );
    return v___x_9562_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___boxed(
    mut v_00_u03b1_9563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9564_: *mut crate::leanh::LeanObject,
    mut v_inst_9565_: *mut crate::leanh::LeanObject,
    mut v_inst_9566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9567_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(
        v_00_u03b1_9563_,
        v_00_u03b2_9564_,
        v_inst_9565_,
        v_inst_9566_,
    );
    crate::leanh::lean_dec_ref(v_inst_9566_);
    crate::leanh::lean_dec_ref(v_inst_9565_);
    return v_res_9567_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension(
    mut v_a_9568_: *mut crate::leanh::LeanObject,
    mut v_a_9569_: *mut crate::leanh::LeanObject,
    mut v_a_9570_: *mut crate::leanh::LeanObject,
    mut v_a_9571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9572_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0,
    );
    return v___x_9572_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension___boxed(
    mut v_a_9573_: *mut crate::leanh::LeanObject,
    mut v_a_9574_: *mut crate::leanh::LeanObject,
    mut v_a_9575_: *mut crate::leanh::LeanObject,
    mut v_a_9576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9577_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(
        v_a_9573_, v_a_9574_, v_a_9575_, v_a_9576_,
    );
    crate::leanh::lean_dec_ref(v_a_9576_);
    crate::leanh::lean_dec_ref(v_a_9575_);
    return v_res_9577_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9581_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2;
    v___x_9582_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_9583_ = crate::leanh::lean_unsigned_to_nat(177);
    v___x_9584_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1;
    v___x_9585_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0;
    v___x_9586_ = l_mkPanicMessageWithDecl(
        v___x_9585_,
        v___x_9584_,
        v___x_9583_,
        v___x_9582_,
        v___x_9581_,
    );
    return v___x_9586_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(
    mut v_inst_9587_: *mut crate::leanh::LeanObject,
    mut v_inst_9588_: *mut crate::leanh::LeanObject,
    mut v_snd_9589_: *mut crate::leanh::LeanObject,
    mut v_inst_9590_: *mut crate::leanh::LeanObject,
    mut v_s_9591_: *mut crate::leanh::LeanObject,
    mut v_e_9592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_9593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9597_: u8 = 0;
    let mut v___x_9598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_9600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9593_ = crate::leanh::lean_ctor_get(v_s_9591_, 0);
                v_snd_9594_ = crate::leanh::lean_ctor_get(v_s_9591_, 1);
                v_isSharedCheck_9609_ = (!crate::leanh::lean_is_exclusive(v_s_9591_)) as u8;
                if v_isSharedCheck_9609_ == 0 {
                    v___x_9596_ = v_s_9591_;
                    v_isShared_9597_ = v_isSharedCheck_9609_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_9594_);
                    crate::leanh::lean_inc(v_fst_9593_);
                    crate::leanh::lean_dec(v_s_9591_);
                    v___x_9596_ = crate::leanh::lean_box(0);
                    v_isShared_9597_ = v_isSharedCheck_9609_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_e_9592_, 2);
                v___x_9598_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_9598_, 0, v_e_9592_);
                crate::leanh::lean_ctor_set(v___x_9598_, 1, v_fst_9593_);
                crate::leanh::lean_inc_ref(v_inst_9588_);
                crate::leanh::lean_inc_ref(v_inst_9587_);
                v___x_9605_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v_inst_9587_,
                    v_inst_9588_,
                    v_snd_9589_,
                    v_e_9592_,
                );
                if crate::leanh::lean_obj_tag(v___x_9605_) == 0 {
                    v___x_9606_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
                    v___x_9607_ = l_panic___redArg(v_inst_9590_, v___x_9606_);
                    v___y_9600_ = v___x_9607_;
                    state = 2;
                    continue;
                } else {
                    v_val_9608_ = crate::leanh::lean_ctor_get(v___x_9605_, 0);
                    crate::leanh::lean_inc(v_val_9608_);
                    crate::leanh::lean_dec_ref_known(v___x_9605_, 1);
                    v___y_9600_ = v_val_9608_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9601_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_9587_,
                    v_inst_9588_,
                    v_snd_9594_,
                    v_e_9592_,
                    v___y_9600_,
                );
                if v_isShared_9597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9596_, 1, v___x_9601_);
                    crate::leanh::lean_ctor_set(v___x_9596_, 0, v___x_9598_);
                    v___x_9603_ = v___x_9596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9604_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9604_, 0, v___x_9598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9604_, 1, v___x_9601_);
                    v___x_9603_ = v_reuseFailAlloc_9604_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed(
    mut v_inst_9610_: *mut crate::leanh::LeanObject,
    mut v_inst_9611_: *mut crate::leanh::LeanObject,
    mut v_snd_9612_: *mut crate::leanh::LeanObject,
    mut v_inst_9613_: *mut crate::leanh::LeanObject,
    mut v_s_9614_: *mut crate::leanh::LeanObject,
    mut v_e_9615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9616_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(
        v_inst_9610_,
        v_inst_9611_,
        v_snd_9612_,
        v_inst_9613_,
        v_s_9614_,
        v_e_9615_,
    );
    crate::leanh::lean_dec(v_inst_9613_);
    crate::leanh::lean_dec(v_snd_9612_);
    return v_res_9616_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(
    mut v_inst_9619_: *mut crate::leanh::LeanObject,
    mut v_inst_9620_: *mut crate::leanh::LeanObject,
    mut v_inst_9621_: *mut crate::leanh::LeanObject,
    mut v_oldState_9622_: *mut crate::leanh::LeanObject,
    mut v_newState_9623_: *mut crate::leanh::LeanObject,
    mut v_x_9624_: *mut crate::leanh::LeanObject,
    mut v_s_9625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_9626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_9628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_9634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_9626_ = crate::leanh::lean_ctor_get(v_newState_9623_, 0);
    crate::leanh::lean_inc_n(v_fst_9626_, 2);
    v_snd_9627_ = crate::leanh::lean_ctor_get(v_newState_9623_, 1);
    crate::leanh::lean_inc(v_snd_9627_);
    crate::leanh::lean_dec_ref(v_newState_9623_);
    v_fst_9628_ = crate::leanh::lean_ctor_get(v_oldState_9622_, 0);
    v___f_9629_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_9629_, 0, v_inst_9619_);
    crate::leanh::lean_closure_set(v___f_9629_, 1, v_inst_9620_);
    crate::leanh::lean_closure_set(v___f_9629_, 2, v_snd_9627_);
    crate::leanh::lean_closure_set(v___f_9629_, 3, v_inst_9621_);
    v___x_9630_ = l_List_lengthTR___redArg(v_fst_9626_);
    v___x_9631_ = l_List_lengthTR___redArg(v_fst_9628_);
    v___x_9632_ = lean_nat_sub(v___x_9630_, v___x_9631_);
    crate::leanh::lean_dec(v___x_9631_);
    crate::leanh::lean_dec(v___x_9630_);
    v___x_9633_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0;
    v_newEntries_9634_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        crate::leanh::lean_box(0),
        v_fst_9626_,
        v_fst_9626_,
        v___x_9632_,
        v___x_9633_,
    );
    crate::leanh::lean_dec(v_fst_9626_);
    v___x_9635_ = l_List_foldl___redArg(v___f_9629_, v_s_9625_, v_newEntries_9634_);
    return v___x_9635_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(
    mut v_inst_9636_: *mut crate::leanh::LeanObject,
    mut v_inst_9637_: *mut crate::leanh::LeanObject,
    mut v_inst_9638_: *mut crate::leanh::LeanObject,
    mut v_oldState_9639_: *mut crate::leanh::LeanObject,
    mut v_newState_9640_: *mut crate::leanh::LeanObject,
    mut v_x_9641_: *mut crate::leanh::LeanObject,
    mut v_s_9642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9643_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(
        v_inst_9636_,
        v_inst_9637_,
        v_inst_9638_,
        v_oldState_9639_,
        v_newState_9640_,
        v_x_9641_,
        v_s_9642_,
    );
    crate::leanh::lean_dec(v_x_9641_);
    crate::leanh::lean_dec_ref(v_oldState_9639_);
    return v_res_9643_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_9644_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0,
    );
    v___x_9646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9646_, 0, v___x_9645_);
    return v___x_9646_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1,
    );
    v___x_9648_ = crate::leanh::lean_box(0);
    v___x_9649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9649_, 0, v___x_9648_);
    crate::leanh::lean_ctor_set(v___x_9649_, 1, v___x_9647_);
    return v___x_9649_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2,
    );
    v___x_9651_ = crate::leanh::lean_alloc_closure(
        l_instMonadEIO___aux__5___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___x_9651_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9651_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_9651_, 2, v___x_9650_);
    return v___x_9651_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
    mut v_inst_9652_: *mut crate::leanh::LeanObject,
    mut v_inst_9653_: *mut crate::leanh::LeanObject,
    mut v_inst_9654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_9656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9664_: u8 = 0;
    let mut v___x_9666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9668_: u8 = 0;
    let mut v_a_9669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9672_: u8 = 0;
    let mut v___x_9674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_9656_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    7,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_9656_, 0, v_inst_9652_);
                crate::leanh::lean_closure_set(v___f_9656_, 1, v_inst_9653_);
                crate::leanh::lean_closure_set(v___f_9656_, 2, v_inst_9654_);
                v___x_9657_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3,
                );
                v___x_9658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_9658_, 0, v___f_9656_);
                v___x_9659_ = crate::leanh::lean_box(0);
                v___x_9660_ =
                    l_Lean_registerEnvExtension___redArg(v___x_9657_, v___x_9658_, v___x_9659_);
                if crate::leanh::lean_obj_tag(v___x_9660_) == 0 {
                    v_a_9661_ = crate::leanh::lean_ctor_get(v___x_9660_, 0);
                    v_isSharedCheck_9668_ = (!crate::leanh::lean_is_exclusive(v___x_9660_)) as u8;
                    if v_isSharedCheck_9668_ == 0 {
                        v___x_9663_ = v___x_9660_;
                        v_isShared_9664_ = v_isSharedCheck_9668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_9661_);
                        crate::leanh::lean_dec(v___x_9660_);
                        v___x_9663_ = crate::leanh::lean_box(0);
                        v_isShared_9664_ = v_isSharedCheck_9668_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9669_ = crate::leanh::lean_ctor_get(v___x_9660_, 0);
                    v_isSharedCheck_9676_ = (!crate::leanh::lean_is_exclusive(v___x_9660_)) as u8;
                    if v_isSharedCheck_9676_ == 0 {
                        v___x_9671_ = v___x_9660_;
                        v_isShared_9672_ = v_isSharedCheck_9676_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_9669_);
                        crate::leanh::lean_dec(v___x_9660_);
                        v___x_9671_ = crate::leanh::lean_box(0);
                        v_isShared_9672_ = v_isSharedCheck_9676_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9664_ == 0 {
                    v___x_9666_ = v___x_9663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9667_, 0, v_a_9661_);
                    v___x_9666_ = v_reuseFailAlloc_9667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9666_;
            }
            3 => {
                if v_isShared_9672_ == 0 {
                    v___x_9674_ = v___x_9671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9675_, 0, v_a_9669_);
                    v___x_9674_ = v_reuseFailAlloc_9675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___boxed(
    mut v_inst_9677_: *mut crate::leanh::LeanObject,
    mut v_inst_9678_: *mut crate::leanh::LeanObject,
    mut v_inst_9679_: *mut crate::leanh::LeanObject,
    mut v_a_9680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9681_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
        v_inst_9677_,
        v_inst_9678_,
        v_inst_9679_,
    );
    return v_res_9681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register(
    mut v_00_u03b1_9682_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9683_: *mut crate::leanh::LeanObject,
    mut v_inst_9684_: *mut crate::leanh::LeanObject,
    mut v_inst_9685_: *mut crate::leanh::LeanObject,
    mut v_inst_9686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9688_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
        v_inst_9684_,
        v_inst_9685_,
        v_inst_9686_,
    );
    return v___x_9688_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___boxed(
    mut v_00_u03b1_9689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9690_: *mut crate::leanh::LeanObject,
    mut v_inst_9691_: *mut crate::leanh::LeanObject,
    mut v_inst_9692_: *mut crate::leanh::LeanObject,
    mut v_inst_9693_: *mut crate::leanh::LeanObject,
    mut v_a_9694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9695_ = l_Lean_Compiler_LCNF_CacheExtension_register(
        v_00_u03b1_9689_,
        v_00_u03b2_9690_,
        v_inst_9691_,
        v_inst_9692_,
        v_inst_9693_,
    );
    return v_res_9695_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0(
    mut v_a_9696_: *mut crate::leanh::LeanObject,
    mut v_inst_9697_: *mut crate::leanh::LeanObject,
    mut v_inst_9698_: *mut crate::leanh::LeanObject,
    mut v_b_9699_: *mut crate::leanh::LeanObject,
    mut v_x_9700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_9701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9705_: u8 = 0;
    let mut v___x_9706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9701_ = crate::leanh::lean_ctor_get(v_x_9700_, 0);
                v_snd_9702_ = crate::leanh::lean_ctor_get(v_x_9700_, 1);
                v_isSharedCheck_9711_ = (!crate::leanh::lean_is_exclusive(v_x_9700_)) as u8;
                if v_isSharedCheck_9711_ == 0 {
                    v___x_9704_ = v_x_9700_;
                    v_isShared_9705_ = v_isSharedCheck_9711_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_9702_);
                    crate::leanh::lean_inc(v_fst_9701_);
                    crate::leanh::lean_dec(v_x_9700_);
                    v___x_9704_ = crate::leanh::lean_box(0);
                    v_isShared_9705_ = v_isSharedCheck_9711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_9696_);
                v___x_9706_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_9706_, 0, v_a_9696_);
                crate::leanh::lean_ctor_set(v___x_9706_, 1, v_fst_9701_);
                v___x_9707_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_9697_,
                    v_inst_9698_,
                    v_snd_9702_,
                    v_a_9696_,
                    v_b_9699_,
                );
                if v_isShared_9705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9704_, 1, v___x_9707_);
                    crate::leanh::lean_ctor_set(v___x_9704_, 0, v___x_9706_);
                    v___x_9709_ = v___x_9704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9710_, 0, v___x_9706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9710_, 1, v___x_9707_);
                    v___x_9709_ = v_reuseFailAlloc_9710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9712_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_9712_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0,
    );
    v___x_9714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9714_, 0, v___x_9713_);
    return v___x_9714_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_9715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9715_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1,
    );
    v___x_9716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9716_, 0, v___x_9715_);
    crate::leanh::lean_ctor_set(v___x_9716_, 1, v___x_9715_);
    return v___x_9716_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(
    mut v_inst_9717_: *mut crate::leanh::LeanObject,
    mut v_inst_9718_: *mut crate::leanh::LeanObject,
    mut v_ext_9719_: *mut crate::leanh::LeanObject,
    mut v_a_9720_: *mut crate::leanh::LeanObject,
    mut v_b_9721_: *mut crate::leanh::LeanObject,
    mut v_a_9722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_9725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_9726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_9727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_9728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_9729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_9730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_9731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_9732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9735_: u8 = 0;
    let mut v_asyncMode_9736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_9737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9747_: u8 = 0;
    let mut v_unused_9748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9724_ = lean_st_ref_take(v_a_9722_);
                v_env_9725_ = crate::leanh::lean_ctor_get(v___x_9724_, 0);
                v_nextMacroScope_9726_ = crate::leanh::lean_ctor_get(v___x_9724_, 1);
                v_ngen_9727_ = crate::leanh::lean_ctor_get(v___x_9724_, 2);
                v_auxDeclNGen_9728_ = crate::leanh::lean_ctor_get(v___x_9724_, 3);
                v_traceState_9729_ = crate::leanh::lean_ctor_get(v___x_9724_, 4);
                v_messages_9730_ = crate::leanh::lean_ctor_get(v___x_9724_, 6);
                v_infoState_9731_ = crate::leanh::lean_ctor_get(v___x_9724_, 7);
                v_snapshotTasks_9732_ = crate::leanh::lean_ctor_get(v___x_9724_, 8);
                v_isSharedCheck_9747_ = (!crate::leanh::lean_is_exclusive(v___x_9724_)) as u8;
                if v_isSharedCheck_9747_ == 0 {
                    v_unused_9748_ = crate::leanh::lean_ctor_get(v___x_9724_, 5);
                    crate::leanh::lean_dec(v_unused_9748_);
                    v___x_9734_ = v___x_9724_;
                    v_isShared_9735_ = v_isSharedCheck_9747_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_9732_);
                    crate::leanh::lean_inc(v_infoState_9731_);
                    crate::leanh::lean_inc(v_messages_9730_);
                    crate::leanh::lean_inc(v_traceState_9729_);
                    crate::leanh::lean_inc(v_auxDeclNGen_9728_);
                    crate::leanh::lean_inc(v_ngen_9727_);
                    crate::leanh::lean_inc(v_nextMacroScope_9726_);
                    crate::leanh::lean_inc(v_env_9725_);
                    crate::leanh::lean_dec(v___x_9724_);
                    v___x_9734_ = crate::leanh::lean_box(0);
                    v_isShared_9735_ = v_isSharedCheck_9747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_9736_ = crate::leanh::lean_ctor_get(v_ext_9719_, 2);
                crate::leanh::lean_inc(v_asyncMode_9736_);
                v___f_9737_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0
                        as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_9737_, 0, v_a_9720_);
                crate::leanh::lean_closure_set(v___f_9737_, 1, v_inst_9717_);
                crate::leanh::lean_closure_set(v___f_9737_, 2, v_inst_9718_);
                crate::leanh::lean_closure_set(v___f_9737_, 3, v_b_9721_);
                v___x_9738_ = crate::leanh::lean_box(0);
                v___x_9739_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_9719_,
                    v_env_9725_,
                    v___f_9737_,
                    v_asyncMode_9736_,
                    v___x_9738_,
                );
                crate::leanh::lean_dec(v_asyncMode_9736_);
                v___x_9740_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2,
                );
                if v_isShared_9735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_9734_, 5, v___x_9740_);
                    crate::leanh::lean_ctor_set(v___x_9734_, 0, v___x_9739_);
                    v___x_9742_ = v___x_9734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9746_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 0, v___x_9739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 1, v_nextMacroScope_9726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 2, v_ngen_9727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 3, v_auxDeclNGen_9728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 4, v_traceState_9729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 5, v___x_9740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 6, v_messages_9730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 7, v_infoState_9731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_9746_, 8, v_snapshotTasks_9732_);
                    v___x_9742_ = v_reuseFailAlloc_9746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9743_ = lean_st_ref_set(v_a_9722_, v___x_9742_);
                v___x_9744_ = crate::leanh::lean_box(0);
                v___x_9745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_9745_, 0, v___x_9744_);
                return v___x_9745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(
    mut v_inst_9749_: *mut crate::leanh::LeanObject,
    mut v_inst_9750_: *mut crate::leanh::LeanObject,
    mut v_ext_9751_: *mut crate::leanh::LeanObject,
    mut v_a_9752_: *mut crate::leanh::LeanObject,
    mut v_b_9753_: *mut crate::leanh::LeanObject,
    mut v_a_9754_: *mut crate::leanh::LeanObject,
    mut v_a_9755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9756_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(
        v_inst_9749_,
        v_inst_9750_,
        v_ext_9751_,
        v_a_9752_,
        v_b_9753_,
        v_a_9754_,
    );
    crate::leanh::lean_dec(v_a_9754_);
    return v_res_9756_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert(
    mut v_00_u03b1_9757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9758_: *mut crate::leanh::LeanObject,
    mut v_inst_9759_: *mut crate::leanh::LeanObject,
    mut v_inst_9760_: *mut crate::leanh::LeanObject,
    mut v_inst_9761_: *mut crate::leanh::LeanObject,
    mut v_ext_9762_: *mut crate::leanh::LeanObject,
    mut v_a_9763_: *mut crate::leanh::LeanObject,
    mut v_b_9764_: *mut crate::leanh::LeanObject,
    mut v_a_9765_: *mut crate::leanh::LeanObject,
    mut v_a_9766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9768_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(
        v_inst_9759_,
        v_inst_9760_,
        v_ext_9762_,
        v_a_9763_,
        v_b_9764_,
        v_a_9766_,
    );
    return v___x_9768_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___boxed(
    mut v_00_u03b1_9769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9770_: *mut crate::leanh::LeanObject,
    mut v_inst_9771_: *mut crate::leanh::LeanObject,
    mut v_inst_9772_: *mut crate::leanh::LeanObject,
    mut v_inst_9773_: *mut crate::leanh::LeanObject,
    mut v_ext_9774_: *mut crate::leanh::LeanObject,
    mut v_a_9775_: *mut crate::leanh::LeanObject,
    mut v_b_9776_: *mut crate::leanh::LeanObject,
    mut v_a_9777_: *mut crate::leanh::LeanObject,
    mut v_a_9778_: *mut crate::leanh::LeanObject,
    mut v_a_9779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9780_ = l_Lean_Compiler_LCNF_CacheExtension_insert(
        v_00_u03b1_9769_,
        v_00_u03b2_9770_,
        v_inst_9771_,
        v_inst_9772_,
        v_inst_9773_,
        v_ext_9774_,
        v_a_9775_,
        v_b_9776_,
        v_a_9777_,
        v_a_9778_,
    );
    crate::leanh::lean_dec(v_a_9778_);
    crate::leanh::lean_dec_ref(v_a_9777_);
    crate::leanh::lean_dec(v_inst_9773_);
    return v_res_9780_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(
    mut v_inst_9781_: *mut crate::leanh::LeanObject,
    mut v_inst_9782_: *mut crate::leanh::LeanObject,
    mut v_ext_9783_: *mut crate::leanh::LeanObject,
    mut v_a_9784_: *mut crate::leanh::LeanObject,
    mut v_a_9785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_9788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_9789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9787_ = lean_st_ref_get(v_a_9785_);
    v_env_9788_ = crate::leanh::lean_ctor_get(v___x_9787_, 0);
    crate::leanh::lean_inc_ref(v_env_9788_);
    crate::leanh::lean_dec(v___x_9787_);
    v_asyncMode_9789_ = crate::leanh::lean_ctor_get(v_ext_9783_, 2);
    v___x_9790_ = crate::leanh::lean_box(0);
    v___x_9791_ = l_Lean_PersistentHashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_9781_,
        v_inst_9782_,
    );
    v___x_9792_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9792_, 0, v___x_9790_);
    crate::leanh::lean_ctor_set(v___x_9792_, 1, v___x_9791_);
    v___x_9793_ = crate::leanh::lean_box(0);
    v___x_9794_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_9792_,
        v_ext_9783_,
        v_env_9788_,
        v_asyncMode_9789_,
        v___x_9793_,
    );
    crate::leanh::lean_dec_ref_known(v___x_9792_, 2);
    v_snd_9795_ = crate::leanh::lean_ctor_get(v___x_9794_, 1);
    crate::leanh::lean_inc(v_snd_9795_);
    crate::leanh::lean_dec(v___x_9794_);
    v___x_9796_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v_inst_9781_,
        v_inst_9782_,
        v_snd_9795_,
        v_a_9784_,
    );
    crate::leanh::lean_dec(v_snd_9795_);
    v___x_9797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_9797_, 0, v___x_9796_);
    return v___x_9797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(
    mut v_inst_9798_: *mut crate::leanh::LeanObject,
    mut v_inst_9799_: *mut crate::leanh::LeanObject,
    mut v_ext_9800_: *mut crate::leanh::LeanObject,
    mut v_a_9801_: *mut crate::leanh::LeanObject,
    mut v_a_9802_: *mut crate::leanh::LeanObject,
    mut v_a_9803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9804_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(
        v_inst_9798_,
        v_inst_9799_,
        v_ext_9800_,
        v_a_9801_,
        v_a_9802_,
    );
    crate::leanh::lean_dec(v_a_9802_);
    crate::leanh::lean_dec_ref(v_ext_9800_);
    return v_res_9804_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f(
    mut v_00_u03b1_9805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9806_: *mut crate::leanh::LeanObject,
    mut v_inst_9807_: *mut crate::leanh::LeanObject,
    mut v_inst_9808_: *mut crate::leanh::LeanObject,
    mut v_inst_9809_: *mut crate::leanh::LeanObject,
    mut v_ext_9810_: *mut crate::leanh::LeanObject,
    mut v_a_9811_: *mut crate::leanh::LeanObject,
    mut v_a_9812_: *mut crate::leanh::LeanObject,
    mut v_a_9813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9815_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(
        v_inst_9807_,
        v_inst_9808_,
        v_ext_9810_,
        v_a_9811_,
        v_a_9813_,
    );
    return v___x_9815_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___boxed(
    mut v_00_u03b1_9816_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_9817_: *mut crate::leanh::LeanObject,
    mut v_inst_9818_: *mut crate::leanh::LeanObject,
    mut v_inst_9819_: *mut crate::leanh::LeanObject,
    mut v_inst_9820_: *mut crate::leanh::LeanObject,
    mut v_ext_9821_: *mut crate::leanh::LeanObject,
    mut v_a_9822_: *mut crate::leanh::LeanObject,
    mut v_a_9823_: *mut crate::leanh::LeanObject,
    mut v_a_9824_: *mut crate::leanh::LeanObject,
    mut v_a_9825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_9826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_9826_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f(
        v_00_u03b1_9816_,
        v_00_u03b2_9817_,
        v_inst_9818_,
        v_inst_9819_,
        v_inst_9820_,
        v_ext_9821_,
        v_a_9822_,
        v_a_9823_,
        v_a_9824_,
    );
    crate::leanh::lean_dec(v_a_9824_);
    crate::leanh::lean_dec_ref(v_a_9823_);
    crate::leanh::lean_dec_ref(v_ext_9821_);
    crate::leanh::lean_dec(v_inst_9820_);
    return v_res_9826_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_CompilerM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedPhase_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default();
    l_Lean_Compiler_LCNF_instInhabitedPhase = _init_l_Lean_Compiler_LCNF_instInhabitedPhase();
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedState =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext);
    l_Lean_Compiler_LCNF_instMonadCompilerM = _init_l_Lean_Compiler_LCNF_instMonadCompilerM();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instMonadCompilerM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_CompilerM(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_CompilerM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_CompilerM(builtin);
}
