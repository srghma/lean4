// Lean compiler output
// Module: Lean.Compiler.LCNF.CompilerM
// Imports: Lean.Compiler.LCNF.LCtx Lean.Compiler.LCNF.ConfigOptions
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::BasicAux::l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_List_foldl___redArg,
    l_List_lengthTR___redArg, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_5, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static mut l_Lean_Compiler_LCNF_instInhabitedPhase_default: u8 = 0;
pub static mut l_Lean_Compiler_LCNF_instInhabitedPhase: u8 = 0;
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instMonadCompilerM: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instAddMessageContextCompilerM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_getType___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_getType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getType___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getType___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getType___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getParam___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_getParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getParam___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getParam___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getParam___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getLetDecl___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getLetDecl___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getLetDecl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getFunDecl___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getFunDecl___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getFunDecl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 109, 112, 105, 108, 101, 114, 77, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 110, 111, 114, 109, 69, 120, 112, 114, 73, 109, 112, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 109, 112, 105, 108, 101, 114, 77, 0]};
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedNormFVarResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedNormFVarResult_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_addSubst___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addSubst___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_addSubst___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addSubst___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkParam___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_mkParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkParam___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__0_value) as *mut LeanObject,
        6531178163111358628 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkParam___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_mkLetDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__0_value) as *mut LeanObject,
        7699194985028780469 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkLetDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkLetDecl___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_mkFunDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__0_value) as *mut LeanObject,
        12317437071847932413 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_mkFunDecl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFunDecl___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__0_value)
                as *mut LeanObject,
            12958253247387092313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorIdx(mut v_x_4914_: u8) -> *mut LeanObject {
    match v_x_4914_ {
        0 => {
            let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
            v___x_4915_ = lean_unsigned_to_nat(0);
            return v___x_4915_;
        }
        1 => {
            let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
            v___x_4916_ = lean_unsigned_to_nat(1);
            return v___x_4916_;
        }
        _ => {
            let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
            v___x_4917_ = lean_unsigned_to_nat(2);
            return v___x_4917_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorIdx___boxed(
    mut v_x_4918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4919_: u8 = 0;
    let mut v_res_4920_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4919_ = (lean_unbox(v_x_4918_) as u8);
    v_res_4920_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_boxed_4919_);
    return v_res_4920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toCtorIdx(mut v_x_4921_: u8) -> *mut LeanObject {
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_4921_);
    return v___x_4922_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_toCtorIdx___boxed(
    mut v_x_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_4924_: u8 = 0;
    let mut v_res_4925_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4924_ = (lean_unbox(v_x_4923_) as u8);
    v_res_4925_ = l_Lean_Compiler_LCNF_Phase_toCtorIdx(v_x_4__boxed_4924_);
    return v_res_4925_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(
    mut v_k_4926_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4926_);
    return v_k_4926_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___redArg___boxed(
    mut v_k_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4928_: *mut LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_Compiler_LCNF_Phase_ctorElim___redArg(v_k_4927_);
    lean_dec(v_k_4927_);
    return v_res_4928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim(
    mut v_motive_4929_: *mut LeanObject,
    mut v_ctorIdx_4930_: *mut LeanObject,
    mut v_t_4931_: u8,
    mut v_h_4932_: *mut LeanObject,
    mut v_k_4933_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4933_);
    return v_k_4933_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ctorElim___boxed(
    mut v_motive_4934_: *mut LeanObject,
    mut v_ctorIdx_4935_: *mut LeanObject,
    mut v_t_4936_: *mut LeanObject,
    mut v_h_4937_: *mut LeanObject,
    mut v_k_4938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4939_: u8 = 0;
    let mut v_res_4940_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4939_ = (lean_unbox(v_t_4936_) as u8);
    v_res_4940_ = l_Lean_Compiler_LCNF_Phase_ctorElim(
        v_motive_4934_,
        v_ctorIdx_4935_,
        v_t_boxed_4939_,
        v_h_4937_,
        v_k_4938_,
    );
    lean_dec(v_k_4938_);
    lean_dec(v_ctorIdx_4935_);
    return v_res_4940_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___redArg(
    mut v_base_4941_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_base_4941_);
    return v_base_4941_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___redArg___boxed(
    mut v_base_4942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4943_: *mut LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_Compiler_LCNF_Phase_base_elim___redArg(v_base_4942_);
    lean_dec(v_base_4942_);
    return v_res_4943_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim(
    mut v_motive_4944_: *mut LeanObject,
    mut v_t_4945_: u8,
    mut v_h_4946_: *mut LeanObject,
    mut v_base_4947_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_base_4947_);
    return v_base_4947_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_base_elim___boxed(
    mut v_motive_4948_: *mut LeanObject,
    mut v_t_4949_: *mut LeanObject,
    mut v_h_4950_: *mut LeanObject,
    mut v_base_4951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4952_: u8 = 0;
    let mut v_res_4953_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4952_ = (lean_unbox(v_t_4949_) as u8);
    v_res_4953_ = l_Lean_Compiler_LCNF_Phase_base_elim(
        v_motive_4948_,
        v_t_boxed_4952_,
        v_h_4950_,
        v_base_4951_,
    );
    lean_dec(v_base_4951_);
    return v_res_4953_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(
    mut v_mono_4954_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_mono_4954_);
    return v_mono_4954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___redArg___boxed(
    mut v_mono_4955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4956_: *mut LeanObject = core::ptr::null_mut();
    v_res_4956_ = l_Lean_Compiler_LCNF_Phase_mono_elim___redArg(v_mono_4955_);
    lean_dec(v_mono_4955_);
    return v_res_4956_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim(
    mut v_motive_4957_: *mut LeanObject,
    mut v_t_4958_: u8,
    mut v_h_4959_: *mut LeanObject,
    mut v_mono_4960_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_mono_4960_);
    return v_mono_4960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_mono_elim___boxed(
    mut v_motive_4961_: *mut LeanObject,
    mut v_t_4962_: *mut LeanObject,
    mut v_h_4963_: *mut LeanObject,
    mut v_mono_4964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4965_: u8 = 0;
    let mut v_res_4966_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4965_ = (lean_unbox(v_t_4962_) as u8);
    v_res_4966_ = l_Lean_Compiler_LCNF_Phase_mono_elim(
        v_motive_4961_,
        v_t_boxed_4965_,
        v_h_4963_,
        v_mono_4964_,
    );
    lean_dec(v_mono_4964_);
    return v_res_4966_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(
    mut v_impure_4967_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_impure_4967_);
    return v_impure_4967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___redArg___boxed(
    mut v_impure_4968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4969_: *mut LeanObject = core::ptr::null_mut();
    v_res_4969_ = l_Lean_Compiler_LCNF_Phase_impure_elim___redArg(v_impure_4968_);
    lean_dec(v_impure_4968_);
    return v_res_4969_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim(
    mut v_motive_4970_: *mut LeanObject,
    mut v_t_4971_: u8,
    mut v_h_4972_: *mut LeanObject,
    mut v_impure_4973_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_impure_4973_);
    return v_impure_4973_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Phase_impure_elim___boxed(
    mut v_motive_4974_: *mut LeanObject,
    mut v_t_4975_: *mut LeanObject,
    mut v_h_4976_: *mut LeanObject,
    mut v_impure_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4978_: u8 = 0;
    let mut v_res_4979_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4978_ = (lean_unbox(v_t_4975_) as u8);
    v_res_4979_ = l_Lean_Compiler_LCNF_Phase_impure_elim(
        v_motive_4974_,
        v_t_boxed_4978_,
        v_h_4976_,
        v_impure_4977_,
    );
    lean_dec(v_impure_4977_);
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
pub unsafe fn l_Lean_Compiler_LCNF_Phase_ofNat(mut v_n_4982_: *mut LeanObject) -> u8 {
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    v___x_4983_ = lean_unsigned_to_nat(0);
    v___x_4984_ = lean_nat_dec_le(v_n_4982_, v___x_4983_);
    if v___x_4984_ == 0 {
        let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4986_: u8 = 0;
        v___x_4985_ = lean_unsigned_to_nat(1);
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
    mut v_n_4990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4991_: u8 = 0;
    let mut v_r_4992_: *mut LeanObject = core::ptr::null_mut();
    v_res_4991_ = l_Lean_Compiler_LCNF_Phase_ofNat(v_n_4990_);
    lean_dec(v_n_4990_);
    v_r_4992_ = lean_box((v_res_4991_) as usize);
    return v_r_4992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableEqPhase(
    mut v_x_4993_: u8,
    mut v_y_4994_: u8,
) -> u8 {
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: u8 = 0;
    v___x_4995_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_x_4993_);
    v___x_4996_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_y_4994_);
    v___x_4997_ = lean_nat_dec_eq(v___x_4995_, v___x_4996_);
    lean_dec(v___x_4996_);
    lean_dec(v___x_4995_);
    return v___x_4997_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instDecidableEqPhase___boxed(
    mut v_x_4998_: *mut LeanObject,
    mut v_y_4999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_5000_: u8 = 0;
    let mut v_y_14__boxed_5001_: u8 = 0;
    let mut v_res_5002_: u8 = 0;
    let mut v_r_5003_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_5000_ = (lean_unbox(v_x_4998_) as u8);
    v_y_14__boxed_5001_ = (lean_unbox(v_y_4999_) as u8);
    v_res_5002_ =
        l_Lean_Compiler_LCNF_instDecidableEqPhase(v_x_13__boxed_5000_, v_y_14__boxed_5001_);
    v_r_5003_ = lean_box((v_res_5002_) as usize);
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
    mut v_x_5007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_23__boxed_5008_: u8 = 0;
    let mut v_res_5009_: u8 = 0;
    let mut v_r_5010_: *mut LeanObject = core::ptr::null_mut();
    v_x_23__boxed_5008_ = (lean_unbox(v_x_5007_) as u8);
    v_res_5009_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_x_23__boxed_5008_);
    v_r_5010_ = lean_box((v_res_5009_) as usize);
    return v_r_5010_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0()
-> *mut LeanObject {
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    v___x_5011_ = lean_box(0);
    v___x_5012_ = lean_unsigned_to_nat(16);
    v___x_5013_ = lean_mk_array(v___x_5012_, v___x_5011_);
    return v___x_5013_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    v___x_5014_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__0,
    );
    v___x_5015_ = lean_unsigned_to_nat(0);
    v___x_5016_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5016_, 0, v___x_5015_);
    lean_ctor_set(v___x_5016_, 1, v___x_5014_);
    return v___x_5016_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    v___x_5017_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__1,
    );
    v___x_5018_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5018_, 0, v___x_5017_);
    lean_ctor_set(v___x_5018_, 1, v___x_5017_);
    lean_ctor_set(v___x_5018_, 2, v___x_5017_);
    lean_ctor_set(v___x_5018_, 3, v___x_5017_);
    lean_ctor_set(v___x_5018_, 4, v___x_5017_);
    lean_ctor_set(v___x_5018_, 5, v___x_5017_);
    return v___x_5018_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__3()
-> *mut LeanObject {
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    v___x_5019_ = lean_unsigned_to_nat(1);
    v___x_5020_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default___closed__2,
    );
    v___x_5021_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5021_, 0, v___x_5020_);
    lean_ctor_set(v___x_5021_, 1, v___x_5019_);
    return v___x_5021_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    v___x_5022_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState() -> *mut LeanObject {
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default;
    return v___x_5023_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default___closed__0()
-> *mut LeanObject {
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_Lean_Compiler_LCNF_instInhabitedConfigOptions_default;
    v___x_5025_ = 0;
    v___x_5026_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5026_, 0, v___x_5024_);
    lean_ctor_set_uint8(
        v___x_5026_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5025_,
    );
    return v___x_5026_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default() -> *mut LeanObject
{
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    v___x_5027_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext() -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    v___x_5028_ = l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default;
    return v___x_5028_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(
    mut v_00_u03b1_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    v___x_5036_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5036_, 0, v___y_5030_);
    return v___x_5036_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(
    mut v_00_u03b1_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
    mut v___y_5043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5044_: *mut LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0(
        v_00_u03b1_5037_,
        v___y_5038_,
        v___y_5039_,
        v___y_5040_,
        v___y_5041_,
        v___y_5042_,
    );
    lean_dec(v___y_5042_);
    lean_dec_ref(v___y_5041_);
    lean_dec(v___y_5040_);
    lean_dec_ref(v___y_5039_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(
    mut v_00_u03b1_5045_: *mut LeanObject,
    mut v_00_u03b2_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5060_: u8 = 0;
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5052_);
                lean_inc_ref(v___y_5051_);
                lean_inc(v___y_5050_);
                lean_inc_ref(v___y_5049_);
                v___x_5054_ = lean_apply_5(
                    v___y_5047_,
                    v___y_5049_,
                    v___y_5050_,
                    v___y_5051_,
                    v___y_5052_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5054_) == 0 {
                    v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
                    lean_inc(v_a_5055_);
                    lean_dec_ref_known(v___x_5054_, 1);
                    lean_inc(v___y_5052_);
                    lean_inc_ref(v___y_5051_);
                    lean_inc(v___y_5050_);
                    lean_inc_ref(v___y_5049_);
                    v___x_5056_ = lean_apply_6(
                        v___y_5048_,
                        v_a_5055_,
                        v___y_5049_,
                        v___y_5050_,
                        v___y_5051_,
                        v___y_5052_,
                        lean_box(0),
                    );
                    return v___x_5056_;
                } else {
                    lean_dec_ref(v___y_5048_);
                    v_a_5057_ = lean_ctor_get(v___x_5054_, 0);
                    v_isSharedCheck_5064_ = (!lean_is_exclusive(v___x_5054_)) as u8;
                    if v_isSharedCheck_5064_ == 0 {
                        v___x_5059_ = v___x_5054_;
                        v_isShared_5060_ = v_isSharedCheck_5064_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5057_);
                        lean_dec(v___x_5054_);
                        v___x_5059_ = lean_box(0);
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
                    v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
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
    mut v_00_u03b1_5065_: *mut LeanObject,
    mut v_00_u03b2_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5074_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5072_);
    lean_dec_ref(v___y_5071_);
    lean_dec(v___y_5070_);
    lean_dec_ref(v___y_5069_);
    return v_res_5074_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0() -> *mut LeanObject {
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    v___x_5075_ = l_instMonadEIO(lean_box(0));
    return v___x_5075_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1() -> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    v___x_5076_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0_once),
        _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__0,
    );
    v___x_5077_ = l_StateRefT_x27_instMonad___redArg(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instMonadCompilerM() -> *mut LeanObject {
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v_toFunctor_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___f_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut v_unused_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_unused_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5082_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1,
                );
                v_toApplicative_5083_ = lean_ctor_get(v___x_5082_, 0);
                v_toFunctor_5084_ = lean_ctor_get(v_toApplicative_5083_, 0);
                v_toSeq_5085_ = lean_ctor_get(v_toApplicative_5083_, 2);
                v_toSeqLeft_5086_ = lean_ctor_get(v_toApplicative_5083_, 3);
                v_toSeqRight_5087_ = lean_ctor_get(v_toApplicative_5083_, 4);
                v___f_5088_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2;
                v___f_5089_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3;
                lean_inc_ref_n(v_toFunctor_5084_, 2);
                v___f_5090_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5090_, 0, v_toFunctor_5084_);
                v___f_5091_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5091_, 0, v_toFunctor_5084_);
                v___x_5092_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5092_, 0, v___f_5090_);
                lean_ctor_set(v___x_5092_, 1, v___f_5091_);
                lean_inc(v_toSeqRight_5087_);
                v___f_5093_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5093_, 0, v_toSeqRight_5087_);
                lean_inc(v_toSeqLeft_5086_);
                v___f_5094_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5094_, 0, v_toSeqLeft_5086_);
                lean_inc(v_toSeq_5085_);
                v___f_5095_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5095_, 0, v_toSeq_5085_);
                v___x_5096_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5096_, 0, v___x_5092_);
                lean_ctor_set(v___x_5096_, 1, v___f_5088_);
                lean_ctor_set(v___x_5096_, 2, v___f_5095_);
                lean_ctor_set(v___x_5096_, 3, v___f_5094_);
                lean_ctor_set(v___x_5096_, 4, v___f_5093_);
                v___x_5097_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5097_, 0, v___x_5096_);
                lean_ctor_set(v___x_5097_, 1, v___f_5089_);
                v___x_5098_ = l_StateRefT_x27_instMonad___redArg(v___x_5097_);
                v_toApplicative_5099_ = lean_ctor_get(v___x_5098_, 0);
                v_isSharedCheck_5126_ = (!lean_is_exclusive(v___x_5098_)) as u8;
                if v_isSharedCheck_5126_ == 0 {
                    v_unused_5127_ = lean_ctor_get(v___x_5098_, 1);
                    lean_dec(v_unused_5127_);
                    v___x_5101_ = v___x_5098_;
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5099_);
                    lean_dec(v___x_5098_);
                    v___x_5101_ = lean_box(0);
                    v_isShared_5102_ = v_isSharedCheck_5126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5103_ = lean_ctor_get(v_toApplicative_5099_, 0);
                v_toSeq_5104_ = lean_ctor_get(v_toApplicative_5099_, 2);
                v_toSeqLeft_5105_ = lean_ctor_get(v_toApplicative_5099_, 3);
                v_toSeqRight_5106_ = lean_ctor_get(v_toApplicative_5099_, 4);
                v_isSharedCheck_5124_ = (!lean_is_exclusive(v_toApplicative_5099_)) as u8;
                if v_isSharedCheck_5124_ == 0 {
                    v_unused_5125_ = lean_ctor_get(v_toApplicative_5099_, 1);
                    lean_dec(v_unused_5125_);
                    v___x_5108_ = v_toApplicative_5099_;
                    v_isShared_5109_ = v_isSharedCheck_5124_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5106_);
                    lean_inc(v_toSeqLeft_5105_);
                    lean_inc(v_toSeq_5104_);
                    lean_inc(v_toFunctor_5103_);
                    lean_dec(v_toApplicative_5099_);
                    v___x_5108_ = lean_box(0);
                    v_isShared_5109_ = v_isSharedCheck_5124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5110_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4;
                v___f_5111_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5;
                lean_inc_ref(v_toFunctor_5103_);
                v___f_5112_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5112_, 0, v_toFunctor_5103_);
                v___f_5113_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5113_, 0, v_toFunctor_5103_);
                v___x_5114_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5114_, 0, v___f_5112_);
                lean_ctor_set(v___x_5114_, 1, v___f_5113_);
                v___f_5115_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5115_, 0, v_toSeqRight_5106_);
                v___f_5116_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5116_, 0, v_toSeqLeft_5105_);
                v___f_5117_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5117_, 0, v_toSeq_5104_);
                if v_isShared_5109_ == 0 {
                    lean_ctor_set(v___x_5108_, 4, v___f_5115_);
                    lean_ctor_set(v___x_5108_, 3, v___f_5116_);
                    lean_ctor_set(v___x_5108_, 2, v___f_5117_);
                    lean_ctor_set(v___x_5108_, 1, v___f_5110_);
                    lean_ctor_set(v___x_5108_, 0, v___x_5114_);
                    v___x_5119_ = v___x_5108_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5123_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5114_);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 1, v___f_5110_);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 2, v___f_5117_);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 3, v___f_5116_);
                    lean_ctor_set(v_reuseFailAlloc_5123_, 4, v___f_5115_);
                    v___x_5119_ = v_reuseFailAlloc_5123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5102_ == 0 {
                    lean_ctor_set(v___x_5101_, 1, v___f_5111_);
                    lean_ctor_set(v___x_5101_, 0, v___x_5119_);
                    v___x_5121_ = v___x_5101_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
                    lean_ctor_set(v_reuseFailAlloc_5122_, 1, v___f_5111_);
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
    mut v_x_5129_: *mut LeanObject,
    mut v_a_5130_: *mut LeanObject,
    mut v_a_5131_: *mut LeanObject,
    mut v_a_5132_: *mut LeanObject,
    mut v_a_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    v_config_5135_ = lean_ctor_get(v_a_5130_, 0);
    lean_inc_ref(v_config_5135_);
    v___x_5136_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5136_, 0, v_config_5135_);
    lean_ctor_set_uint8(
        v___x_5136_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_phase_5128_,
    );
    lean_inc(v_a_5133_);
    lean_inc_ref(v_a_5132_);
    lean_inc(v_a_5131_);
    v___x_5137_ = lean_apply_5(
        v_x_5129_,
        v___x_5136_,
        v_a_5131_,
        v_a_5132_,
        v_a_5133_,
        lean_box(0),
    );
    return v___x_5137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase___redArg___boxed(
    mut v_phase_5138_: *mut LeanObject,
    mut v_x_5139_: *mut LeanObject,
    mut v_a_5140_: *mut LeanObject,
    mut v_a_5141_: *mut LeanObject,
    mut v_a_5142_: *mut LeanObject,
    mut v_a_5143_: *mut LeanObject,
    mut v_a_5144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_5145_: u8 = 0;
    let mut v_res_5146_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_5145_ = (lean_unbox(v_phase_5138_) as u8);
    v_res_5146_ = l_Lean_Compiler_LCNF_withPhase___redArg(
        v_phase_boxed_5145_,
        v_x_5139_,
        v_a_5140_,
        v_a_5141_,
        v_a_5142_,
        v_a_5143_,
    );
    lean_dec(v_a_5143_);
    lean_dec_ref(v_a_5142_);
    lean_dec(v_a_5141_);
    lean_dec_ref(v_a_5140_);
    return v_res_5146_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase(
    mut v_00_u03b1_5147_: *mut LeanObject,
    mut v_phase_5148_: u8,
    mut v_x_5149_: *mut LeanObject,
    mut v_a_5150_: *mut LeanObject,
    mut v_a_5151_: *mut LeanObject,
    mut v_a_5152_: *mut LeanObject,
    mut v_a_5153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    v_config_5155_ = lean_ctor_get(v_a_5150_, 0);
    lean_inc_ref(v_config_5155_);
    v___x_5156_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_5156_, 0, v_config_5155_);
    lean_ctor_set_uint8(
        v___x_5156_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_phase_5148_,
    );
    lean_inc(v_a_5153_);
    lean_inc_ref(v_a_5152_);
    lean_inc(v_a_5151_);
    v___x_5157_ = lean_apply_5(
        v_x_5149_,
        v___x_5156_,
        v_a_5151_,
        v_a_5152_,
        v_a_5153_,
        lean_box(0),
    );
    return v___x_5157_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withPhase___boxed(
    mut v_00_u03b1_5158_: *mut LeanObject,
    mut v_phase_5159_: *mut LeanObject,
    mut v_x_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
    mut v_a_5162_: *mut LeanObject,
    mut v_a_5163_: *mut LeanObject,
    mut v_a_5164_: *mut LeanObject,
    mut v_a_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_5166_: u8 = 0;
    let mut v_res_5167_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_5166_ = (lean_unbox(v_phase_5159_) as u8);
    v_res_5167_ = l_Lean_Compiler_LCNF_withPhase(
        v_00_u03b1_5158_,
        v_phase_boxed_5166_,
        v_x_5160_,
        v_a_5161_,
        v_a_5162_,
        v_a_5163_,
        v_a_5164_,
    );
    lean_dec(v_a_5164_);
    lean_dec_ref(v_a_5163_);
    lean_dec(v_a_5162_);
    lean_dec_ref(v_a_5161_);
    return v_res_5167_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___redArg(
    mut v_a_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_5170_: u8 = 0;
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    v_phase_5170_ = lean_ctor_get_uint8(
        v_a_5168_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_5171_ = lean_box((v_phase_5170_) as usize);
    v___x_5172_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5172_, 0, v___x_5171_);
    return v___x_5172_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___redArg___boxed(
    mut v_a_5173_: *mut LeanObject,
    mut v_a_5174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5175_: *mut LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5173_);
    lean_dec_ref(v_a_5173_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase(
    mut v_a_5176_: *mut LeanObject,
    mut v_a_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v_a_5179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    v___x_5181_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5176_);
    return v___x_5181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPhase___boxed(
    mut v_a_5182_: *mut LeanObject,
    mut v_a_5183_: *mut LeanObject,
    mut v_a_5184_: *mut LeanObject,
    mut v_a_5185_: *mut LeanObject,
    mut v_a_5186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5187_: *mut LeanObject = core::ptr::null_mut();
    v_res_5187_ = l_Lean_Compiler_LCNF_getPhase(v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
    lean_dec(v_a_5185_);
    lean_dec_ref(v_a_5184_);
    lean_dec(v_a_5183_);
    lean_dec_ref(v_a_5182_);
    return v_res_5187_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity___redArg(
    mut v_a_5188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5190_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5188_);
                v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
                v_isSharedCheck_5201_ = (!lean_is_exclusive(v___x_5190_)) as u8;
                if v_isSharedCheck_5201_ == 0 {
                    v___x_5193_ = v___x_5190_;
                    v_isShared_5194_ = v_isSharedCheck_5201_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5191_);
                    lean_dec(v___x_5190_);
                    v___x_5193_ = lean_box(0);
                    v_isShared_5194_ = v_isSharedCheck_5201_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5195_ = (lean_unbox(v_a_5191_) as u8);
                lean_dec(v_a_5191_);
                v___x_5196_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_5195_);
                v___x_5197_ = lean_box((v___x_5196_) as usize);
                if v_isShared_5194_ == 0 {
                    lean_ctor_set(v___x_5193_, 0, v___x_5197_);
                    v___x_5199_ = v___x_5193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5197_);
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
    mut v_a_5202_: *mut LeanObject,
    mut v_a_5203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5204_: *mut LeanObject = core::ptr::null_mut();
    v_res_5204_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5202_);
    lean_dec_ref(v_a_5202_);
    return v_res_5204_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity(
    mut v_a_5205_: *mut LeanObject,
    mut v_a_5206_: *mut LeanObject,
    mut v_a_5207_: *mut LeanObject,
    mut v_a_5208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5205_);
    return v___x_5210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPurity___boxed(
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5216_: *mut LeanObject = core::ptr::null_mut();
    v_res_5216_ = l_Lean_Compiler_LCNF_getPurity(v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
    lean_dec(v_a_5214_);
    lean_dec_ref(v_a_5213_);
    lean_dec(v_a_5212_);
    lean_dec_ref(v_a_5211_);
    return v_res_5216_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase___redArg(
    mut v_a_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5223_: u8 = 0;
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: u8 = 0;
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5219_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_5217_);
                v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
                v_isSharedCheck_5235_ = (!lean_is_exclusive(v___x_5219_)) as u8;
                if v_isSharedCheck_5235_ == 0 {
                    v___x_5222_ = v___x_5219_;
                    v_isShared_5223_ = v_isSharedCheck_5235_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5220_);
                    lean_dec(v___x_5219_);
                    v___x_5222_ = lean_box(0);
                    v_isShared_5223_ = v_isSharedCheck_5235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5224_ = (lean_unbox(v_a_5220_) as u8);
                lean_dec(v_a_5220_);
                if v___x_5224_ == 0 {
                    v___x_5225_ = 1;
                    v___x_5226_ = lean_box((v___x_5225_) as usize);
                    if v_isShared_5223_ == 0 {
                        lean_ctor_set(v___x_5222_, 0, v___x_5226_);
                        v___x_5228_ = v___x_5222_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
                        v___x_5228_ = v_reuseFailAlloc_5229_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5230_ = 0;
                    v___x_5231_ = lean_box((v___x_5230_) as usize);
                    if v_isShared_5223_ == 0 {
                        lean_ctor_set(v___x_5222_, 0, v___x_5231_);
                        v___x_5233_ = v___x_5222_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
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
    mut v_a_5236_: *mut LeanObject,
    mut v_a_5237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5238_: *mut LeanObject = core::ptr::null_mut();
    v_res_5238_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_5236_);
    lean_dec_ref(v_a_5236_);
    return v_res_5238_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase(
    mut v_a_5239_: *mut LeanObject,
    mut v_a_5240_: *mut LeanObject,
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    v___x_5244_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v_a_5239_);
    return v___x_5244_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inBasePhase___boxed(
    mut v_a_5245_: *mut LeanObject,
    mut v_a_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
    mut v_a_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5250_: *mut LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_Compiler_LCNF_inBasePhase(v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_);
    lean_dec(v_a_5248_);
    lean_dec_ref(v_a_5247_);
    lean_dec(v_a_5246_);
    lean_dec_ref(v_a_5245_);
    return v_res_5250_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5251_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    v___x_5252_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__0,
    );
    v___x_5253_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5253_, 0, v___x_5252_);
    return v___x_5253_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    v___x_5254_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__1,
    );
    v___x_5255_ = lean_unsigned_to_nat(0);
    v___x_5256_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5256_, 0, v___x_5255_);
    lean_ctor_set(v___x_5256_, 1, v___x_5255_);
    lean_ctor_set(v___x_5256_, 2, v___x_5255_);
    lean_ctor_set(v___x_5256_, 3, v___x_5255_);
    lean_ctor_set(v___x_5256_, 4, v___x_5254_);
    lean_ctor_set(v___x_5256_, 5, v___x_5254_);
    lean_ctor_set(v___x_5256_, 6, v___x_5254_);
    lean_ctor_set(v___x_5256_, 7, v___x_5254_);
    lean_ctor_set(v___x_5256_, 8, v___x_5254_);
    lean_ctor_set(v___x_5256_, 9, v___x_5254_);
    return v___x_5256_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(
    mut v_msgData_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v_env_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v_options_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: u8 = 0;
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut v_unused_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5263_ = lean_st_ref_get(v___y_5261_);
                v___x_5264_ = lean_st_ref_get(v___y_5259_);
                v___x_5265_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5258_);
                if lean_obj_tag(v___x_5265_) == 0 {
                    v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5288_ = (!lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5288_ == 0 {
                        v___x_5268_ = v___x_5265_;
                        v_isShared_5269_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5266_);
                        lean_dec(v___x_5265_);
                        v___x_5268_ = lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5288_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5264_);
                    lean_dec(v___x_5263_);
                    lean_dec_ref(v_msgData_5257_);
                    v_a_5289_ = lean_ctor_get(v___x_5265_, 0);
                    v_isSharedCheck_5296_ = (!lean_is_exclusive(v___x_5265_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5291_ = v___x_5265_;
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5289_);
                        lean_dec(v___x_5265_);
                        v___x_5291_ = lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_5270_ = lean_ctor_get(v___x_5263_, 0);
                lean_inc_ref(v_env_5270_);
                lean_dec(v___x_5263_);
                v_lctx_5271_ = lean_ctor_get(v___x_5264_, 0);
                v_isSharedCheck_5286_ = (!lean_is_exclusive(v___x_5264_)) as u8;
                if v_isSharedCheck_5286_ == 0 {
                    v_unused_5287_ = lean_ctor_get(v___x_5264_, 1);
                    lean_dec(v_unused_5287_);
                    v___x_5273_ = v___x_5264_;
                    v_isShared_5274_ = v_isSharedCheck_5286_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_5271_);
                    lean_dec(v___x_5264_);
                    v___x_5273_ = lean_box(0);
                    v_isShared_5274_ = v_isSharedCheck_5286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_options_5275_ = lean_ctor_get(v___y_5260_, 2);
                v___x_5276_ = (lean_unbox(v_a_5266_) as u8);
                lean_dec(v_a_5266_);
                v___x_5277_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5271_, v___x_5276_);
                lean_dec_ref(v_lctx_5271_);
                v___x_5278_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
                lean_inc_ref(v_options_5275_);
                v___x_5279_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5279_, 0, v_env_5270_);
                lean_ctor_set(v___x_5279_, 1, v___x_5278_);
                lean_ctor_set(v___x_5279_, 2, v___x_5277_);
                lean_ctor_set(v___x_5279_, 3, v_options_5275_);
                if v_isShared_5274_ == 0 {
                    lean_ctor_set_tag(v___x_5273_, 3);
                    lean_ctor_set(v___x_5273_, 1, v_msgData_5257_);
                    lean_ctor_set(v___x_5273_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5273_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5279_);
                    lean_ctor_set(v_reuseFailAlloc_5285_, 1, v_msgData_5257_);
                    v___x_5281_ = v_reuseFailAlloc_5285_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5269_ == 0 {
                    lean_ctor_set(v___x_5268_, 0, v___x_5281_);
                    v___x_5283_ = v___x_5268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5281_);
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
                    v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
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
    mut v_msgData_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
    mut v___y_5301_: *mut LeanObject,
    mut v___y_5302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5303_: *mut LeanObject = core::ptr::null_mut();
    v_res_5303_ = l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0(
        v_msgData_5297_,
        v___y_5298_,
        v___y_5299_,
        v___y_5300_,
        v___y_5301_,
    );
    lean_dec(v___y_5301_);
    lean_dec_ref(v___y_5300_);
    lean_dec(v___y_5299_);
    lean_dec_ref(v___y_5298_);
    return v_res_5303_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
    mut v_msg_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v_env_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v___x_5326_: u8 = 0;
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_unused_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5312_ = lean_ctor_get(v___y_5309_, 2);
                v_ref_5313_ = lean_ctor_get(v___y_5309_, 5);
                v___x_5314_ = lean_st_ref_get(v___y_5310_);
                v___x_5315_ = lean_st_ref_get(v___y_5308_);
                v___x_5316_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5307_);
                if lean_obj_tag(v___x_5316_) == 0 {
                    v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
                    v_isSharedCheck_5339_ = (!lean_is_exclusive(v___x_5316_)) as u8;
                    if v_isSharedCheck_5339_ == 0 {
                        v___x_5319_ = v___x_5316_;
                        v_isShared_5320_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5317_);
                        lean_dec(v___x_5316_);
                        v___x_5319_ = lean_box(0);
                        v_isShared_5320_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5315_);
                    lean_dec(v___x_5314_);
                    lean_dec_ref(v_msg_5306_);
                    v_a_5340_ = lean_ctor_get(v___x_5316_, 0);
                    v_isSharedCheck_5347_ = (!lean_is_exclusive(v___x_5316_)) as u8;
                    if v_isSharedCheck_5347_ == 0 {
                        v___x_5342_ = v___x_5316_;
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5340_);
                        lean_dec(v___x_5316_);
                        v___x_5342_ = lean_box(0);
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_5321_ = lean_ctor_get(v___x_5314_, 0);
                lean_inc_ref(v_env_5321_);
                lean_dec(v___x_5314_);
                v_lctx_5322_ = lean_ctor_get(v___x_5315_, 0);
                v_isSharedCheck_5337_ = (!lean_is_exclusive(v___x_5315_)) as u8;
                if v_isSharedCheck_5337_ == 0 {
                    v_unused_5338_ = lean_ctor_get(v___x_5315_, 1);
                    lean_dec(v_unused_5338_);
                    v___x_5324_ = v___x_5315_;
                    v_isShared_5325_ = v_isSharedCheck_5337_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_5322_);
                    lean_dec(v___x_5315_);
                    v___x_5324_ = lean_box(0);
                    v_isShared_5325_ = v_isSharedCheck_5337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5326_ = (lean_unbox(v_a_5317_) as u8);
                lean_dec(v_a_5317_);
                v___x_5327_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5322_, v___x_5326_);
                lean_dec_ref(v_lctx_5322_);
                v___x_5328_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___closed__2);
                lean_inc_ref(v_options_5312_);
                v___x_5329_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5329_, 0, v_env_5321_);
                lean_ctor_set(v___x_5329_, 1, v___x_5328_);
                lean_ctor_set(v___x_5329_, 2, v___x_5327_);
                lean_ctor_set(v___x_5329_, 3, v_options_5312_);
                if v_isShared_5325_ == 0 {
                    lean_ctor_set_tag(v___x_5324_, 3);
                    lean_ctor_set(v___x_5324_, 1, v_msg_5306_);
                    lean_ctor_set(v___x_5324_, 0, v___x_5329_);
                    v___x_5331_ = v___x_5324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5329_);
                    lean_ctor_set(v_reuseFailAlloc_5336_, 1, v_msg_5306_);
                    v___x_5331_ = v_reuseFailAlloc_5336_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_5313_);
                v___x_5332_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5332_, 0, v_ref_5313_);
                lean_ctor_set(v___x_5332_, 1, v___x_5331_);
                if v_isShared_5320_ == 0 {
                    lean_ctor_set_tag(v___x_5319_, 1);
                    lean_ctor_set(v___x_5319_, 0, v___x_5332_);
                    v___x_5334_ = v___x_5319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
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
                    v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
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
    mut v_msg_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
    mut v___y_5351_: *mut LeanObject,
    mut v___y_5352_: *mut LeanObject,
    mut v___y_5353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5354_: *mut LeanObject = core::ptr::null_mut();
    v_res_5354_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1___redArg(
        v_msg_5348_,
        v___y_5349_,
        v___y_5350_,
        v___y_5351_,
        v___y_5352_,
    );
    lean_dec(v___y_5352_);
    lean_dec_ref(v___y_5351_);
    lean_dec(v___y_5350_);
    lean_dec_ref(v___y_5349_);
    return v_res_5354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(
    mut v_00_u03b1_5355_: *mut LeanObject,
    mut v_msg_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
    mut v___y_5360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5363_: *mut LeanObject,
    mut v_msg_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5370_: *mut LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getType_spec__1(
        v_00_u03b1_5363_,
        v_msg_5364_,
        v___y_5365_,
        v___y_5366_,
        v___y_5367_,
        v___y_5368_,
    );
    lean_dec(v___y_5368_);
    lean_dec_ref(v___y_5367_);
    lean_dec(v___y_5366_);
    lean_dec_ref(v___y_5365_);
    return v_res_5370_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(
    mut v_a_5371_: *mut LeanObject,
    mut v_x_5372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5372_) == 0 {
                    v___x_5373_ = lean_box(0);
                    return v___x_5373_;
                } else {
                    v_key_5374_ = lean_ctor_get(v_x_5372_, 0);
                    v_value_5375_ = lean_ctor_get(v_x_5372_, 1);
                    v_tail_5376_ = lean_ctor_get(v_x_5372_, 2);
                    v___x_5377_ = l_Lean_instBEqFVarId_beq(v_key_5374_, v_a_5371_);
                    if v___x_5377_ == 0 {
                        v_x_5372_ = v_tail_5376_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_5375_);
                        v___x_5379_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5379_, 0, v_value_5375_);
                        return v___x_5379_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg___boxed(
    mut v_a_5380_: *mut LeanObject,
    mut v_x_5381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5382_: *mut LeanObject = core::ptr::null_mut();
    v_res_5382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_5380_, v_x_5381_);
    lean_dec(v_x_5381_);
    lean_dec(v_a_5380_);
    return v_res_5382_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(
    mut v_m_5383_: *mut LeanObject,
    mut v_a_5384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_5385_ = lean_ctor_get(v_m_5383_, 1);
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
    mut v_m_5401_: *mut LeanObject,
    mut v_a_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5403_: *mut LeanObject = core::ptr::null_mut();
    v_res_5403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_5401_, v_a_5402_);
    lean_dec(v_a_5402_);
    lean_dec_ref(v_m_5401_);
    return v_res_5403_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getType___closed__1() -> *mut LeanObject {
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    v___x_5405_ = l_Lean_Compiler_LCNF_getType___closed__0;
    v___x_5406_ = l_Lean_stringToMessageData(v___x_5405_);
    return v___x_5406_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getType(
    mut v_fvarId_5407_: *mut LeanObject,
    mut v_a_5408_: *mut LeanObject,
    mut v_a_5409_: *mut LeanObject,
    mut v_a_5410_: *mut LeanObject,
    mut v_a_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5418_: u8 = 0;
    let mut v___y_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5438_: u8 = 0;
    let mut v_type_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut v___x_5444_: u8 = 0;
    let mut v_funDeclsPure_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5453_: u8 = 0;
    let mut v_type_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v___x_5459_: u8 = 0;
    let mut v_paramsPure_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: u8 = 0;
    let mut v_letDeclsPure_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut v_a_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5469_: u8 = 0;
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5413_ = lean_st_ref_get(v_a_5409_);
                v___x_5414_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5408_);
                if lean_obj_tag(v___x_5414_) == 0 {
                    v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
                    v_isSharedCheck_5465_ = (!lean_is_exclusive(v___x_5414_)) as u8;
                    if v_isSharedCheck_5465_ == 0 {
                        v___x_5417_ = v___x_5414_;
                        v_isShared_5418_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5415_);
                        lean_dec(v___x_5414_);
                        v___x_5417_ = lean_box(0);
                        v_isShared_5418_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5413_);
                    lean_dec(v_fvarId_5407_);
                    v_a_5466_ = lean_ctor_get(v___x_5414_, 0);
                    v_isSharedCheck_5473_ = (!lean_is_exclusive(v___x_5414_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5468_ = v___x_5414_;
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5466_);
                        lean_dec(v___x_5414_);
                        v___x_5468_ = lean_box(0);
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_5431_ = lean_ctor_get(v___x_5413_, 0);
                lean_inc_ref(v_lctx_5431_);
                lean_dec(v___x_5413_);
                v___x_5462_ = (lean_unbox(v_a_5415_) as u8);
                if v___x_5462_ == 0 {
                    v_letDeclsPure_5463_ = lean_ctor_get(v_lctx_5431_, 2);
                    lean_inc_ref(v_letDeclsPure_5463_);
                    v___y_5448_ = v_letDeclsPure_5463_;
                    state = 7;
                    continue;
                } else {
                    v_letDeclsImpure_5464_ = lean_ctor_get(v_lctx_5431_, 3);
                    lean_inc_ref(v_letDeclsImpure_5464_);
                    v___y_5448_ = v_letDeclsImpure_5464_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_5421_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5420_, v_fvarId_5407_);
                lean_dec_ref(v___y_5420_);
                if lean_obj_tag(v___x_5421_) == 1 {
                    lean_dec(v_fvarId_5407_);
                    v_val_5422_ = lean_ctor_get(v___x_5421_, 0);
                    lean_inc(v_val_5422_);
                    lean_dec_ref_known(v___x_5421_, 1);
                    v_type_5423_ = lean_ctor_get(v_val_5422_, 3);
                    lean_inc_ref(v_type_5423_);
                    lean_dec(v_val_5422_);
                    if v_isShared_5418_ == 0 {
                        lean_ctor_set(v___x_5417_, 0, v_type_5423_);
                        v___x_5425_ = v___x_5417_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_type_5423_);
                        v___x_5425_ = v_reuseFailAlloc_5426_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5421_);
                    lean_del_object(v___x_5417_);
                    v___x_5427_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getType___closed__1,
                    );
                    v___x_5428_ = l_Lean_MessageData_ofName(v_fvarId_5407_);
                    v___x_5429_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5429_, 0, v___x_5427_);
                    lean_ctor_set(v___x_5429_, 1, v___x_5428_);
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
                lean_dec_ref(v___y_5433_);
                if lean_obj_tag(v___x_5434_) == 1 {
                    lean_dec_ref(v_lctx_5431_);
                    lean_del_object(v___x_5417_);
                    lean_dec(v_a_5415_);
                    lean_dec(v_fvarId_5407_);
                    v_val_5435_ = lean_ctor_get(v___x_5434_, 0);
                    v_isSharedCheck_5443_ = (!lean_is_exclusive(v___x_5434_)) as u8;
                    if v_isSharedCheck_5443_ == 0 {
                        v___x_5437_ = v___x_5434_;
                        v_isShared_5438_ = v_isSharedCheck_5443_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_5435_);
                        lean_dec(v___x_5434_);
                        v___x_5437_ = lean_box(0);
                        v_isShared_5438_ = v_isSharedCheck_5443_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5434_);
                    v___x_5444_ = (lean_unbox(v_a_5415_) as u8);
                    lean_dec(v_a_5415_);
                    if v___x_5444_ == 0 {
                        v_funDeclsPure_5445_ = lean_ctor_get(v_lctx_5431_, 4);
                        lean_inc_ref(v_funDeclsPure_5445_);
                        lean_dec_ref(v_lctx_5431_);
                        v___y_5420_ = v_funDeclsPure_5445_;
                        state = 2;
                        continue;
                    } else {
                        v_funDeclsImpure_5446_ = lean_ctor_get(v_lctx_5431_, 5);
                        lean_inc_ref(v_funDeclsImpure_5446_);
                        lean_dec_ref(v_lctx_5431_);
                        v___y_5420_ = v_funDeclsImpure_5446_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_type_5439_ = lean_ctor_get(v_val_5435_, 2);
                lean_inc_ref(v_type_5439_);
                lean_dec(v_val_5435_);
                if v_isShared_5438_ == 0 {
                    lean_ctor_set_tag(v___x_5437_, 0);
                    lean_ctor_set(v___x_5437_, 0, v_type_5439_);
                    v___x_5441_ = v___x_5437_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_type_5439_);
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
                lean_dec_ref(v___y_5448_);
                if lean_obj_tag(v___x_5449_) == 1 {
                    lean_dec_ref(v_lctx_5431_);
                    lean_del_object(v___x_5417_);
                    lean_dec(v_a_5415_);
                    lean_dec(v_fvarId_5407_);
                    v_val_5450_ = lean_ctor_get(v___x_5449_, 0);
                    v_isSharedCheck_5458_ = (!lean_is_exclusive(v___x_5449_)) as u8;
                    if v_isSharedCheck_5458_ == 0 {
                        v___x_5452_ = v___x_5449_;
                        v_isShared_5453_ = v_isSharedCheck_5458_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_5450_);
                        lean_dec(v___x_5449_);
                        v___x_5452_ = lean_box(0);
                        v_isShared_5453_ = v_isSharedCheck_5458_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5449_);
                    v___x_5459_ = (lean_unbox(v_a_5415_) as u8);
                    if v___x_5459_ == 0 {
                        v_paramsPure_5460_ = lean_ctor_get(v_lctx_5431_, 0);
                        lean_inc_ref(v_paramsPure_5460_);
                        v___y_5433_ = v_paramsPure_5460_;
                        state = 4;
                        continue;
                    } else {
                        v_paramsImpure_5461_ = lean_ctor_get(v_lctx_5431_, 1);
                        lean_inc_ref(v_paramsImpure_5461_);
                        v___y_5433_ = v_paramsImpure_5461_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v_type_5454_ = lean_ctor_get(v_val_5450_, 2);
                lean_inc_ref(v_type_5454_);
                lean_dec(v_val_5450_);
                if v_isShared_5453_ == 0 {
                    lean_ctor_set_tag(v___x_5452_, 0);
                    lean_ctor_set(v___x_5452_, 0, v_type_5454_);
                    v___x_5456_ = v___x_5452_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_type_5454_);
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
                    v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
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
    mut v_fvarId_5474_: *mut LeanObject,
    mut v_a_5475_: *mut LeanObject,
    mut v_a_5476_: *mut LeanObject,
    mut v_a_5477_: *mut LeanObject,
    mut v_a_5478_: *mut LeanObject,
    mut v_a_5479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5480_: *mut LeanObject = core::ptr::null_mut();
    v_res_5480_ =
        l_Lean_Compiler_LCNF_getType(v_fvarId_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_);
    lean_dec(v_a_5478_);
    lean_dec_ref(v_a_5477_);
    lean_dec(v_a_5476_);
    lean_dec_ref(v_a_5475_);
    return v_res_5480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(
    mut v_00_u03b2_5481_: *mut LeanObject,
    mut v_m_5482_: *mut LeanObject,
    mut v_a_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    v___x_5484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_m_5482_, v_a_5483_);
    return v___x_5484_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___boxed(
    mut v_00_u03b2_5485_: *mut LeanObject,
    mut v_m_5486_: *mut LeanObject,
    mut v_a_5487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5488_: *mut LeanObject = core::ptr::null_mut();
    v_res_5488_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0(
            v_00_u03b2_5485_,
            v_m_5486_,
            v_a_5487_,
        );
    lean_dec(v_a_5487_);
    lean_dec_ref(v_m_5486_);
    return v_res_5488_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(
    mut v_00_u03b2_5489_: *mut LeanObject,
    mut v_a_5490_: *mut LeanObject,
    mut v_x_5491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    v___x_5492_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___redArg(v_a_5490_, v_x_5491_);
    return v___x_5492_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0___boxed(
    mut v_00_u03b2_5493_: *mut LeanObject,
    mut v_a_5494_: *mut LeanObject,
    mut v_x_5495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5496_: *mut LeanObject = core::ptr::null_mut();
    v_res_5496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0_spec__0(v_00_u03b2_5493_, v_a_5494_, v_x_5495_);
    lean_dec(v_x_5495_);
    lean_dec(v_a_5494_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getBinderName(
    mut v_fvarId_5497_: *mut LeanObject,
    mut v_a_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
    mut v_a_5500_: *mut LeanObject,
    mut v_a_5501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5508_: u8 = 0;
    let mut v___y_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v_binderName_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5533_: u8 = 0;
    let mut v___x_5534_: u8 = 0;
    let mut v_funDeclsPure_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v_binderName_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut v___x_5549_: u8 = 0;
    let mut v_paramsPure_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v_letDeclsPure_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5555_: u8 = 0;
    let mut v_a_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5503_ = lean_st_ref_get(v_a_5499_);
                v___x_5504_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_5498_);
                if lean_obj_tag(v___x_5504_) == 0 {
                    v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5555_ = (!lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5555_ == 0 {
                        v___x_5507_ = v___x_5504_;
                        v_isShared_5508_ = v_isSharedCheck_5555_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5505_);
                        lean_dec(v___x_5504_);
                        v___x_5507_ = lean_box(0);
                        v_isShared_5508_ = v_isSharedCheck_5555_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5503_);
                    lean_dec(v_fvarId_5497_);
                    v_a_5556_ = lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5563_ = (!lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5563_ == 0 {
                        v___x_5558_ = v___x_5504_;
                        v_isShared_5559_ = v_isSharedCheck_5563_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5556_);
                        lean_dec(v___x_5504_);
                        v___x_5558_ = lean_box(0);
                        v_isShared_5559_ = v_isSharedCheck_5563_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_5521_ = lean_ctor_get(v___x_5503_, 0);
                lean_inc_ref(v_lctx_5521_);
                lean_dec(v___x_5503_);
                v___x_5552_ = (lean_unbox(v_a_5505_) as u8);
                if v___x_5552_ == 0 {
                    v_letDeclsPure_5553_ = lean_ctor_get(v_lctx_5521_, 2);
                    lean_inc_ref(v_letDeclsPure_5553_);
                    v___y_5538_ = v_letDeclsPure_5553_;
                    state = 7;
                    continue;
                } else {
                    v_letDeclsImpure_5554_ = lean_ctor_get(v_lctx_5521_, 3);
                    lean_inc_ref(v_letDeclsImpure_5554_);
                    v___y_5538_ = v_letDeclsImpure_5554_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v___x_5511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5510_, v_fvarId_5497_);
                lean_dec_ref(v___y_5510_);
                if lean_obj_tag(v___x_5511_) == 1 {
                    lean_dec(v_fvarId_5497_);
                    v_val_5512_ = lean_ctor_get(v___x_5511_, 0);
                    lean_inc(v_val_5512_);
                    lean_dec_ref_known(v___x_5511_, 1);
                    v_binderName_5513_ = lean_ctor_get(v_val_5512_, 1);
                    lean_inc(v_binderName_5513_);
                    lean_dec(v_val_5512_);
                    if v_isShared_5508_ == 0 {
                        lean_ctor_set(v___x_5507_, 0, v_binderName_5513_);
                        v___x_5515_ = v___x_5507_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_binderName_5513_);
                        v___x_5515_ = v_reuseFailAlloc_5516_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5511_);
                    lean_del_object(v___x_5507_);
                    v___x_5517_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getType___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getType___closed__1,
                    );
                    v___x_5518_ = l_Lean_MessageData_ofName(v_fvarId_5497_);
                    v___x_5519_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5519_, 0, v___x_5517_);
                    lean_ctor_set(v___x_5519_, 1, v___x_5518_);
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
                lean_dec_ref(v___y_5523_);
                if lean_obj_tag(v___x_5524_) == 1 {
                    lean_dec_ref(v_lctx_5521_);
                    lean_del_object(v___x_5507_);
                    lean_dec(v_a_5505_);
                    lean_dec(v_fvarId_5497_);
                    v_val_5525_ = lean_ctor_get(v___x_5524_, 0);
                    v_isSharedCheck_5533_ = (!lean_is_exclusive(v___x_5524_)) as u8;
                    if v_isSharedCheck_5533_ == 0 {
                        v___x_5527_ = v___x_5524_;
                        v_isShared_5528_ = v_isSharedCheck_5533_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_5525_);
                        lean_dec(v___x_5524_);
                        v___x_5527_ = lean_box(0);
                        v_isShared_5528_ = v_isSharedCheck_5533_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5524_);
                    v___x_5534_ = (lean_unbox(v_a_5505_) as u8);
                    lean_dec(v_a_5505_);
                    if v___x_5534_ == 0 {
                        v_funDeclsPure_5535_ = lean_ctor_get(v_lctx_5521_, 4);
                        lean_inc_ref(v_funDeclsPure_5535_);
                        lean_dec_ref(v_lctx_5521_);
                        v___y_5510_ = v_funDeclsPure_5535_;
                        state = 2;
                        continue;
                    } else {
                        v_funDeclsImpure_5536_ = lean_ctor_get(v_lctx_5521_, 5);
                        lean_inc_ref(v_funDeclsImpure_5536_);
                        lean_dec_ref(v_lctx_5521_);
                        v___y_5510_ = v_funDeclsImpure_5536_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_binderName_5529_ = lean_ctor_get(v_val_5525_, 1);
                lean_inc(v_binderName_5529_);
                lean_dec(v_val_5525_);
                if v_isShared_5528_ == 0 {
                    lean_ctor_set_tag(v___x_5527_, 0);
                    lean_ctor_set(v___x_5527_, 0, v_binderName_5529_);
                    v___x_5531_ = v___x_5527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_binderName_5529_);
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
                lean_dec_ref(v___y_5538_);
                if lean_obj_tag(v___x_5539_) == 1 {
                    lean_dec_ref(v_lctx_5521_);
                    lean_del_object(v___x_5507_);
                    lean_dec(v_a_5505_);
                    lean_dec(v_fvarId_5497_);
                    v_val_5540_ = lean_ctor_get(v___x_5539_, 0);
                    v_isSharedCheck_5548_ = (!lean_is_exclusive(v___x_5539_)) as u8;
                    if v_isSharedCheck_5548_ == 0 {
                        v___x_5542_ = v___x_5539_;
                        v_isShared_5543_ = v_isSharedCheck_5548_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_5540_);
                        lean_dec(v___x_5539_);
                        v___x_5542_ = lean_box(0);
                        v_isShared_5543_ = v_isSharedCheck_5548_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5539_);
                    v___x_5549_ = (lean_unbox(v_a_5505_) as u8);
                    if v___x_5549_ == 0 {
                        v_paramsPure_5550_ = lean_ctor_get(v_lctx_5521_, 0);
                        lean_inc_ref(v_paramsPure_5550_);
                        v___y_5523_ = v_paramsPure_5550_;
                        state = 4;
                        continue;
                    } else {
                        v_paramsImpure_5551_ = lean_ctor_get(v_lctx_5521_, 1);
                        lean_inc_ref(v_paramsImpure_5551_);
                        v___y_5523_ = v_paramsImpure_5551_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v_binderName_5544_ = lean_ctor_get(v_val_5540_, 1);
                lean_inc(v_binderName_5544_);
                lean_dec(v_val_5540_);
                if v_isShared_5543_ == 0 {
                    lean_ctor_set_tag(v___x_5542_, 0);
                    lean_ctor_set(v___x_5542_, 0, v_binderName_5544_);
                    v___x_5546_ = v___x_5542_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_binderName_5544_);
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
                    v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
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
    mut v_fvarId_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
    mut v_a_5568_: *mut LeanObject,
    mut v_a_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5570_: *mut LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Lean_Compiler_LCNF_getBinderName(
        v_fvarId_5564_,
        v_a_5565_,
        v_a_5566_,
        v_a_5567_,
        v_a_5568_,
    );
    lean_dec(v_a_5568_);
    lean_dec_ref(v_a_5567_);
    lean_dec(v_a_5566_);
    lean_dec_ref(v_a_5565_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___redArg(
    mut v_pu_5571_: u8,
    mut v_fvarId_5572_: *mut LeanObject,
    mut v_a_5573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramsPure_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramsImpure_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5575_ = lean_st_ref_get(v_a_5573_);
                if v_pu_5571_ == 0 {
                    v_lctx_5580_ = lean_ctor_get(v___x_5575_, 0);
                    lean_inc_ref(v_lctx_5580_);
                    lean_dec(v___x_5575_);
                    v_paramsPure_5581_ = lean_ctor_get(v_lctx_5580_, 0);
                    lean_inc_ref(v_paramsPure_5581_);
                    lean_dec_ref(v_lctx_5580_);
                    v___y_5577_ = v_paramsPure_5581_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5582_ = lean_ctor_get(v___x_5575_, 0);
                    lean_inc_ref(v_lctx_5582_);
                    lean_dec(v___x_5575_);
                    v_paramsImpure_5583_ = lean_ctor_get(v_lctx_5582_, 1);
                    lean_inc_ref(v_paramsImpure_5583_);
                    lean_dec_ref(v_lctx_5582_);
                    v___y_5577_ = v_paramsImpure_5583_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5577_, v_fvarId_5572_);
                lean_dec_ref(v___y_5577_);
                v___x_5579_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5579_, 0, v___x_5578_);
                return v___x_5579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___redArg___boxed(
    mut v_pu_5584_: *mut LeanObject,
    mut v_fvarId_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5588_: u8 = 0;
    let mut v_res_5589_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5588_ = (lean_unbox(v_pu_5584_) as u8);
    v_res_5589_ =
        l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_boxed_5588_, v_fvarId_5585_, v_a_5586_);
    lean_dec(v_a_5586_);
    lean_dec(v_fvarId_5585_);
    return v_res_5589_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f(
    mut v_pu_5590_: u8,
    mut v_fvarId_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
    mut v_a_5594_: *mut LeanObject,
    mut v_a_5595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    v___x_5597_ =
        l_Lean_Compiler_LCNF_findParam_x3f___redArg(v_pu_5590_, v_fvarId_5591_, v_a_5593_);
    return v___x_5597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findParam_x3f___boxed(
    mut v_pu_5598_: *mut LeanObject,
    mut v_fvarId_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
    mut v_a_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
    mut v_a_5603_: *mut LeanObject,
    mut v_a_5604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5605_: u8 = 0;
    let mut v_res_5606_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5605_ = (lean_unbox(v_pu_5598_) as u8);
    v_res_5606_ = l_Lean_Compiler_LCNF_findParam_x3f(
        v_pu_boxed_5605_,
        v_fvarId_5599_,
        v_a_5600_,
        v_a_5601_,
        v_a_5602_,
        v_a_5603_,
    );
    lean_dec(v_a_5603_);
    lean_dec_ref(v_a_5602_);
    lean_dec(v_a_5601_);
    lean_dec_ref(v_a_5600_);
    lean_dec(v_fvarId_5599_);
    return v_res_5606_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
    mut v_pu_5607_: u8,
    mut v_fvarId_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_letDeclsPure_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_letDeclsImpure_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5611_ = lean_st_ref_get(v_a_5609_);
                if v_pu_5607_ == 0 {
                    v_lctx_5616_ = lean_ctor_get(v___x_5611_, 0);
                    lean_inc_ref(v_lctx_5616_);
                    lean_dec(v___x_5611_);
                    v_letDeclsPure_5617_ = lean_ctor_get(v_lctx_5616_, 2);
                    lean_inc_ref(v_letDeclsPure_5617_);
                    lean_dec_ref(v_lctx_5616_);
                    v___y_5613_ = v_letDeclsPure_5617_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5618_ = lean_ctor_get(v___x_5611_, 0);
                    lean_inc_ref(v_lctx_5618_);
                    lean_dec(v___x_5611_);
                    v_letDeclsImpure_5619_ = lean_ctor_get(v_lctx_5618_, 3);
                    lean_inc_ref(v_letDeclsImpure_5619_);
                    lean_dec_ref(v_lctx_5618_);
                    v___y_5613_ = v_letDeclsImpure_5619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5613_, v_fvarId_5608_);
                lean_dec_ref(v___y_5613_);
                v___x_5615_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5615_, 0, v___x_5614_);
                return v___x_5615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg___boxed(
    mut v_pu_5620_: *mut LeanObject,
    mut v_fvarId_5621_: *mut LeanObject,
    mut v_a_5622_: *mut LeanObject,
    mut v_a_5623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5624_: u8 = 0;
    let mut v_res_5625_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5624_ = (lean_unbox(v_pu_5620_) as u8);
    v_res_5625_ =
        l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_boxed_5624_, v_fvarId_5621_, v_a_5622_);
    lean_dec(v_a_5622_);
    lean_dec(v_fvarId_5621_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f(
    mut v_pu_5626_: u8,
    mut v_fvarId_5627_: *mut LeanObject,
    mut v_a_5628_: *mut LeanObject,
    mut v_a_5629_: *mut LeanObject,
    mut v_a_5630_: *mut LeanObject,
    mut v_a_5631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    v___x_5633_ =
        l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v_pu_5626_, v_fvarId_5627_, v_a_5629_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetDecl_x3f___boxed(
    mut v_pu_5634_: *mut LeanObject,
    mut v_fvarId_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
    mut v_a_5637_: *mut LeanObject,
    mut v_a_5638_: *mut LeanObject,
    mut v_a_5639_: *mut LeanObject,
    mut v_a_5640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5641_: u8 = 0;
    let mut v_res_5642_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5641_ = (lean_unbox(v_pu_5634_) as u8);
    v_res_5642_ = l_Lean_Compiler_LCNF_findLetDecl_x3f(
        v_pu_boxed_5641_,
        v_fvarId_5635_,
        v_a_5636_,
        v_a_5637_,
        v_a_5638_,
        v_a_5639_,
    );
    lean_dec(v_a_5639_);
    lean_dec_ref(v_a_5638_);
    lean_dec(v_a_5637_);
    lean_dec_ref(v_a_5636_);
    lean_dec(v_fvarId_5635_);
    return v_res_5642_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
    mut v_pu_5643_: u8,
    mut v_fvarId_5644_: *mut LeanObject,
    mut v_a_5645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclsPure_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclsImpure_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5647_ = lean_st_ref_get(v_a_5645_);
                if v_pu_5643_ == 0 {
                    v_lctx_5652_ = lean_ctor_get(v___x_5647_, 0);
                    lean_inc_ref(v_lctx_5652_);
                    lean_dec(v___x_5647_);
                    v_funDeclsPure_5653_ = lean_ctor_get(v_lctx_5652_, 4);
                    lean_inc_ref(v_funDeclsPure_5653_);
                    lean_dec_ref(v_lctx_5652_);
                    v___y_5649_ = v_funDeclsPure_5653_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_5654_ = lean_ctor_get(v___x_5647_, 0);
                    lean_inc_ref(v_lctx_5654_);
                    lean_dec(v___x_5647_);
                    v_funDeclsImpure_5655_ = lean_ctor_get(v_lctx_5654_, 5);
                    lean_inc_ref(v_funDeclsImpure_5655_);
                    lean_dec_ref(v_lctx_5654_);
                    v___y_5649_ = v_funDeclsImpure_5655_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v___y_5649_, v_fvarId_5644_);
                lean_dec_ref(v___y_5649_);
                v___x_5651_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5651_, 0, v___x_5650_);
                return v___x_5651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg___boxed(
    mut v_pu_5656_: *mut LeanObject,
    mut v_fvarId_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
    mut v_a_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5660_: u8 = 0;
    let mut v_res_5661_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5660_ = (lean_unbox(v_pu_5656_) as u8);
    v_res_5661_ =
        l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_boxed_5660_, v_fvarId_5657_, v_a_5658_);
    lean_dec(v_a_5658_);
    lean_dec(v_fvarId_5657_);
    return v_res_5661_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f(
    mut v_pu_5662_: u8,
    mut v_fvarId_5663_: *mut LeanObject,
    mut v_a_5664_: *mut LeanObject,
    mut v_a_5665_: *mut LeanObject,
    mut v_a_5666_: *mut LeanObject,
    mut v_a_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    v___x_5669_ =
        l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v_pu_5662_, v_fvarId_5663_, v_a_5665_);
    return v___x_5669_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findFunDecl_x3f___boxed(
    mut v_pu_5670_: *mut LeanObject,
    mut v_fvarId_5671_: *mut LeanObject,
    mut v_a_5672_: *mut LeanObject,
    mut v_a_5673_: *mut LeanObject,
    mut v_a_5674_: *mut LeanObject,
    mut v_a_5675_: *mut LeanObject,
    mut v_a_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5677_: u8 = 0;
    let mut v_res_5678_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5677_ = (lean_unbox(v_pu_5670_) as u8);
    v_res_5678_ = l_Lean_Compiler_LCNF_findFunDecl_x3f(
        v_pu_boxed_5677_,
        v_fvarId_5671_,
        v_a_5672_,
        v_a_5673_,
        v_a_5674_,
        v_a_5675_,
    );
    lean_dec(v_a_5675_);
    lean_dec_ref(v_a_5674_);
    lean_dec(v_a_5673_);
    lean_dec_ref(v_a_5672_);
    lean_dec(v_fvarId_5671_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
    mut v_pu_5679_: u8,
    mut v_fvarId_5680_: *mut LeanObject,
    mut v_a_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v_val_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5691_: u8 = 0;
    let mut v_value_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5699_: u8 = 0;
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5703_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_5684_ = lean_ctor_get(v___x_5683_, 0);
                v_isSharedCheck_5704_ = (!lean_is_exclusive(v___x_5683_)) as u8;
                if v_isSharedCheck_5704_ == 0 {
                    v___x_5686_ = v___x_5683_;
                    v_isShared_5687_ = v_isSharedCheck_5704_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5684_);
                    lean_dec(v___x_5683_);
                    v___x_5686_ = lean_box(0);
                    v_isShared_5687_ = v_isSharedCheck_5704_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5684_) == 1 {
                    v_val_5688_ = lean_ctor_get(v_a_5684_, 0);
                    v_isSharedCheck_5699_ = (!lean_is_exclusive(v_a_5684_)) as u8;
                    if v_isSharedCheck_5699_ == 0 {
                        v___x_5690_ = v_a_5684_;
                        v_isShared_5691_ = v_isSharedCheck_5699_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_5688_);
                        lean_dec(v_a_5684_);
                        v___x_5690_ = lean_box(0);
                        v_isShared_5691_ = v_isSharedCheck_5699_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5684_);
                    v___x_5700_ = lean_box(0);
                    if v_isShared_5687_ == 0 {
                        lean_ctor_set(v___x_5686_, 0, v___x_5700_);
                        v___x_5702_ = v___x_5686_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5700_);
                        v___x_5702_ = v_reuseFailAlloc_5703_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_value_5692_ = lean_ctor_get(v_val_5688_, 3);
                lean_inc(v_value_5692_);
                lean_dec(v_val_5688_);
                if v_isShared_5691_ == 0 {
                    lean_ctor_set(v___x_5690_, 0, v_value_5692_);
                    v___x_5694_ = v___x_5690_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_value_5692_);
                    v___x_5694_ = v_reuseFailAlloc_5698_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5687_ == 0 {
                    lean_ctor_set(v___x_5686_, 0, v___x_5694_);
                    v___x_5696_ = v___x_5686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5694_);
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
    mut v_pu_5705_: *mut LeanObject,
    mut v_fvarId_5706_: *mut LeanObject,
    mut v_a_5707_: *mut LeanObject,
    mut v_a_5708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5709_: u8 = 0;
    let mut v_res_5710_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5709_ = (lean_unbox(v_pu_5705_) as u8);
    v_res_5710_ =
        l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_boxed_5709_, v_fvarId_5706_, v_a_5707_);
    lean_dec(v_a_5707_);
    lean_dec(v_fvarId_5706_);
    return v_res_5710_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f(
    mut v_pu_5711_: u8,
    mut v_fvarId_5712_: *mut LeanObject,
    mut v_a_5713_: *mut LeanObject,
    mut v_a_5714_: *mut LeanObject,
    mut v_a_5715_: *mut LeanObject,
    mut v_a_5716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ =
        l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v_pu_5711_, v_fvarId_5712_, v_a_5714_);
    return v___x_5718_;
}
pub unsafe fn l_Lean_Compiler_LCNF_findLetValue_x3f___boxed(
    mut v_pu_5719_: *mut LeanObject,
    mut v_fvarId_5720_: *mut LeanObject,
    mut v_a_5721_: *mut LeanObject,
    mut v_a_5722_: *mut LeanObject,
    mut v_a_5723_: *mut LeanObject,
    mut v_a_5724_: *mut LeanObject,
    mut v_a_5725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5726_: u8 = 0;
    let mut v_res_5727_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5726_ = (lean_unbox(v_pu_5719_) as u8);
    v_res_5727_ = l_Lean_Compiler_LCNF_findLetValue_x3f(
        v_pu_boxed_5726_,
        v_fvarId_5720_,
        v_a_5721_,
        v_a_5722_,
        v_a_5723_,
        v_a_5724_,
    );
    lean_dec(v_a_5724_);
    lean_dec_ref(v_a_5723_);
    lean_dec(v_a_5722_);
    lean_dec_ref(v_a_5721_);
    lean_dec(v_fvarId_5720_);
    return v_res_5727_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp___redArg(
    mut v_fvarId_5728_: *mut LeanObject,
    mut v_a_5729_: *mut LeanObject,
    mut v_a_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5732_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5737_: u8 = 0;
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5747_: u8 = 0;
    let mut v_declName_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: u8 = 0;
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5765_: u8 = 0;
    let mut v_unused_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5771_: u8 = 0;
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5776_: u8 = 0;
    let mut v_isSharedCheck_5777_: u8 = 0;
    let mut v_a_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5784_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5733_) == 0 {
                    v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5777_ = (!lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5777_ == 0 {
                        v___x_5736_ = v___x_5733_;
                        v_isShared_5737_ = v_isSharedCheck_5777_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5734_);
                        lean_dec(v___x_5733_);
                        v___x_5736_ = lean_box(0);
                        v_isShared_5737_ = v_isSharedCheck_5777_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5778_ = lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5785_ = (!lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5785_ == 0 {
                        v___x_5780_ = v___x_5733_;
                        v_isShared_5781_ = v_isSharedCheck_5785_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5778_);
                        lean_dec(v___x_5733_);
                        v___x_5780_ = lean_box(0);
                        v_isShared_5781_ = v_isSharedCheck_5785_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5734_) == 1 {
                    v_val_5744_ = lean_ctor_get(v_a_5734_, 0);
                    v_isSharedCheck_5776_ = (!lean_is_exclusive(v_a_5734_)) as u8;
                    if v_isSharedCheck_5776_ == 0 {
                        v___x_5746_ = v_a_5734_;
                        v_isShared_5747_ = v_isSharedCheck_5776_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_5744_);
                        lean_dec(v_a_5734_);
                        v___x_5746_ = lean_box(0);
                        v_isShared_5747_ = v_isSharedCheck_5776_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5734_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5739_ = 0;
                v___x_5740_ = lean_box((v___x_5739_) as usize);
                if v_isShared_5737_ == 0 {
                    lean_ctor_set(v___x_5736_, 0, v___x_5740_);
                    v___x_5742_ = v___x_5736_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5740_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5742_;
            }
            4 => {
                if lean_obj_tag(v_val_5744_) == 3 {
                    lean_del_object(v___x_5736_);
                    v_declName_5748_ = lean_ctor_get(v_val_5744_, 0);
                    lean_inc(v_declName_5748_);
                    lean_dec_ref_known(v_val_5744_, 3);
                    v___x_5749_ = lean_st_ref_get(v_a_5730_);
                    v_env_5750_ = lean_ctor_get(v___x_5749_, 0);
                    lean_inc_ref(v_env_5750_);
                    lean_dec(v___x_5749_);
                    v___x_5751_ = 0;
                    v___x_5752_ =
                        l_Lean_Environment_find_x3f(v_env_5750_, v_declName_5748_, v___x_5751_);
                    if lean_obj_tag(v___x_5752_) == 1 {
                        lean_del_object(v___x_5746_);
                        v_val_5753_ = lean_ctor_get(v___x_5752_, 0);
                        v_isSharedCheck_5771_ = (!lean_is_exclusive(v___x_5752_)) as u8;
                        if v_isSharedCheck_5771_ == 0 {
                            v___x_5755_ = v___x_5752_;
                            v_isShared_5756_ = v_isSharedCheck_5771_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_5753_);
                            lean_dec(v___x_5752_);
                            v___x_5755_ = lean_box(0);
                            v_isShared_5756_ = v_isSharedCheck_5771_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5752_);
                        v___x_5772_ = lean_box((v___x_5751_) as usize);
                        if v_isShared_5747_ == 0 {
                            lean_ctor_set_tag(v___x_5746_, 0);
                            lean_ctor_set(v___x_5746_, 0, v___x_5772_);
                            v___x_5774_ = v___x_5746_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
                            v___x_5774_ = v_reuseFailAlloc_5775_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5746_);
                    lean_dec(v_val_5744_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v_val_5753_) == 6 {
                    lean_del_object(v___x_5755_);
                    v_isSharedCheck_5765_ = (!lean_is_exclusive(v_val_5753_)) as u8;
                    if v_isSharedCheck_5765_ == 0 {
                        v_unused_5766_ = lean_ctor_get(v_val_5753_, 0);
                        lean_dec(v_unused_5766_);
                        v___x_5758_ = v_val_5753_;
                        v_isShared_5759_ = v_isSharedCheck_5765_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_val_5753_);
                        v___x_5758_ = lean_box(0);
                        v_isShared_5759_ = v_isSharedCheck_5765_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_val_5753_);
                    v___x_5767_ = lean_box((v___x_5751_) as usize);
                    if v_isShared_5756_ == 0 {
                        lean_ctor_set_tag(v___x_5755_, 0);
                        lean_ctor_set(v___x_5755_, 0, v___x_5767_);
                        v___x_5769_ = v___x_5755_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
                        v___x_5769_ = v_reuseFailAlloc_5770_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5760_ = 1;
                v___x_5761_ = lean_box((v___x_5760_) as usize);
                if v_isShared_5759_ == 0 {
                    lean_ctor_set_tag(v___x_5758_, 0);
                    lean_ctor_set(v___x_5758_, 0, v___x_5761_);
                    v___x_5763_ = v___x_5758_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
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
                    v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
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
    mut v_fvarId_5786_: *mut LeanObject,
    mut v_a_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
    mut v_a_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5790_: *mut LeanObject = core::ptr::null_mut();
    v_res_5790_ =
        l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5786_, v_a_5787_, v_a_5788_);
    lean_dec(v_a_5788_);
    lean_dec(v_a_5787_);
    lean_dec(v_fvarId_5786_);
    return v_res_5790_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp(
    mut v_fvarId_5791_: *mut LeanObject,
    mut v_a_5792_: *mut LeanObject,
    mut v_a_5793_: *mut LeanObject,
    mut v_a_5794_: *mut LeanObject,
    mut v_a_5795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    v___x_5797_ =
        l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5791_, v_a_5793_, v_a_5795_);
    return v___x_5797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isConstructorApp___boxed(
    mut v_fvarId_5798_: *mut LeanObject,
    mut v_a_5799_: *mut LeanObject,
    mut v_a_5800_: *mut LeanObject,
    mut v_a_5801_: *mut LeanObject,
    mut v_a_5802_: *mut LeanObject,
    mut v_a_5803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5804_: *mut LeanObject = core::ptr::null_mut();
    v_res_5804_ = l_Lean_Compiler_LCNF_isConstructorApp(
        v_fvarId_5798_,
        v_a_5799_,
        v_a_5800_,
        v_a_5801_,
        v_a_5802_,
    );
    lean_dec(v_a_5802_);
    lean_dec_ref(v_a_5801_);
    lean_dec(v_a_5800_);
    lean_dec_ref(v_a_5799_);
    lean_dec(v_fvarId_5798_);
    return v_res_5804_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(
    mut v_arg_5805_: *mut LeanObject,
    mut v_a_5806_: *mut LeanObject,
    mut v_a_5807_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_5805_) == 1 {
        let mut v_fvarId_5809_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_5809_ = lean_ctor_get(v_arg_5805_, 0);
        v___x_5810_ =
            l_Lean_Compiler_LCNF_isConstructorApp___redArg(v_fvarId_5809_, v_a_5806_, v_a_5807_);
        return v___x_5810_;
    } else {
        let mut v___x_5811_: u8 = 0;
        let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
        v___x_5811_ = 0;
        v___x_5812_ = lean_box((v___x_5811_) as usize);
        v___x_5813_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5813_, 0, v___x_5812_);
        return v___x_5813_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg___boxed(
    mut v_arg_5814_: *mut LeanObject,
    mut v_a_5815_: *mut LeanObject,
    mut v_a_5816_: *mut LeanObject,
    mut v_a_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5818_: *mut LeanObject = core::ptr::null_mut();
    v_res_5818_ =
        l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_5814_, v_a_5815_, v_a_5816_);
    lean_dec(v_a_5816_);
    lean_dec(v_a_5815_);
    lean_dec(v_arg_5814_);
    return v_res_5818_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp(
    mut v_pu_5819_: u8,
    mut v_arg_5820_: *mut LeanObject,
    mut v_a_5821_: *mut LeanObject,
    mut v_a_5822_: *mut LeanObject,
    mut v_a_5823_: *mut LeanObject,
    mut v_a_5824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v___x_5826_ =
        l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(v_arg_5820_, v_a_5822_, v_a_5824_);
    return v___x_5826_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_isConstructorApp___boxed(
    mut v_pu_5827_: *mut LeanObject,
    mut v_arg_5828_: *mut LeanObject,
    mut v_a_5829_: *mut LeanObject,
    mut v_a_5830_: *mut LeanObject,
    mut v_a_5831_: *mut LeanObject,
    mut v_a_5832_: *mut LeanObject,
    mut v_a_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5834_ = (lean_unbox(v_pu_5827_) as u8);
    v_res_5835_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp(
        v_pu_boxed_5834_,
        v_arg_5828_,
        v_a_5829_,
        v_a_5830_,
        v_a_5831_,
        v_a_5832_,
    );
    lean_dec(v_a_5832_);
    lean_dec_ref(v_a_5831_);
    lean_dec(v_a_5830_);
    lean_dec_ref(v_a_5829_);
    lean_dec(v_arg_5828_);
    return v_res_5835_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getParam___closed__1() -> *mut LeanObject {
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_Compiler_LCNF_getParam___closed__0;
    v___x_5838_ = l_Lean_stringToMessageData(v___x_5837_);
    return v___x_5838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getParam(
    mut v_pu_5839_: u8,
    mut v_fvarId_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
    mut v_a_5842_: *mut LeanObject,
    mut v_a_5843_: *mut LeanObject,
    mut v_a_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5850_: u8 = 0;
    let mut v_val_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
                v_isSharedCheck_5859_ = (!lean_is_exclusive(v___x_5846_)) as u8;
                if v_isSharedCheck_5859_ == 0 {
                    v___x_5849_ = v___x_5846_;
                    v_isShared_5850_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5847_);
                    lean_dec(v___x_5846_);
                    v___x_5849_ = lean_box(0);
                    v_isShared_5850_ = v_isSharedCheck_5859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5847_) == 1 {
                    lean_dec(v_fvarId_5840_);
                    v_val_5851_ = lean_ctor_get(v_a_5847_, 0);
                    lean_inc(v_val_5851_);
                    lean_dec_ref_known(v_a_5847_, 1);
                    if v_isShared_5850_ == 0 {
                        lean_ctor_set(v___x_5849_, 0, v_val_5851_);
                        v___x_5853_ = v___x_5849_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_val_5851_);
                        v___x_5853_ = v_reuseFailAlloc_5854_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5849_);
                    lean_dec(v_a_5847_);
                    v___x_5855_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getParam___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getParam___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getParam___closed__1,
                    );
                    v___x_5856_ = l_Lean_MessageData_ofName(v_fvarId_5840_);
                    v___x_5857_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5857_, 0, v___x_5855_);
                    lean_ctor_set(v___x_5857_, 1, v___x_5856_);
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
    mut v_pu_5860_: *mut LeanObject,
    mut v_fvarId_5861_: *mut LeanObject,
    mut v_a_5862_: *mut LeanObject,
    mut v_a_5863_: *mut LeanObject,
    mut v_a_5864_: *mut LeanObject,
    mut v_a_5865_: *mut LeanObject,
    mut v_a_5866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5867_: u8 = 0;
    let mut v_res_5868_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5867_ = (lean_unbox(v_pu_5860_) as u8);
    v_res_5868_ = l_Lean_Compiler_LCNF_getParam(
        v_pu_boxed_5867_,
        v_fvarId_5861_,
        v_a_5862_,
        v_a_5863_,
        v_a_5864_,
        v_a_5865_,
    );
    lean_dec(v_a_5865_);
    lean_dec_ref(v_a_5864_);
    lean_dec(v_a_5863_);
    lean_dec_ref(v_a_5862_);
    return v_res_5868_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1() -> *mut LeanObject {
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    v___x_5870_ = l_Lean_Compiler_LCNF_getLetDecl___closed__0;
    v___x_5871_ = l_Lean_stringToMessageData(v___x_5870_);
    return v___x_5871_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getLetDecl(
    mut v_pu_5872_: u8,
    mut v_fvarId_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
    mut v_a_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v_val_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_5880_ = lean_ctor_get(v___x_5879_, 0);
                v_isSharedCheck_5892_ = (!lean_is_exclusive(v___x_5879_)) as u8;
                if v_isSharedCheck_5892_ == 0 {
                    v___x_5882_ = v___x_5879_;
                    v_isShared_5883_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5880_);
                    lean_dec(v___x_5879_);
                    v___x_5882_ = lean_box(0);
                    v_isShared_5883_ = v_isSharedCheck_5892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5880_) == 1 {
                    lean_dec(v_fvarId_5873_);
                    v_val_5884_ = lean_ctor_get(v_a_5880_, 0);
                    lean_inc(v_val_5884_);
                    lean_dec_ref_known(v_a_5880_, 1);
                    if v_isShared_5883_ == 0 {
                        lean_ctor_set(v___x_5882_, 0, v_val_5884_);
                        v___x_5886_ = v___x_5882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5887_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_val_5884_);
                        v___x_5886_ = v_reuseFailAlloc_5887_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5882_);
                    lean_dec(v_a_5880_);
                    v___x_5888_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getLetDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getLetDecl___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getLetDecl___closed__1,
                    );
                    v___x_5889_ = l_Lean_MessageData_ofName(v_fvarId_5873_);
                    v___x_5890_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5890_, 0, v___x_5888_);
                    lean_ctor_set(v___x_5890_, 1, v___x_5889_);
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
    mut v_pu_5893_: *mut LeanObject,
    mut v_fvarId_5894_: *mut LeanObject,
    mut v_a_5895_: *mut LeanObject,
    mut v_a_5896_: *mut LeanObject,
    mut v_a_5897_: *mut LeanObject,
    mut v_a_5898_: *mut LeanObject,
    mut v_a_5899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5900_: u8 = 0;
    let mut v_res_5901_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5900_ = (lean_unbox(v_pu_5893_) as u8);
    v_res_5901_ = l_Lean_Compiler_LCNF_getLetDecl(
        v_pu_boxed_5900_,
        v_fvarId_5894_,
        v_a_5895_,
        v_a_5896_,
        v_a_5897_,
        v_a_5898_,
    );
    lean_dec(v_a_5898_);
    lean_dec_ref(v_a_5897_);
    lean_dec(v_a_5896_);
    lean_dec_ref(v_a_5895_);
    return v_res_5901_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1() -> *mut LeanObject {
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    v___x_5903_ = l_Lean_Compiler_LCNF_getFunDecl___closed__0;
    v___x_5904_ = l_Lean_stringToMessageData(v___x_5903_);
    return v___x_5904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getFunDecl(
    mut v_pu_5905_: u8,
    mut v_fvarId_5906_: *mut LeanObject,
    mut v_a_5907_: *mut LeanObject,
    mut v_a_5908_: *mut LeanObject,
    mut v_a_5909_: *mut LeanObject,
    mut v_a_5910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_val_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
                v_isSharedCheck_5925_ = (!lean_is_exclusive(v___x_5912_)) as u8;
                if v_isSharedCheck_5925_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    v_isShared_5916_ = v_isSharedCheck_5925_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5913_);
                    lean_dec(v___x_5912_);
                    v___x_5915_ = lean_box(0);
                    v_isShared_5916_ = v_isSharedCheck_5925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_5913_) == 1 {
                    lean_dec(v_fvarId_5906_);
                    v_val_5917_ = lean_ctor_get(v_a_5913_, 0);
                    lean_inc(v_val_5917_);
                    lean_dec_ref_known(v_a_5913_, 1);
                    if v_isShared_5916_ == 0 {
                        lean_ctor_set(v___x_5915_, 0, v_val_5917_);
                        v___x_5919_ = v___x_5915_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_val_5917_);
                        v___x_5919_ = v_reuseFailAlloc_5920_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5915_);
                    lean_dec(v_a_5913_);
                    v___x_5921_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getFunDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getFunDecl___closed__1_once),
                        _init_l_Lean_Compiler_LCNF_getFunDecl___closed__1,
                    );
                    v___x_5922_ = l_Lean_MessageData_ofName(v_fvarId_5906_);
                    v___x_5923_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5923_, 0, v___x_5921_);
                    lean_ctor_set(v___x_5923_, 1, v___x_5922_);
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
    mut v_pu_5926_: *mut LeanObject,
    mut v_fvarId_5927_: *mut LeanObject,
    mut v_a_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
    mut v_a_5932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_5933_: u8 = 0;
    let mut v_res_5934_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_5933_ = (lean_unbox(v_pu_5926_) as u8);
    v_res_5934_ = l_Lean_Compiler_LCNF_getFunDecl(
        v_pu_boxed_5933_,
        v_fvarId_5927_,
        v_a_5928_,
        v_a_5929_,
        v_a_5930_,
        v_a_5931_,
    );
    lean_dec(v_a_5931_);
    lean_dec_ref(v_a_5930_);
    lean_dec(v_a_5929_);
    lean_dec_ref(v_a_5928_);
    return v_res_5934_;
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___redArg(
    mut v_f_5935_: *mut LeanObject,
    mut v_a_5936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5943_: u8 = 0;
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5938_ = lean_st_ref_take(v_a_5936_);
                v_lctx_5939_ = lean_ctor_get(v___x_5938_, 0);
                v_nextIdx_5940_ = lean_ctor_get(v___x_5938_, 1);
                v_isSharedCheck_5951_ = (!lean_is_exclusive(v___x_5938_)) as u8;
                if v_isSharedCheck_5951_ == 0 {
                    v___x_5942_ = v___x_5938_;
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_5940_);
                    lean_inc(v_lctx_5939_);
                    lean_dec(v___x_5938_);
                    v___x_5942_ = lean_box(0);
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5944_ = lean_apply_1(v_f_5935_, v_lctx_5939_);
                if v_isShared_5943_ == 0 {
                    lean_ctor_set(v___x_5942_, 0, v___x_5944_);
                    v___x_5946_ = v___x_5942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5944_);
                    lean_ctor_set(v_reuseFailAlloc_5950_, 1, v_nextIdx_5940_);
                    v___x_5946_ = v_reuseFailAlloc_5950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5947_ = lean_st_ref_set(v_a_5936_, v___x_5946_);
                v___x_5948_ = lean_box(0);
                v___x_5949_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5949_, 0, v___x_5948_);
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___redArg___boxed(
    mut v_f_5952_: *mut LeanObject,
    mut v_a_5953_: *mut LeanObject,
    mut v_a_5954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5955_: *mut LeanObject = core::ptr::null_mut();
    v_res_5955_ = l_Lean_Compiler_LCNF_modifyLCtx___redArg(v_f_5952_, v_a_5953_);
    lean_dec(v_a_5953_);
    return v_res_5955_;
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx(
    mut v_f_5956_: *mut LeanObject,
    mut v_a_5957_: *mut LeanObject,
    mut v_a_5958_: *mut LeanObject,
    mut v_a_5959_: *mut LeanObject,
    mut v_a_5960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5962_ = lean_st_ref_take(v_a_5958_);
                v_lctx_5963_ = lean_ctor_get(v___x_5962_, 0);
                v_nextIdx_5964_ = lean_ctor_get(v___x_5962_, 1);
                v_isSharedCheck_5975_ = (!lean_is_exclusive(v___x_5962_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v___x_5966_ = v___x_5962_;
                    v_isShared_5967_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_5964_);
                    lean_inc(v_lctx_5963_);
                    lean_dec(v___x_5962_);
                    v___x_5966_ = lean_box(0);
                    v_isShared_5967_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5968_ = lean_apply_1(v_f_5956_, v_lctx_5963_);
                if v_isShared_5967_ == 0 {
                    lean_ctor_set(v___x_5966_, 0, v___x_5968_);
                    v___x_5970_ = v___x_5966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5968_);
                    lean_ctor_set(v_reuseFailAlloc_5974_, 1, v_nextIdx_5964_);
                    v___x_5970_ = v_reuseFailAlloc_5974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5971_ = lean_st_ref_set(v_a_5958_, v___x_5970_);
                v___x_5972_ = lean_box(0);
                v___x_5973_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5973_, 0, v___x_5972_);
                return v___x_5973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_modifyLCtx___boxed(
    mut v_f_5976_: *mut LeanObject,
    mut v_a_5977_: *mut LeanObject,
    mut v_a_5978_: *mut LeanObject,
    mut v_a_5979_: *mut LeanObject,
    mut v_a_5980_: *mut LeanObject,
    mut v_a_5981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5982_: *mut LeanObject = core::ptr::null_mut();
    v_res_5982_ =
        l_Lean_Compiler_LCNF_modifyLCtx(v_f_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_);
    lean_dec(v_a_5980_);
    lean_dec_ref(v_a_5979_);
    lean_dec(v_a_5978_);
    lean_dec_ref(v_a_5977_);
    return v_res_5982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___redArg(
    mut v_pu_5983_: u8,
    mut v_decl_5984_: *mut LeanObject,
    mut v_a_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5992_: u8 = 0;
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5987_ = lean_st_ref_take(v_a_5985_);
                v_lctx_5988_ = lean_ctor_get(v___x_5987_, 0);
                v_nextIdx_5989_ = lean_ctor_get(v___x_5987_, 1);
                v_isSharedCheck_6000_ = (!lean_is_exclusive(v___x_5987_)) as u8;
                if v_isSharedCheck_6000_ == 0 {
                    v___x_5991_ = v___x_5987_;
                    v_isShared_5992_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_5989_);
                    lean_inc(v_lctx_5988_);
                    lean_dec(v___x_5987_);
                    v___x_5991_ = lean_box(0);
                    v_isShared_5992_ = v_isSharedCheck_6000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5993_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseLetDecl(v_pu_5983_, v_lctx_5988_, v_decl_5984_);
                if v_isShared_5992_ == 0 {
                    lean_ctor_set(v___x_5991_, 0, v___x_5993_);
                    v___x_5995_ = v___x_5991_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5993_);
                    lean_ctor_set(v_reuseFailAlloc_5999_, 1, v_nextIdx_5989_);
                    v___x_5995_ = v_reuseFailAlloc_5999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5996_ = lean_st_ref_set(v_a_5985_, v___x_5995_);
                v___x_5997_ = lean_box(0);
                v___x_5998_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5998_, 0, v___x_5997_);
                return v___x_5998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___redArg___boxed(
    mut v_pu_6001_: *mut LeanObject,
    mut v_decl_6002_: *mut LeanObject,
    mut v_a_6003_: *mut LeanObject,
    mut v_a_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6005_: u8 = 0;
    let mut v_res_6006_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6005_ = (lean_unbox(v_pu_6001_) as u8);
    v_res_6006_ =
        l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_boxed_6005_, v_decl_6002_, v_a_6003_);
    lean_dec(v_a_6003_);
    lean_dec_ref(v_decl_6002_);
    return v_res_6006_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl(
    mut v_pu_6007_: u8,
    mut v_decl_6008_: *mut LeanObject,
    mut v_a_6009_: *mut LeanObject,
    mut v_a_6010_: *mut LeanObject,
    mut v_a_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    v___x_6014_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_6007_, v_decl_6008_, v_a_6010_);
    return v___x_6014_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseLetDecl___boxed(
    mut v_pu_6015_: *mut LeanObject,
    mut v_decl_6016_: *mut LeanObject,
    mut v_a_6017_: *mut LeanObject,
    mut v_a_6018_: *mut LeanObject,
    mut v_a_6019_: *mut LeanObject,
    mut v_a_6020_: *mut LeanObject,
    mut v_a_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6022_: u8 = 0;
    let mut v_res_6023_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6022_ = (lean_unbox(v_pu_6015_) as u8);
    v_res_6023_ = l_Lean_Compiler_LCNF_eraseLetDecl(
        v_pu_boxed_6022_,
        v_decl_6016_,
        v_a_6017_,
        v_a_6018_,
        v_a_6019_,
        v_a_6020_,
    );
    lean_dec(v_a_6020_);
    lean_dec_ref(v_a_6019_);
    lean_dec(v_a_6018_);
    lean_dec_ref(v_a_6017_);
    lean_dec_ref(v_decl_6016_);
    return v_res_6023_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
    mut v_pu_6024_: u8,
    mut v_decl_6025_: *mut LeanObject,
    mut v_recursive_6026_: u8,
    mut v_a_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6029_ = lean_st_ref_take(v_a_6027_);
                v_lctx_6030_ = lean_ctor_get(v___x_6029_, 0);
                v_nextIdx_6031_ = lean_ctor_get(v___x_6029_, 1);
                v_isSharedCheck_6042_ = (!lean_is_exclusive(v___x_6029_)) as u8;
                if v_isSharedCheck_6042_ == 0 {
                    v___x_6033_ = v___x_6029_;
                    v_isShared_6034_ = v_isSharedCheck_6042_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_6031_);
                    lean_inc(v_lctx_6030_);
                    lean_dec(v___x_6029_);
                    v___x_6033_ = lean_box(0);
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
                    lean_ctor_set(v___x_6033_, 0, v___x_6035_);
                    v___x_6037_ = v___x_6033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6041_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6035_);
                    lean_ctor_set(v_reuseFailAlloc_6041_, 1, v_nextIdx_6031_);
                    v___x_6037_ = v_reuseFailAlloc_6041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6038_ = lean_st_ref_set(v_a_6027_, v___x_6037_);
                v___x_6039_ = lean_box(0);
                v___x_6040_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6040_, 0, v___x_6039_);
                return v___x_6040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___redArg___boxed(
    mut v_pu_6043_: *mut LeanObject,
    mut v_decl_6044_: *mut LeanObject,
    mut v_recursive_6045_: *mut LeanObject,
    mut v_a_6046_: *mut LeanObject,
    mut v_a_6047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6048_: u8 = 0;
    let mut v_recursive_boxed_6049_: u8 = 0;
    let mut v_res_6050_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6048_ = (lean_unbox(v_pu_6043_) as u8);
    v_recursive_boxed_6049_ = (lean_unbox(v_recursive_6045_) as u8);
    v_res_6050_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
        v_pu_boxed_6048_,
        v_decl_6044_,
        v_recursive_boxed_6049_,
        v_a_6046_,
    );
    lean_dec(v_a_6046_);
    lean_dec_ref(v_decl_6044_);
    return v_res_6050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl(
    mut v_pu_6051_: u8,
    mut v_decl_6052_: *mut LeanObject,
    mut v_recursive_6053_: u8,
    mut v_a_6054_: *mut LeanObject,
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
    mut v_a_6057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    v___x_6059_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
        v_pu_6051_,
        v_decl_6052_,
        v_recursive_6053_,
        v_a_6055_,
    );
    return v___x_6059_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseFunDecl___boxed(
    mut v_pu_6060_: *mut LeanObject,
    mut v_decl_6061_: *mut LeanObject,
    mut v_recursive_6062_: *mut LeanObject,
    mut v_a_6063_: *mut LeanObject,
    mut v_a_6064_: *mut LeanObject,
    mut v_a_6065_: *mut LeanObject,
    mut v_a_6066_: *mut LeanObject,
    mut v_a_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6068_: u8 = 0;
    let mut v_recursive_boxed_6069_: u8 = 0;
    let mut v_res_6070_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6068_ = (lean_unbox(v_pu_6060_) as u8);
    v_recursive_boxed_6069_ = (lean_unbox(v_recursive_6062_) as u8);
    v_res_6070_ = l_Lean_Compiler_LCNF_eraseFunDecl(
        v_pu_boxed_6068_,
        v_decl_6061_,
        v_recursive_boxed_6069_,
        v_a_6063_,
        v_a_6064_,
        v_a_6065_,
        v_a_6066_,
    );
    lean_dec(v_a_6066_);
    lean_dec_ref(v_a_6065_);
    lean_dec(v_a_6064_);
    lean_dec_ref(v_a_6063_);
    lean_dec_ref(v_decl_6061_);
    return v_res_6070_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___redArg(
    mut v_pu_6071_: u8,
    mut v_code_6072_: *mut LeanObject,
    mut v_a_6073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6080_: u8 = 0;
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6075_ = lean_st_ref_take(v_a_6073_);
                v_lctx_6076_ = lean_ctor_get(v___x_6075_, 0);
                v_nextIdx_6077_ = lean_ctor_get(v___x_6075_, 1);
                v_isSharedCheck_6088_ = (!lean_is_exclusive(v___x_6075_)) as u8;
                if v_isSharedCheck_6088_ == 0 {
                    v___x_6079_ = v___x_6075_;
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_6077_);
                    lean_inc(v_lctx_6076_);
                    lean_dec(v___x_6075_);
                    v___x_6079_ = lean_box(0);
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6081_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseCode(v_pu_6071_, v_code_6072_, v_lctx_6076_);
                if v_isShared_6080_ == 0 {
                    lean_ctor_set(v___x_6079_, 0, v___x_6081_);
                    v___x_6083_ = v___x_6079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6081_);
                    lean_ctor_set(v_reuseFailAlloc_6087_, 1, v_nextIdx_6077_);
                    v___x_6083_ = v_reuseFailAlloc_6087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6084_ = lean_st_ref_set(v_a_6073_, v___x_6083_);
                v___x_6085_ = lean_box(0);
                v___x_6086_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6086_, 0, v___x_6085_);
                return v___x_6086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___redArg___boxed(
    mut v_pu_6089_: *mut LeanObject,
    mut v_code_6090_: *mut LeanObject,
    mut v_a_6091_: *mut LeanObject,
    mut v_a_6092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6093_: u8 = 0;
    let mut v_res_6094_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6093_ = (lean_unbox(v_pu_6089_) as u8);
    v_res_6094_ =
        l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_boxed_6093_, v_code_6090_, v_a_6091_);
    lean_dec(v_a_6091_);
    lean_dec_ref(v_code_6090_);
    return v_res_6094_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode(
    mut v_pu_6095_: u8,
    mut v_code_6096_: *mut LeanObject,
    mut v_a_6097_: *mut LeanObject,
    mut v_a_6098_: *mut LeanObject,
    mut v_a_6099_: *mut LeanObject,
    mut v_a_6100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    v___x_6102_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_6095_, v_code_6096_, v_a_6098_);
    return v___x_6102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCode___boxed(
    mut v_pu_6103_: *mut LeanObject,
    mut v_code_6104_: *mut LeanObject,
    mut v_a_6105_: *mut LeanObject,
    mut v_a_6106_: *mut LeanObject,
    mut v_a_6107_: *mut LeanObject,
    mut v_a_6108_: *mut LeanObject,
    mut v_a_6109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6110_: u8 = 0;
    let mut v_res_6111_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6110_ = (lean_unbox(v_pu_6103_) as u8);
    v_res_6111_ = l_Lean_Compiler_LCNF_eraseCode(
        v_pu_boxed_6110_,
        v_code_6104_,
        v_a_6105_,
        v_a_6106_,
        v_a_6107_,
        v_a_6108_,
    );
    lean_dec(v_a_6108_);
    lean_dec_ref(v_a_6107_);
    lean_dec(v_a_6106_);
    lean_dec_ref(v_a_6105_);
    lean_dec_ref(v_code_6104_);
    return v_res_6111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___redArg(
    mut v_pu_6112_: u8,
    mut v_param_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6116_ = lean_st_ref_take(v_a_6114_);
                v_lctx_6117_ = lean_ctor_get(v___x_6116_, 0);
                v_nextIdx_6118_ = lean_ctor_get(v___x_6116_, 1);
                v_isSharedCheck_6129_ = (!lean_is_exclusive(v___x_6116_)) as u8;
                if v_isSharedCheck_6129_ == 0 {
                    v___x_6120_ = v___x_6116_;
                    v_isShared_6121_ = v_isSharedCheck_6129_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_6118_);
                    lean_inc(v_lctx_6117_);
                    lean_dec(v___x_6116_);
                    v___x_6120_ = lean_box(0);
                    v_isShared_6121_ = v_isSharedCheck_6129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6122_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseParam(v_pu_6112_, v_lctx_6117_, v_param_6113_);
                if v_isShared_6121_ == 0 {
                    lean_ctor_set(v___x_6120_, 0, v___x_6122_);
                    v___x_6124_ = v___x_6120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6122_);
                    lean_ctor_set(v_reuseFailAlloc_6128_, 1, v_nextIdx_6118_);
                    v___x_6124_ = v_reuseFailAlloc_6128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6125_ = lean_st_ref_set(v_a_6114_, v___x_6124_);
                v___x_6126_ = lean_box(0);
                v___x_6127_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6127_, 0, v___x_6126_);
                return v___x_6127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___redArg___boxed(
    mut v_pu_6130_: *mut LeanObject,
    mut v_param_6131_: *mut LeanObject,
    mut v_a_6132_: *mut LeanObject,
    mut v_a_6133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6134_: u8 = 0;
    let mut v_res_6135_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6134_ = (lean_unbox(v_pu_6130_) as u8);
    v_res_6135_ =
        l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_boxed_6134_, v_param_6131_, v_a_6132_);
    lean_dec(v_a_6132_);
    lean_dec_ref(v_param_6131_);
    return v_res_6135_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam(
    mut v_pu_6136_: u8,
    mut v_param_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
    mut v_a_6139_: *mut LeanObject,
    mut v_a_6140_: *mut LeanObject,
    mut v_a_6141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    v___x_6143_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_6136_, v_param_6137_, v_a_6139_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParam___boxed(
    mut v_pu_6144_: *mut LeanObject,
    mut v_param_6145_: *mut LeanObject,
    mut v_a_6146_: *mut LeanObject,
    mut v_a_6147_: *mut LeanObject,
    mut v_a_6148_: *mut LeanObject,
    mut v_a_6149_: *mut LeanObject,
    mut v_a_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6151_: u8 = 0;
    let mut v_res_6152_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6151_ = (lean_unbox(v_pu_6144_) as u8);
    v_res_6152_ = l_Lean_Compiler_LCNF_eraseParam(
        v_pu_boxed_6151_,
        v_param_6145_,
        v_a_6146_,
        v_a_6147_,
        v_a_6148_,
        v_a_6149_,
    );
    lean_dec(v_a_6149_);
    lean_dec_ref(v_a_6148_);
    lean_dec(v_a_6147_);
    lean_dec_ref(v_a_6146_);
    lean_dec_ref(v_param_6145_);
    return v_res_6152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___redArg(
    mut v_pu_6153_: u8,
    mut v_params_6154_: *mut LeanObject,
    mut v_a_6155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6157_ = lean_st_ref_take(v_a_6155_);
                v_lctx_6158_ = lean_ctor_get(v___x_6157_, 0);
                v_nextIdx_6159_ = lean_ctor_get(v___x_6157_, 1);
                v_isSharedCheck_6170_ = (!lean_is_exclusive(v___x_6157_)) as u8;
                if v_isSharedCheck_6170_ == 0 {
                    v___x_6161_ = v___x_6157_;
                    v_isShared_6162_ = v_isSharedCheck_6170_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_6159_);
                    lean_inc(v_lctx_6158_);
                    lean_dec(v___x_6157_);
                    v___x_6161_ = lean_box(0);
                    v_isShared_6162_ = v_isSharedCheck_6170_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6163_ =
                    l_Lean_Compiler_LCNF_LCtx_eraseParams(v_pu_6153_, v_lctx_6158_, v_params_6154_);
                if v_isShared_6162_ == 0 {
                    lean_ctor_set(v___x_6161_, 0, v___x_6163_);
                    v___x_6165_ = v___x_6161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6163_);
                    lean_ctor_set(v_reuseFailAlloc_6169_, 1, v_nextIdx_6159_);
                    v___x_6165_ = v_reuseFailAlloc_6169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6166_ = lean_st_ref_set(v_a_6155_, v___x_6165_);
                v___x_6167_ = lean_box(0);
                v___x_6168_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6168_, 0, v___x_6167_);
                return v___x_6168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___redArg___boxed(
    mut v_pu_6171_: *mut LeanObject,
    mut v_params_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v_a_6174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6175_: u8 = 0;
    let mut v_res_6176_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6175_ = (lean_unbox(v_pu_6171_) as u8);
    v_res_6176_ =
        l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_boxed_6175_, v_params_6172_, v_a_6173_);
    lean_dec(v_a_6173_);
    lean_dec_ref(v_params_6172_);
    return v_res_6176_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams(
    mut v_pu_6177_: u8,
    mut v_params_6178_: *mut LeanObject,
    mut v_a_6179_: *mut LeanObject,
    mut v_a_6180_: *mut LeanObject,
    mut v_a_6181_: *mut LeanObject,
    mut v_a_6182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    v___x_6184_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_6177_, v_params_6178_, v_a_6180_);
    return v___x_6184_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseParams___boxed(
    mut v_pu_6185_: *mut LeanObject,
    mut v_params_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
    mut v_a_6189_: *mut LeanObject,
    mut v_a_6190_: *mut LeanObject,
    mut v_a_6191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6192_: u8 = 0;
    let mut v_res_6193_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6192_ = (lean_unbox(v_pu_6185_) as u8);
    v_res_6193_ = l_Lean_Compiler_LCNF_eraseParams(
        v_pu_boxed_6192_,
        v_params_6186_,
        v_a_6187_,
        v_a_6188_,
        v_a_6189_,
        v_a_6190_,
    );
    lean_dec(v_a_6190_);
    lean_dec_ref(v_a_6189_);
    lean_dec(v_a_6188_);
    lean_dec_ref(v_a_6187_);
    lean_dec_ref(v_params_6186_);
    return v_res_6193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
    mut v_pu_6194_: u8,
    mut v_decl_6195_: *mut LeanObject,
    mut v_a_6196_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_6195_) {
        0 => {
            let mut v_decl_6198_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6198_ = lean_ctor_get(v_decl_6195_, 0);
            v___x_6199_ =
                l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_6194_, v_decl_6198_, v_a_6196_);
            return v___x_6199_;
        }
        1 => {
            let mut v_decl_6200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6201_: u8 = 0;
            let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6200_ = lean_ctor_get(v_decl_6195_, 0);
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
            let mut v_decl_6203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6204_: u8 = 0;
            let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
            v_decl_6203_ = lean_ctor_get(v_decl_6195_, 0);
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
            let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
            v___x_6206_ = lean_box(0);
            v___x_6207_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6207_, 0, v___x_6206_);
            return v___x_6207_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___redArg___boxed(
    mut v_pu_6208_: *mut LeanObject,
    mut v_decl_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
    mut v_a_6211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6212_: u8 = 0;
    let mut v_res_6213_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6212_ = (lean_unbox(v_pu_6208_) as u8);
    v_res_6213_ =
        l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_boxed_6212_, v_decl_6209_, v_a_6210_);
    lean_dec(v_a_6210_);
    lean_dec_ref(v_decl_6209_);
    return v_res_6213_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl(
    mut v_pu_6214_: u8,
    mut v_decl_6215_: *mut LeanObject,
    mut v_a_6216_: *mut LeanObject,
    mut v_a_6217_: *mut LeanObject,
    mut v_a_6218_: *mut LeanObject,
    mut v_a_6219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    v___x_6221_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(v_pu_6214_, v_decl_6215_, v_a_6217_);
    return v___x_6221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecl___boxed(
    mut v_pu_6222_: *mut LeanObject,
    mut v_decl_6223_: *mut LeanObject,
    mut v_a_6224_: *mut LeanObject,
    mut v_a_6225_: *mut LeanObject,
    mut v_a_6226_: *mut LeanObject,
    mut v_a_6227_: *mut LeanObject,
    mut v_a_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6229_: u8 = 0;
    let mut v_res_6230_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6229_ = (lean_unbox(v_pu_6222_) as u8);
    v_res_6230_ = l_Lean_Compiler_LCNF_eraseCodeDecl(
        v_pu_boxed_6229_,
        v_decl_6223_,
        v_a_6224_,
        v_a_6225_,
        v_a_6226_,
        v_a_6227_,
    );
    lean_dec(v_a_6227_);
    lean_dec_ref(v_a_6226_);
    lean_dec(v_a_6225_);
    lean_dec_ref(v_a_6224_);
    lean_dec_ref(v_decl_6223_);
    return v_res_6230_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(
    mut v_pu_6231_: u8,
    mut v_as_6232_: *mut LeanObject,
    mut v_i_6233_: usize,
    mut v_stop_6234_: usize,
    mut v_b_6235_: *mut LeanObject,
    mut v___y_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6238_: u8 = 0;
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: usize = 0;
    let mut v___x_6243_: usize = 0;
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_6240_) == 0 {
                        v_a_6241_ = lean_ctor_get(v___x_6240_, 0);
                        lean_inc(v_a_6241_);
                        lean_dec_ref_known(v___x_6240_, 1);
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
                    v___x_6245_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6245_, 0, v_b_6235_);
                    return v___x_6245_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg___boxed(
    mut v_pu_6246_: *mut LeanObject,
    mut v_as_6247_: *mut LeanObject,
    mut v_i_6248_: *mut LeanObject,
    mut v_stop_6249_: *mut LeanObject,
    mut v_b_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6253_: u8 = 0;
    let mut v_i_boxed_6254_: usize = 0;
    let mut v_stop_boxed_6255_: usize = 0;
    let mut v_res_6256_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6253_ = (lean_unbox(v_pu_6246_) as u8);
    v_i_boxed_6254_ = lean_unbox_usize(v_i_6248_);
    lean_dec(v_i_6248_);
    v_stop_boxed_6255_ = lean_unbox_usize(v_stop_6249_);
    lean_dec(v_stop_6249_);
    v_res_6256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_boxed_6253_, v_as_6247_, v_i_boxed_6254_, v_stop_boxed_6255_, v_b_6250_, v___y_6251_);
    lean_dec(v___y_6251_);
    lean_dec_ref(v_as_6247_);
    return v_res_6256_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecls(
    mut v_pu_6257_: u8,
    mut v_decls_6258_: *mut LeanObject,
    mut v_a_6259_: *mut LeanObject,
    mut v_a_6260_: *mut LeanObject,
    mut v_a_6261_: *mut LeanObject,
    mut v_a_6262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: u8 = 0;
    v___x_6264_ = lean_unsigned_to_nat(0);
    v___x_6265_ = lean_array_get_size(v_decls_6258_);
    v___x_6266_ = lean_box(0);
    v___x_6267_ = lean_nat_dec_lt(v___x_6264_, v___x_6265_);
    if v___x_6267_ == 0 {
        let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
        v___x_6268_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6268_, 0, v___x_6266_);
        return v___x_6268_;
    } else {
        let mut v___x_6269_: u8 = 0;
        v___x_6269_ = lean_nat_dec_le(v___x_6265_, v___x_6265_);
        if v___x_6269_ == 0 {
            if v___x_6267_ == 0 {
                let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
                v___x_6270_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6270_, 0, v___x_6266_);
                return v___x_6270_;
            } else {
                let mut v___x_6271_: usize = 0;
                let mut v___x_6272_: usize = 0;
                let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
                v___x_6271_ = 0usize;
                v___x_6272_ = lean_usize_of_nat(v___x_6265_);
                v___x_6273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6257_, v_decls_6258_, v___x_6271_, v___x_6272_, v___x_6266_, v_a_6260_);
                return v___x_6273_;
            }
        } else {
            let mut v___x_6274_: usize = 0;
            let mut v___x_6275_: usize = 0;
            let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
            v___x_6274_ = 0usize;
            v___x_6275_ = lean_usize_of_nat(v___x_6265_);
            v___x_6276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6257_, v_decls_6258_, v___x_6274_, v___x_6275_, v___x_6266_, v_a_6260_);
            return v___x_6276_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseCodeDecls___boxed(
    mut v_pu_6277_: *mut LeanObject,
    mut v_decls_6278_: *mut LeanObject,
    mut v_a_6279_: *mut LeanObject,
    mut v_a_6280_: *mut LeanObject,
    mut v_a_6281_: *mut LeanObject,
    mut v_a_6282_: *mut LeanObject,
    mut v_a_6283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6284_: u8 = 0;
    let mut v_res_6285_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6284_ = (lean_unbox(v_pu_6277_) as u8);
    v_res_6285_ = l_Lean_Compiler_LCNF_eraseCodeDecls(
        v_pu_boxed_6284_,
        v_decls_6278_,
        v_a_6279_,
        v_a_6280_,
        v_a_6281_,
        v_a_6282_,
    );
    lean_dec(v_a_6282_);
    lean_dec_ref(v_a_6281_);
    lean_dec(v_a_6280_);
    lean_dec_ref(v_a_6279_);
    lean_dec_ref(v_decls_6278_);
    return v_res_6285_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(
    mut v_pu_6286_: u8,
    mut v_as_6287_: *mut LeanObject,
    mut v_i_6288_: usize,
    mut v_stop_6289_: usize,
    mut v_b_6290_: *mut LeanObject,
    mut v___y_6291_: *mut LeanObject,
    mut v___y_6292_: *mut LeanObject,
    mut v___y_6293_: *mut LeanObject,
    mut v___y_6294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    v___x_6296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___redArg(v_pu_6286_, v_as_6287_, v_i_6288_, v_stop_6289_, v_b_6290_, v___y_6292_);
    return v___x_6296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0___boxed(
    mut v_pu_6297_: *mut LeanObject,
    mut v_as_6298_: *mut LeanObject,
    mut v_i_6299_: *mut LeanObject,
    mut v_stop_6300_: *mut LeanObject,
    mut v_b_6301_: *mut LeanObject,
    mut v___y_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6307_: u8 = 0;
    let mut v_i_boxed_6308_: usize = 0;
    let mut v_stop_boxed_6309_: usize = 0;
    let mut v_res_6310_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6307_ = (lean_unbox(v_pu_6297_) as u8);
    v_i_boxed_6308_ = lean_unbox_usize(v_i_6299_);
    lean_dec(v_i_6299_);
    v_stop_boxed_6309_ = lean_unbox_usize(v_stop_6300_);
    lean_dec(v_stop_6300_);
    v_res_6310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_eraseCodeDecls_spec__0(v_pu_boxed_6307_, v_as_6298_, v_i_boxed_6308_, v_stop_boxed_6309_, v_b_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
    lean_dec(v___y_6305_);
    lean_dec_ref(v___y_6304_);
    lean_dec(v___y_6303_);
    lean_dec_ref(v___y_6302_);
    lean_dec_ref(v_as_6298_);
    return v_res_6310_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(
    mut v_f_6311_: *mut LeanObject,
    mut v_v_6312_: *mut LeanObject,
    mut v___y_6313_: *mut LeanObject,
    mut v___y_6314_: *mut LeanObject,
    mut v___y_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6327_: u8 = 0;
    let mut v_unused_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_6312_) == 0 {
                    v_code_6318_ = lean_ctor_get(v_v_6312_, 0);
                    lean_inc_ref(v_code_6318_);
                    lean_dec_ref_known(v_v_6312_, 1);
                    lean_inc(v___y_6316_);
                    lean_inc_ref(v___y_6315_);
                    lean_inc(v___y_6314_);
                    lean_inc_ref(v___y_6313_);
                    v___x_6319_ = lean_apply_6(
                        v_f_6311_,
                        v_code_6318_,
                        v___y_6313_,
                        v___y_6314_,
                        v___y_6315_,
                        v___y_6316_,
                        lean_box(0),
                    );
                    return v___x_6319_;
                } else {
                    lean_dec_ref(v_f_6311_);
                    v_isSharedCheck_6327_ = (!lean_is_exclusive(v_v_6312_)) as u8;
                    if v_isSharedCheck_6327_ == 0 {
                        v_unused_6328_ = lean_ctor_get(v_v_6312_, 0);
                        lean_dec(v_unused_6328_);
                        v___x_6321_ = v_v_6312_;
                        v_isShared_6322_ = v_isSharedCheck_6327_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_6312_);
                        v___x_6321_ = lean_box(0);
                        v_isShared_6322_ = v_isSharedCheck_6327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6323_ = lean_box(0);
                if v_isShared_6322_ == 0 {
                    lean_ctor_set_tag(v___x_6321_, 0);
                    lean_ctor_set(v___x_6321_, 0, v___x_6323_);
                    v___x_6325_ = v___x_6321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6326_, 0, v___x_6323_);
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
    mut v_f_6329_: *mut LeanObject,
    mut v_v_6330_: *mut LeanObject,
    mut v___y_6331_: *mut LeanObject,
    mut v___y_6332_: *mut LeanObject,
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6336_: *mut LeanObject = core::ptr::null_mut();
    v_res_6336_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_6329_, v_v_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    lean_dec(v___y_6334_);
    lean_dec_ref(v___y_6333_);
    lean_dec(v___y_6332_);
    lean_dec_ref(v___y_6331_);
    return v_res_6336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0(
    mut v_pu_6337_: u8,
    mut v_f_6338_: *mut LeanObject,
    mut v_v_6339_: *mut LeanObject,
    mut v___y_6340_: *mut LeanObject,
    mut v___y_6341_: *mut LeanObject,
    mut v___y_6342_: *mut LeanObject,
    mut v___y_6343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    v___x_6345_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v_f_6338_, v_v_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
    return v___x_6345_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___boxed(
    mut v_pu_6346_: *mut LeanObject,
    mut v_f_6347_: *mut LeanObject,
    mut v_v_6348_: *mut LeanObject,
    mut v___y_6349_: *mut LeanObject,
    mut v___y_6350_: *mut LeanObject,
    mut v___y_6351_: *mut LeanObject,
    mut v___y_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6354_: u8 = 0;
    let mut v_res_6355_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6354_ = (lean_unbox(v_pu_6346_) as u8);
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
    lean_dec(v___y_6352_);
    lean_dec_ref(v___y_6351_);
    lean_dec(v___y_6350_);
    lean_dec_ref(v___y_6349_);
    return v_res_6355_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseDecl(
    mut v_pu_6356_: u8,
    mut v_decl_6357_: *mut LeanObject,
    mut v_a_6358_: *mut LeanObject,
    mut v_a_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
    mut v_a_6361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    v_toSignature_6363_ = lean_ctor_get(v_decl_6357_, 0);
    lean_inc_ref(v_toSignature_6363_);
    v_value_6364_ = lean_ctor_get(v_decl_6357_, 1);
    lean_inc_ref(v_value_6364_);
    lean_dec_ref(v_decl_6357_);
    v_params_6365_ = lean_ctor_get(v_toSignature_6363_, 3);
    lean_inc_ref(v_params_6365_);
    lean_dec_ref(v_toSignature_6363_);
    v___x_6366_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v_pu_6356_, v_params_6365_, v_a_6359_);
    lean_dec_ref(v_params_6365_);
    lean_dec_ref(v___x_6366_);
    v___x_6367_ = lean_box((v_pu_6356_) as usize);
    v___x_6368_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_eraseCode___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_6368_, 0, v___x_6367_);
    v___x_6369_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_eraseDecl_spec__0___redArg(v___x_6368_, v_value_6364_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eraseDecl___boxed(
    mut v_pu_6370_: *mut LeanObject,
    mut v_decl_6371_: *mut LeanObject,
    mut v_a_6372_: *mut LeanObject,
    mut v_a_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
    mut v_a_6376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6377_: u8 = 0;
    let mut v_res_6378_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6377_ = (lean_unbox(v_pu_6370_) as u8);
    v_res_6378_ = l_Lean_Compiler_LCNF_eraseDecl(
        v_pu_boxed_6377_,
        v_decl_6371_,
        v_a_6372_,
        v_a_6373_,
        v_a_6374_,
        v_a_6375_,
    );
    lean_dec(v_a_6375_);
    lean_dec_ref(v_a_6374_);
    lean_dec(v_a_6373_);
    lean_dec_ref(v_a_6372_);
    return v_res_6378_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_erase(
    mut v_pu_6379_: u8,
    mut v_decl_6380_: *mut LeanObject,
    mut v_a_6381_: *mut LeanObject,
    mut v_a_6382_: *mut LeanObject,
    mut v_a_6383_: *mut LeanObject,
    mut v_a_6384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_6387_: *mut LeanObject,
    mut v_decl_6388_: *mut LeanObject,
    mut v_a_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
    mut v_a_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6394_: u8 = 0;
    let mut v_res_6395_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6394_ = (lean_unbox(v_pu_6387_) as u8);
    v_res_6395_ = l_Lean_Compiler_LCNF_Decl_erase(
        v_pu_boxed_6394_,
        v_decl_6388_,
        v_a_6389_,
        v_a_6390_,
        v_a_6391_,
        v_a_6392_,
    );
    lean_dec(v_a_6392_);
    lean_dec_ref(v_a_6391_);
    lean_dec(v_a_6390_);
    lean_dec_ref(v_a_6389_);
    return v_res_6395_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(
    mut v_msg_6396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    v___x_6397_ = l_Lean_instInhabitedExpr;
    v___x_6398_ = lean_panic_fn_borrowed(v___x_6397_, v_msg_6396_);
    return v___x_6398_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3()
-> *mut LeanObject {
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    v___x_6402_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__2;
    v___x_6403_ = lean_unsigned_to_nat(20);
    v___x_6404_ = lean_unsigned_to_nat(215);
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
    mut v_s_6409_: *mut LeanObject,
    mut v_translator_6410_: u8,
    mut v_e_6411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6412_: u8 = 0;
    let mut v_fvarId_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6430_: u8 = 0;
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: usize = 0;
    let mut v___x_6435_: usize = 0;
    let mut v___x_6436_: u8 = 0;
    let mut v___x_6437_: usize = 0;
    let mut v___x_6438_: usize = 0;
    let mut v___x_6439_: u8 = 0;
    let mut v_binderName_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6443_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6447_: u8 = 0;
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: u8 = 0;
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: usize = 0;
    let mut v___x_6452_: usize = 0;
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: usize = 0;
    let mut v___x_6455_: usize = 0;
    let mut v___x_6456_: u8 = 0;
    let mut v_binderName_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6460_: u8 = 0;
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6464_: u8 = 0;
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: u8 = 0;
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: usize = 0;
    let mut v___x_6469_: usize = 0;
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6471_: usize = 0;
    let mut v___x_6472_: usize = 0;
    let mut v___x_6473_: u8 = 0;
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: u8 = 0;
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: usize = 0;
    let mut v___x_6488_: usize = 0;
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6412_ = l_Lean_Expr_hasFVar(v_e_6411_);
                if v___x_6412_ == 0 {
                    return v_e_6411_;
                } else {
                    match lean_obj_tag(v_e_6411_) {
                        1 => {
                            v_fvarId_6413_ = lean_ctor_get(v_e_6411_, 0);
                            v___x_6414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6409_, v_fvarId_6413_);
                            if lean_obj_tag(v___x_6414_) == 0 {
                                return v_e_6411_;
                            } else {
                                lean_dec_ref_known(v_e_6411_, 1);
                                v_val_6415_ = lean_ctor_get(v___x_6414_, 0);
                                lean_inc(v_val_6415_);
                                lean_dec_ref_known(v___x_6414_, 1);
                                match lean_obj_tag(v_val_6415_) {
                                    0 => {
                                        v___x_6416_ = l_Lean_Compiler_LCNF_erasedExpr;
                                        return v___x_6416_;
                                    }
                                    1 => {
                                        if v_translator_6410_ == 0 {
                                            v_fvarId_6417_ = lean_ctor_get(v_val_6415_, 0);
                                            lean_inc(v_fvarId_6417_);
                                            lean_dec_ref_known(v_val_6415_, 1);
                                            v___x_6418_ =
                                                l_Lean_Expr_fvar___override(v_fvarId_6417_);
                                            v_e_6411_ = v___x_6418_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v_fvarId_6420_ = lean_ctor_get(v_val_6415_, 0);
                                            lean_inc(v_fvarId_6420_);
                                            lean_dec_ref_known(v_val_6415_, 1);
                                            v___x_6421_ =
                                                l_Lean_Expr_fvar___override(v_fvarId_6420_);
                                            return v___x_6421_;
                                        }
                                    }
                                    _ => {
                                        if v_translator_6410_ == 0 {
                                            v_expr_6422_ = lean_ctor_get(v_val_6415_, 0);
                                            lean_inc_ref(v_expr_6422_);
                                            lean_dec_ref_known(v_val_6415_, 1);
                                            v_e_6411_ = v_expr_6422_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v_expr_6424_ = lean_ctor_get(v_val_6415_, 0);
                                            lean_inc_ref(v_expr_6424_);
                                            lean_dec_ref_known(v_val_6415_, 1);
                                            return v_expr_6424_;
                                        }
                                    }
                                }
                            }
                        }
                        5 => {
                            v_fn_6425_ = lean_ctor_get(v_e_6411_, 0);
                            v_arg_6426_ = lean_ctor_get(v_e_6411_, 1);
                            lean_inc_ref(v_fn_6425_);
                            v___x_6427_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_6408_, v_s_6409_, v_translator_6410_, v_fn_6425_);
                            lean_inc_ref(v_arg_6426_);
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
                            v_binderName_6440_ = lean_ctor_get(v_e_6411_, 0);
                            v_binderType_6441_ = lean_ctor_get(v_e_6411_, 1);
                            v_body_6442_ = lean_ctor_get(v_e_6411_, 2);
                            v_binderInfo_6443_ = lean_ctor_get_uint8(
                                v_e_6411_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_6441_);
                            v___x_6444_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_binderType_6441_);
                            lean_inc_ref(v_body_6442_);
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
                            v_binderName_6457_ = lean_ctor_get(v_e_6411_, 0);
                            v_binderType_6458_ = lean_ctor_get(v_e_6411_, 1);
                            v_body_6459_ = lean_ctor_get(v_e_6411_, 2);
                            v_binderInfo_6460_ = lean_ctor_get_uint8(
                                v_e_6411_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_6458_);
                            v___x_6461_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_binderType_6458_);
                            lean_inc_ref(v_body_6459_);
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
                            lean_dec_ref_known(v_e_6411_, 4);
                            v___x_6474_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___closed__3);
                            v___x_6475_ = l_panic___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go_spec__1(v___x_6474_);
                            return v___x_6475_;
                        }
                        10 => {
                            v_data_6476_ = lean_ctor_get(v_e_6411_, 0);
                            v_expr_6477_ = lean_ctor_get(v_e_6411_, 1);
                            lean_inc_ref(v_expr_6477_);
                            v___x_6478_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_expr_6477_);
                            v___x_6479_ = lean_ptr_addr(v_expr_6477_);
                            v___x_6480_ = lean_ptr_addr(v___x_6478_);
                            v___x_6481_ = lean_usize_dec_eq(v___x_6479_, v___x_6480_);
                            if v___x_6481_ == 0 {
                                lean_inc(v_data_6476_);
                                lean_dec_ref_known(v_e_6411_, 2);
                                v___x_6482_ =
                                    l_Lean_Expr_mdata___override(v_data_6476_, v___x_6478_);
                                return v___x_6482_;
                            } else {
                                lean_dec_ref(v___x_6478_);
                                return v_e_6411_;
                            }
                        }
                        11 => {
                            v_typeName_6483_ = lean_ctor_get(v_e_6411_, 0);
                            v_idx_6484_ = lean_ctor_get(v_e_6411_, 1);
                            v_struct_6485_ = lean_ctor_get(v_e_6411_, 2);
                            lean_inc_ref(v_struct_6485_);
                            v___x_6486_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_6408_, v_s_6409_, v_translator_6410_, v_struct_6485_);
                            v___x_6487_ = lean_ptr_addr(v_struct_6485_);
                            v___x_6488_ = lean_ptr_addr(v___x_6486_);
                            v___x_6489_ = lean_usize_dec_eq(v___x_6487_, v___x_6488_);
                            if v___x_6489_ == 0 {
                                lean_inc(v_idx_6484_);
                                lean_inc(v_typeName_6483_);
                                lean_dec_ref_known(v_e_6411_, 3);
                                v___x_6490_ = l_Lean_Expr_proj___override(
                                    v_typeName_6483_,
                                    v_idx_6484_,
                                    v___x_6486_,
                                );
                                return v___x_6490_;
                            } else {
                                lean_dec_ref(v___x_6486_);
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
                    lean_dec_ref_known(v_e_6411_, 2);
                    v___x_6431_ = l_Lean_Expr_app___override(v___x_6427_, v___x_6428_);
                    v___x_6432_ = l_Lean_Expr_headBeta(v___x_6431_);
                    return v___x_6432_;
                } else {
                    lean_dec_ref(v___x_6428_);
                    lean_dec_ref(v___x_6427_);
                    v___x_6433_ = l_Lean_Expr_headBeta(v_e_6411_);
                    return v___x_6433_;
                }
            }
            2 => {
                if v___y_6447_ == 0 {
                    lean_inc(v_binderName_6440_);
                    lean_dec_ref_known(v_e_6411_, 3);
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
                        lean_inc(v_binderName_6440_);
                        lean_dec_ref_known(v_e_6411_, 3);
                        v___x_6450_ = l_Lean_Expr_lam___override(
                            v_binderName_6440_,
                            v___x_6444_,
                            v___x_6445_,
                            v_binderInfo_6443_,
                        );
                        return v___x_6450_;
                    } else {
                        lean_dec_ref(v___x_6445_);
                        lean_dec_ref(v___x_6444_);
                        return v_e_6411_;
                    }
                }
            }
            3 => {
                if v___y_6464_ == 0 {
                    lean_inc(v_binderName_6457_);
                    lean_dec_ref_known(v_e_6411_, 3);
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
                        lean_inc(v_binderName_6457_);
                        lean_dec_ref_known(v_e_6411_, 3);
                        v___x_6467_ = l_Lean_Expr_forallE___override(
                            v_binderName_6457_,
                            v___x_6461_,
                            v___x_6462_,
                            v_binderInfo_6460_,
                        );
                        return v___x_6467_;
                    } else {
                        lean_dec_ref(v___x_6462_);
                        lean_dec_ref(v___x_6461_);
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
    mut v_s_6492_: *mut LeanObject,
    mut v_translator_6493_: u8,
    mut v_e_6494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6500_: u8 = 0;
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: usize = 0;
    let mut v___x_6503_: usize = 0;
    let mut v___x_6504_: u8 = 0;
    let mut v___x_6505_: usize = 0;
    let mut v___x_6506_: usize = 0;
    let mut v___x_6507_: u8 = 0;
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_6494_) == 5 {
                    v_fn_6495_ = lean_ctor_get(v_e_6494_, 0);
                    v_arg_6496_ = lean_ctor_get(v_e_6494_, 1);
                    lean_inc_ref(v_fn_6495_);
                    v___x_6497_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(v_pu_6491_, v_s_6492_, v_translator_6493_, v_fn_6495_);
                    lean_inc_ref(v_arg_6496_);
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
                    lean_dec_ref_known(v_e_6494_, 2);
                    v___x_6501_ = l_Lean_Expr_app___override(v___x_6497_, v___x_6498_);
                    return v___x_6501_;
                } else {
                    lean_dec_ref(v___x_6498_);
                    lean_dec_ref(v___x_6497_);
                    return v_e_6494_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp___boxed(
    mut v_pu_6509_: *mut LeanObject,
    mut v_s_6510_: *mut LeanObject,
    mut v_translator_6511_: *mut LeanObject,
    mut v_e_6512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6513_: u8 = 0;
    let mut v_translator_boxed_6514_: u8 = 0;
    let mut v_res_6515_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6513_ = (lean_unbox(v_pu_6509_) as u8);
    v_translator_boxed_6514_ = (lean_unbox(v_translator_6511_) as u8);
    v_res_6515_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_goApp(
        v_pu_boxed_6513_,
        v_s_6510_,
        v_translator_boxed_6514_,
        v_e_6512_,
    );
    lean_dec_ref(v_s_6510_);
    return v_res_6515_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___boxed(
    mut v_pu_6516_: *mut LeanObject,
    mut v_s_6517_: *mut LeanObject,
    mut v_translator_6518_: *mut LeanObject,
    mut v_e_6519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6520_: u8 = 0;
    let mut v_translator_boxed_6521_: u8 = 0;
    let mut v_res_6522_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6520_ = (lean_unbox(v_pu_6516_) as u8);
    v_translator_boxed_6521_ = (lean_unbox(v_translator_6518_) as u8);
    v_res_6522_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_boxed_6520_,
        v_s_6517_,
        v_translator_boxed_6521_,
        v_e_6519_,
    );
    lean_dec_ref(v_s_6517_);
    return v_res_6522_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(
    mut v_pu_6523_: u8,
    mut v_s_6524_: *mut LeanObject,
    mut v_e_6525_: *mut LeanObject,
    mut v_translator_6526_: u8,
) -> *mut LeanObject {
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    v___x_6527_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_6523_,
        v_s_6524_,
        v_translator_6526_,
        v_e_6525_,
    );
    return v___x_6527_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp___boxed(
    mut v_pu_6528_: *mut LeanObject,
    mut v_s_6529_: *mut LeanObject,
    mut v_e_6530_: *mut LeanObject,
    mut v_translator_6531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6532_: u8 = 0;
    let mut v_translator_boxed_6533_: u8 = 0;
    let mut v_res_6534_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6532_ = (lean_unbox(v_pu_6528_) as u8);
    v_translator_boxed_6533_ = (lean_unbox(v_translator_6531_) as u8);
    v_res_6534_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp(
        v_pu_boxed_6532_,
        v_s_6529_,
        v_e_6530_,
        v_translator_boxed_6533_,
    );
    lean_dec_ref(v_s_6529_);
    return v_res_6534_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(
    mut v_x_6535_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6535_) == 0 {
        let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
        v___x_6536_ = lean_unsigned_to_nat(0);
        return v___x_6536_;
    } else {
        let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
        v___x_6537_ = lean_unsigned_to_nat(1);
        return v___x_6537_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx___boxed(
    mut v_x_6538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6539_: *mut LeanObject = core::ptr::null_mut();
    v_res_6539_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorIdx(v_x_6538_);
    lean_dec(v_x_6538_);
    return v_res_6539_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(
    mut v_t_6540_: *mut LeanObject,
    mut v_k_6541_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_6540_) == 0 {
        let mut v_fvarId_6542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_6542_ = lean_ctor_get(v_t_6540_, 0);
        lean_inc(v_fvarId_6542_);
        lean_dec_ref_known(v_t_6540_, 1);
        v___x_6543_ = lean_apply_1(v_k_6541_, v_fvarId_6542_);
        return v___x_6543_;
    } else {
        return v_k_6541_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(
    mut v_motive_6544_: *mut LeanObject,
    mut v_ctorIdx_6545_: *mut LeanObject,
    mut v_t_6546_: *mut LeanObject,
    mut v_h_6547_: *mut LeanObject,
    mut v_k_6548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    v___x_6549_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6546_, v_k_6548_);
    return v___x_6549_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___boxed(
    mut v_motive_6550_: *mut LeanObject,
    mut v_ctorIdx_6551_: *mut LeanObject,
    mut v_t_6552_: *mut LeanObject,
    mut v_h_6553_: *mut LeanObject,
    mut v_k_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6555_: *mut LeanObject = core::ptr::null_mut();
    v_res_6555_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim(
        v_motive_6550_,
        v_ctorIdx_6551_,
        v_t_6552_,
        v_h_6553_,
        v_k_6554_,
    );
    lean_dec(v_ctorIdx_6551_);
    return v_res_6555_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim___redArg(
    mut v_t_6556_: *mut LeanObject,
    mut v_fvar_6557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6556_, v_fvar_6557_);
    return v___x_6558_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_fvar_elim(
    mut v_motive_6559_: *mut LeanObject,
    mut v_t_6560_: *mut LeanObject,
    mut v_h_6561_: *mut LeanObject,
    mut v_fvar_6562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    v___x_6563_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6560_, v_fvar_6562_);
    return v___x_6563_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_erased_elim___redArg(
    mut v_t_6564_: *mut LeanObject,
    mut v_erased_6565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    v___x_6566_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6564_, v_erased_6565_);
    return v___x_6566_;
}
pub unsafe fn l_Lean_Compiler_LCNF_NormFVarResult_erased_elim(
    mut v_motive_6567_: *mut LeanObject,
    mut v_t_6568_: *mut LeanObject,
    mut v_h_6569_: *mut LeanObject,
    mut v_erased_6570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    v___x_6571_ = l_Lean_Compiler_LCNF_NormFVarResult_ctorElim___redArg(v_t_6568_, v_erased_6570_);
    return v___x_6571_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp___redArg(
    mut v_s_6576_: *mut LeanObject,
    mut v_fvarId_6577_: *mut LeanObject,
    mut v_translator_6578_: u8,
) -> *mut LeanObject {
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6576_, v_fvarId_6577_);
                if lean_obj_tag(v___x_6579_) == 0 {
                    v___x_6580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6580_, 0, v_fvarId_6577_);
                    return v___x_6580_;
                } else {
                    lean_dec(v_fvarId_6577_);
                    v_val_6581_ = lean_ctor_get(v___x_6579_, 0);
                    lean_inc(v_val_6581_);
                    lean_dec_ref_known(v___x_6579_, 1);
                    if lean_obj_tag(v_val_6581_) == 1 {
                        if v_translator_6578_ == 0 {
                            v_fvarId_6582_ = lean_ctor_get(v_val_6581_, 0);
                            lean_inc(v_fvarId_6582_);
                            lean_dec_ref_known(v_val_6581_, 1);
                            v_fvarId_6577_ = v_fvarId_6582_;
                            state = 0;
                            continue;
                        } else {
                            v_fvarId_6584_ = lean_ctor_get(v_val_6581_, 0);
                            v_isSharedCheck_6591_ = (!lean_is_exclusive(v_val_6581_)) as u8;
                            if v_isSharedCheck_6591_ == 0 {
                                v___x_6586_ = v_val_6581_;
                                v_isShared_6587_ = v_isSharedCheck_6591_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_fvarId_6584_);
                                lean_dec(v_val_6581_);
                                v___x_6586_ = lean_box(0);
                                v_isShared_6587_ = v_isSharedCheck_6591_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_6581_);
                        v___x_6592_ = lean_box(1);
                        return v___x_6592_;
                    }
                }
            }
            1 => {
                if v_isShared_6587_ == 0 {
                    lean_ctor_set_tag(v___x_6586_, 0);
                    v___x_6589_ = v___x_6586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_fvarId_6584_);
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
    mut v_s_6593_: *mut LeanObject,
    mut v_fvarId_6594_: *mut LeanObject,
    mut v_translator_6595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_translator_boxed_6596_: u8 = 0;
    let mut v_res_6597_: *mut LeanObject = core::ptr::null_mut();
    v_translator_boxed_6596_ = (lean_unbox(v_translator_6595_) as u8);
    v_res_6597_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
        v_s_6593_,
        v_fvarId_6594_,
        v_translator_boxed_6596_,
    );
    lean_dec_ref(v_s_6593_);
    return v_res_6597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp(
    mut v_pu_6598_: u8,
    mut v_s_6599_: *mut LeanObject,
    mut v_fvarId_6600_: *mut LeanObject,
    mut v_translator_6601_: u8,
) -> *mut LeanObject {
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    v___x_6602_ =
        l_Lean_Compiler_LCNF_normFVarImp___redArg(v_s_6599_, v_fvarId_6600_, v_translator_6601_);
    return v___x_6602_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVarImp___boxed(
    mut v_pu_6603_: *mut LeanObject,
    mut v_s_6604_: *mut LeanObject,
    mut v_fvarId_6605_: *mut LeanObject,
    mut v_translator_6606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6607_: u8 = 0;
    let mut v_translator_boxed_6608_: u8 = 0;
    let mut v_res_6609_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6607_ = (lean_unbox(v_pu_6603_) as u8);
    v_translator_boxed_6608_ = (lean_unbox(v_translator_6606_) as u8);
    v_res_6609_ = l_Lean_Compiler_LCNF_normFVarImp(
        v_pu_boxed_6607_,
        v_s_6604_,
        v_fvarId_6605_,
        v_translator_boxed_6608_,
    );
    lean_dec_ref(v_s_6604_);
    return v_res_6609_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
    mut v_pu_6610_: u8,
    mut v_s_6611_: *mut LeanObject,
    mut v_arg_6612_: *mut LeanObject,
    mut v_translator_6613_: u8,
) -> *mut LeanObject {
    let mut v_fvarId_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6626_: u8 = 0;
    let mut v_expr_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6630_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v_expr_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_arg_6612_) {
                0 => {
                    return v_arg_6612_;
                }
                1 => {
                    v_fvarId_6614_ = lean_ctor_get(v_arg_6612_, 0);
                    v___x_6615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_getType_spec__0___redArg(v_s_6611_, v_fvarId_6614_);
                    if lean_obj_tag(v___x_6615_) == 0 {
                        return v_arg_6612_;
                    } else {
                        lean_dec_ref_known(v_arg_6612_, 1);
                        v_val_6616_ = lean_ctor_get(v___x_6615_, 0);
                        lean_inc(v_val_6616_);
                        lean_dec_ref_known(v___x_6615_, 1);
                        match lean_obj_tag(v_val_6616_) {
                            0 => {
                                v___x_6617_ = lean_box(0);
                                return v___x_6617_;
                            }
                            1 => {
                                v_fvarId_6618_ = lean_ctor_get(v_val_6616_, 0);
                                v_isSharedCheck_6626_ = (!lean_is_exclusive(v_val_6616_)) as u8;
                                if v_isSharedCheck_6626_ == 0 {
                                    v___x_6620_ = v_val_6616_;
                                    v_isShared_6621_ = v_isSharedCheck_6626_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_fvarId_6618_);
                                    lean_dec(v_val_6616_);
                                    v___x_6620_ = lean_box(0);
                                    v_isShared_6621_ = v_isSharedCheck_6626_;
                                    state = 1;
                                    continue;
                                }
                            }
                            _ => {
                                v_expr_6627_ = lean_ctor_get(v_val_6616_, 0);
                                v_isSharedCheck_6634_ = (!lean_is_exclusive(v_val_6616_)) as u8;
                                if v_isSharedCheck_6634_ == 0 {
                                    v___x_6629_ = v_val_6616_;
                                    v_isShared_6630_ = v_isSharedCheck_6634_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_expr_6627_);
                                    lean_dec(v_val_6616_);
                                    v___x_6629_ = lean_box(0);
                                    v_isShared_6630_ = v_isSharedCheck_6634_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {
                    v_expr_6635_ = lean_ctor_get(v_arg_6612_, 0);
                    lean_inc_ref(v_expr_6635_);
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
                    v_reuseFailAlloc_6625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_fvarId_6618_);
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
                    v_reuseFailAlloc_6633_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_expr_6627_);
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
    mut v_pu_6638_: *mut LeanObject,
    mut v_s_6639_: *mut LeanObject,
    mut v_arg_6640_: *mut LeanObject,
    mut v_translator_6641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6642_: u8 = 0;
    let mut v_translator_boxed_6643_: u8 = 0;
    let mut v_res_6644_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6642_ = (lean_unbox(v_pu_6638_) as u8);
    v_translator_boxed_6643_ = (lean_unbox(v_translator_6641_) as u8);
    v_res_6644_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
        v_pu_boxed_6642_,
        v_s_6639_,
        v_arg_6640_,
        v_translator_boxed_6643_,
    );
    lean_dec_ref(v_s_6639_);
    return v_res_6644_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(
    mut v_pu_6645_: u8,
    mut v_s_6646_: *mut LeanObject,
    mut v_translator_6647_: u8,
    mut v_i_6648_: *mut LeanObject,
    mut v_as_6649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: u8 = 0;
    let mut v_a_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: usize = 0;
    let mut v___x_6655_: usize = 0;
    let mut v___x_6656_: u8 = 0;
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6650_ = lean_array_get_size(v_as_6649_);
                v___x_6651_ = lean_nat_dec_lt(v_i_6648_, v___x_6650_);
                if v___x_6651_ == 0 {
                    lean_dec(v_i_6648_);
                    return v_as_6649_;
                } else {
                    v_a_6652_ = lean_array_fget_borrowed(v_as_6649_, v_i_6648_);
                    lean_inc(v_a_6652_);
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
                        v___x_6657_ = lean_unsigned_to_nat(1);
                        v___x_6658_ = lean_nat_add(v_i_6648_, v___x_6657_);
                        v___x_6659_ = lean_array_fset(v_as_6649_, v_i_6648_, v___x_6653_);
                        lean_dec(v_i_6648_);
                        v_i_6648_ = v___x_6658_;
                        v_as_6649_ = v___x_6659_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_6653_);
                        v___x_6661_ = lean_unsigned_to_nat(1);
                        v___x_6662_ = lean_nat_add(v_i_6648_, v___x_6661_);
                        lean_dec(v_i_6648_);
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
    mut v_pu_6664_: *mut LeanObject,
    mut v_s_6665_: *mut LeanObject,
    mut v_translator_6666_: *mut LeanObject,
    mut v_i_6667_: *mut LeanObject,
    mut v_as_6668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6669_: u8 = 0;
    let mut v_translator_boxed_6670_: u8 = 0;
    let mut v_res_6671_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6669_ = (lean_unbox(v_pu_6664_) as u8);
    v_translator_boxed_6670_ = (lean_unbox(v_translator_6666_) as u8);
    v_res_6671_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_boxed_6669_, v_s_6665_, v_translator_boxed_6670_, v_i_6667_, v_as_6668_);
    lean_dec_ref(v_s_6665_);
    return v_res_6671_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
    mut v_pu_6672_: u8,
    mut v_s_6673_: *mut LeanObject,
    mut v_args_6674_: *mut LeanObject,
    mut v_translator_6675_: u8,
) -> *mut LeanObject {
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    v___x_6676_ = lean_unsigned_to_nat(0);
    v___x_6677_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp_spec__0(v_pu_6672_, v_s_6673_, v_translator_6675_, v___x_6676_, v_args_6674_);
    return v___x_6677_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp___boxed(
    mut v_pu_6678_: *mut LeanObject,
    mut v_s_6679_: *mut LeanObject,
    mut v_args_6680_: *mut LeanObject,
    mut v_translator_6681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6682_: u8 = 0;
    let mut v_translator_boxed_6683_: u8 = 0;
    let mut v_res_6684_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6682_ = (lean_unbox(v_pu_6678_) as u8);
    v_translator_boxed_6683_ = (lean_unbox(v_translator_6681_) as u8);
    v_res_6684_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_boxed_6682_,
        v_s_6679_,
        v_args_6680_,
        v_translator_boxed_6683_,
    );
    lean_dec_ref(v_s_6679_);
    return v_res_6684_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
    mut v_pu_6685_: u8,
    mut v_s_6686_: *mut LeanObject,
    mut v_e_6687_: *mut LeanObject,
    mut v_translator_6688_: u8,
) -> *mut LeanObject {
    let mut v_fvarId_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_6734_: u8 = 0;
    let mut v_args_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_e_6687_) {
                    2 => {
                        v_struct_6699_ = lean_ctor_get(v_e_6687_, 2);
                        lean_inc(v_struct_6699_);
                        v___x_6700_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_struct_6699_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6700_) == 0 {
                            v_fvarId_6701_ = lean_ctor_get(v___x_6700_, 0);
                            lean_inc(v_fvarId_6701_);
                            lean_dec_ref_known(v___x_6700_, 1);
                            v___x_6702_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6701_);
                            return v___x_6702_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6703_ = lean_box(1);
                            return v___x_6703_;
                        }
                    }
                    3 => {
                        v_args_6704_ = lean_ctor_get(v_e_6687_, 2);
                        lean_inc_ref(v_args_6704_);
                        v___x_6705_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6704_, v_translator_6688_);
                        v___x_6706_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_6685_, v_e_6687_, v___x_6705_);
                        return v___x_6706_;
                    }
                    4 => {
                        v_fvarId_6707_ = lean_ctor_get(v_e_6687_, 0);
                        v_args_6708_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc(v_fvarId_6707_);
                        v___x_6709_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6707_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6709_) == 0 {
                            v_fvarId_6710_ = lean_ctor_get(v___x_6709_, 0);
                            lean_inc(v_fvarId_6710_);
                            lean_dec_ref_known(v___x_6709_, 1);
                            lean_inc_ref(v_args_6708_);
                            v___x_6711_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6708_, v_translator_6688_);
                            v___x_6712_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(v_pu_6685_, v_e_6687_, v_fvarId_6710_, v___x_6711_);
                            lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6712_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 2);
                            v___x_6713_ = lean_box(1);
                            return v___x_6713_;
                        }
                    }
                    5 => {
                        v_args_6714_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc_ref(v_args_6714_);
                        v___x_6715_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6714_, v_translator_6688_);
                        v___x_6716_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(v_pu_6685_, v_e_6687_, v___x_6715_);
                        return v___x_6716_;
                    }
                    6 => {
                        v_var_6717_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc(v_var_6717_);
                        v_fvarId_6690_ = v_var_6717_;
                        state = 1;
                        continue;
                    }
                    7 => {
                        v_var_6718_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc(v_var_6718_);
                        v_fvarId_6690_ = v_var_6718_;
                        state = 1;
                        continue;
                    }
                    8 => {
                        v_var_6719_ = lean_ctor_get(v_e_6687_, 2);
                        lean_inc(v_var_6719_);
                        v___x_6720_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6719_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6720_) == 0 {
                            v_fvarId_6721_ = lean_ctor_get(v___x_6720_, 0);
                            lean_inc(v_fvarId_6721_);
                            lean_dec_ref_known(v___x_6720_, 1);
                            v___x_6722_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6721_);
                            return v___x_6722_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6723_ = lean_box(1);
                            return v___x_6723_;
                        }
                    }
                    9 => {
                        v_args_6724_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc_ref(v_args_6724_);
                        v_args_6696_ = v_args_6724_;
                        state = 2;
                        continue;
                    }
                    10 => {
                        v_args_6725_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc_ref(v_args_6725_);
                        v_args_6696_ = v_args_6725_;
                        state = 2;
                        continue;
                    }
                    11 => {
                        v_n_6726_ = lean_ctor_get(v_e_6687_, 0);
                        lean_inc(v_n_6726_);
                        v_var_6727_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc(v_var_6727_);
                        v___x_6728_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6727_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6728_) == 0 {
                            v_fvarId_6729_ = lean_ctor_get(v___x_6728_, 0);
                            lean_inc(v_fvarId_6729_);
                            lean_dec_ref_known(v___x_6728_, 1);
                            v___x_6730_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(v_pu_6685_, v_e_6687_, v_n_6726_, v_fvarId_6729_);
                            lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6730_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 2);
                            lean_dec(v_n_6726_);
                            v___x_6731_ = lean_box(1);
                            return v___x_6731_;
                        }
                    }
                    12 => {
                        v_var_6732_ = lean_ctor_get(v_e_6687_, 0);
                        v_i_6733_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc_ref(v_i_6733_);
                        v_updateHeader_6734_ = lean_ctor_get_uint8(
                            v_e_6687_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_args_6735_ = lean_ctor_get(v_e_6687_, 2);
                        lean_inc(v_var_6732_);
                        v___x_6736_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_var_6732_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6736_) == 0 {
                            v_fvarId_6737_ = lean_ctor_get(v___x_6736_, 0);
                            lean_inc(v_fvarId_6737_);
                            lean_dec_ref_known(v___x_6736_, 1);
                            lean_inc_ref(v_args_6735_);
                            v___x_6738_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(v_pu_6685_, v_s_6686_, v_args_6735_, v_translator_6688_);
                            v___x_6739_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(v_pu_6685_, v_e_6687_, v_fvarId_6737_, v_i_6733_, v_updateHeader_6734_, v___x_6738_);
                            return v___x_6739_;
                        } else {
                            lean_dec_ref(v_i_6733_);
                            lean_dec_ref_known(v_e_6687_, 3);
                            v___x_6740_ = lean_box(1);
                            return v___x_6740_;
                        }
                    }
                    13 => {
                        v_ty_6741_ = lean_ctor_get(v_e_6687_, 0);
                        lean_inc_ref(v_ty_6741_);
                        v_fvarId_6742_ = lean_ctor_get(v_e_6687_, 1);
                        lean_inc(v_fvarId_6742_);
                        v___x_6743_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6742_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6743_) == 0 {
                            v_fvarId_6744_ = lean_ctor_get(v___x_6743_, 0);
                            lean_inc(v_fvarId_6744_);
                            lean_dec_ref_known(v___x_6743_, 1);
                            v___x_6745_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(v_pu_6685_, v_e_6687_, v_ty_6741_, v_fvarId_6744_);
                            lean_dec_ref_known(v_e_6687_, 2);
                            return v___x_6745_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 2);
                            lean_dec_ref(v_ty_6741_);
                            v___x_6746_ = lean_box(1);
                            return v___x_6746_;
                        }
                    }
                    14 => {
                        v_fvarId_6747_ = lean_ctor_get(v_e_6687_, 0);
                        lean_inc(v_fvarId_6747_);
                        v___x_6748_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6747_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6748_) == 0 {
                            v_fvarId_6749_ = lean_ctor_get(v___x_6748_, 0);
                            lean_inc(v_fvarId_6749_);
                            lean_dec_ref_known(v___x_6748_, 1);
                            v___x_6750_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(v_pu_6685_, v_e_6687_, v_fvarId_6749_);
                            return v___x_6750_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 1);
                            v___x_6751_ = lean_box(1);
                            return v___x_6751_;
                        }
                    }
                    15 => {
                        v_fvarId_6752_ = lean_ctor_get(v_e_6687_, 0);
                        lean_inc(v_fvarId_6752_);
                        v___x_6753_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_s_6686_,
                            v_fvarId_6752_,
                            v_translator_6688_,
                        );
                        if lean_obj_tag(v___x_6753_) == 0 {
                            v_fvarId_6754_ = lean_ctor_get(v___x_6753_, 0);
                            lean_inc(v_fvarId_6754_);
                            lean_dec_ref_known(v___x_6753_, 1);
                            v___x_6755_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(v_pu_6685_, v_e_6687_, v_fvarId_6754_);
                            return v___x_6755_;
                        } else {
                            lean_dec_ref_known(v_e_6687_, 1);
                            v___x_6756_ = lean_box(1);
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
                if lean_obj_tag(v___x_6691_) == 0 {
                    v_fvarId_6692_ = lean_ctor_get(v___x_6691_, 0);
                    lean_inc(v_fvarId_6692_);
                    lean_dec_ref_known(v___x_6691_, 1);
                    v___x_6693_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(v_pu_6685_, v_e_6687_, v_fvarId_6692_);
                    return v___x_6693_;
                } else {
                    lean_dec(v_e_6687_);
                    v___x_6694_ = lean_box(1);
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
    mut v_pu_6757_: *mut LeanObject,
    mut v_s_6758_: *mut LeanObject,
    mut v_e_6759_: *mut LeanObject,
    mut v_translator_6760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6761_: u8 = 0;
    let mut v_translator_boxed_6762_: u8 = 0;
    let mut v_res_6763_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6761_ = (lean_unbox(v_pu_6757_) as u8);
    v_translator_boxed_6762_ = (lean_unbox(v_translator_6760_) as u8);
    v_res_6763_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_boxed_6761_,
        v_s_6758_,
        v_e_6759_,
        v_translator_boxed_6762_,
    );
    lean_dec_ref(v_s_6758_);
    return v_res_6763_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___redArg(
    mut v_inst_6764_: *mut LeanObject,
    mut v_inst_6765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    v___x_6766_ = lean_apply_2(v_inst_6764_, lean_box(0), v_inst_6765_);
    return v___x_6766_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift(
    mut v_pu_6767_: u8,
    mut v_t_6768_: u8,
    mut v_m_6769_: *mut LeanObject,
    mut v_n_6770_: *mut LeanObject,
    mut v_inst_6771_: *mut LeanObject,
    mut v_inst_6772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    v___x_6773_ = lean_apply_2(v_inst_6771_, lean_box(0), v_inst_6772_);
    return v___x_6773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstOfMonadLift___boxed(
    mut v_pu_6774_: *mut LeanObject,
    mut v_t_6775_: *mut LeanObject,
    mut v_m_6776_: *mut LeanObject,
    mut v_n_6777_: *mut LeanObject,
    mut v_inst_6778_: *mut LeanObject,
    mut v_inst_6779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6780_: u8 = 0;
    let mut v_t_boxed_6781_: u8 = 0;
    let mut v_res_6782_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6780_ = (lean_unbox(v_pu_6774_) as u8);
    v_t_boxed_6781_ = (lean_unbox(v_t_6775_) as u8);
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
    mut v_inst_6783_: *mut LeanObject,
    mut v_inst_6784_: *mut LeanObject,
    mut v_f_6785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    v___x_6786_ = lean_apply_1(v_inst_6783_, v_f_6785_);
    v___x_6787_ = lean_apply_2(v_inst_6784_, lean_box(0), v___x_6786_);
    return v___x_6787_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg(
    mut v_inst_6788_: *mut LeanObject,
    mut v_inst_6789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6790_: *mut LeanObject = core::ptr::null_mut();
    v___f_6790_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6790_, 0, v_inst_6789_);
    lean_closure_set(v___f_6790_, 1, v_inst_6788_);
    return v___f_6790_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift(
    mut v_pu_6791_: u8,
    mut v_m_6792_: *mut LeanObject,
    mut v_n_6793_: *mut LeanObject,
    mut v_inst_6794_: *mut LeanObject,
    mut v_inst_6795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6796_: *mut LeanObject = core::ptr::null_mut();
    v___f_6796_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6796_, 0, v_inst_6795_);
    lean_closure_set(v___f_6796_, 1, v_inst_6794_);
    return v___f_6796_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstStateOfMonadLift___boxed(
    mut v_pu_6797_: *mut LeanObject,
    mut v_m_6798_: *mut LeanObject,
    mut v_n_6799_: *mut LeanObject,
    mut v_inst_6800_: *mut LeanObject,
    mut v_inst_6801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6802_: u8 = 0;
    let mut v_res_6803_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6802_ = (lean_unbox(v_pu_6797_) as u8);
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
    mut v___x_6804_: *mut LeanObject,
    mut v___x_6805_: *mut LeanObject,
    mut v_fvarId_6806_: *mut LeanObject,
    mut v_arg_6807_: *mut LeanObject,
    mut v_s_6808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_6812_: *mut LeanObject,
    mut v_fvarId_6813_: *mut LeanObject,
    mut v_arg_6814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    v___x_6815_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6816_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6817_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_addSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6817_, 0, v___x_6815_);
    lean_closure_set(v___f_6817_, 1, v___x_6816_);
    lean_closure_set(v___f_6817_, 2, v_fvarId_6813_);
    lean_closure_set(v___f_6817_, 3, v_arg_6814_);
    v___x_6818_ = lean_apply_1(v_inst_6812_, v___f_6817_);
    return v___x_6818_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst(
    mut v_m_6819_: *mut LeanObject,
    mut v_pu_6820_: u8,
    mut v_inst_6821_: *mut LeanObject,
    mut v_fvarId_6822_: *mut LeanObject,
    mut v_arg_6823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    v___x_6824_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6825_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6826_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_addSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6826_, 0, v___x_6824_);
    lean_closure_set(v___f_6826_, 1, v___x_6825_);
    lean_closure_set(v___f_6826_, 2, v_fvarId_6822_);
    lean_closure_set(v___f_6826_, 3, v_arg_6823_);
    v___x_6827_ = lean_apply_1(v_inst_6821_, v___f_6826_);
    return v___x_6827_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSubst___boxed(
    mut v_m_6828_: *mut LeanObject,
    mut v_pu_6829_: *mut LeanObject,
    mut v_inst_6830_: *mut LeanObject,
    mut v_fvarId_6831_: *mut LeanObject,
    mut v_arg_6832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6833_: u8 = 0;
    let mut v_res_6834_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6833_ = (lean_unbox(v_pu_6829_) as u8);
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
    mut v_fvarId_x27_6835_: *mut LeanObject,
    mut v___x_6836_: *mut LeanObject,
    mut v___x_6837_: *mut LeanObject,
    mut v_fvarId_6838_: *mut LeanObject,
    mut v_s_6839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    v___x_6840_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6840_, 0, v_fvarId_x27_6835_);
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
    mut v_inst_6842_: *mut LeanObject,
    mut v_fvarId_6843_: *mut LeanObject,
    mut v_fvarId_x27_6844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    v___x_6845_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6846_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6847_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6847_, 0, v_fvarId_x27_6844_);
    lean_closure_set(v___f_6847_, 1, v___x_6845_);
    lean_closure_set(v___f_6847_, 2, v___x_6846_);
    lean_closure_set(v___f_6847_, 3, v_fvarId_6843_);
    v___x_6848_ = lean_apply_1(v_inst_6842_, v___f_6847_);
    return v___x_6848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst(
    mut v_m_6849_: *mut LeanObject,
    mut v_ph_6850_: u8,
    mut v_inst_6851_: *mut LeanObject,
    mut v_fvarId_6852_: *mut LeanObject,
    mut v_fvarId_x27_6853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    v___x_6854_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__0;
    v___x_6855_ = l_Lean_Compiler_LCNF_addSubst___redArg___closed__1;
    v___f_6856_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_addFVarSubst___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6856_, 0, v_fvarId_x27_6853_);
    lean_closure_set(v___f_6856_, 1, v___x_6854_);
    lean_closure_set(v___f_6856_, 2, v___x_6855_);
    lean_closure_set(v___f_6856_, 3, v_fvarId_6852_);
    v___x_6857_ = lean_apply_1(v_inst_6851_, v___f_6856_);
    return v___x_6857_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addFVarSubst___boxed(
    mut v_m_6858_: *mut LeanObject,
    mut v_ph_6859_: *mut LeanObject,
    mut v_inst_6860_: *mut LeanObject,
    mut v_fvarId_6861_: *mut LeanObject,
    mut v_fvarId_x27_6862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ph_boxed_6863_: u8 = 0;
    let mut v_res_6864_: *mut LeanObject = core::ptr::null_mut();
    v_ph_boxed_6863_ = (lean_unbox(v_ph_6859_) as u8);
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
    mut v_fvarId_6865_: *mut LeanObject,
    mut v_t_6866_: u8,
    mut v_toPure_6867_: *mut LeanObject,
    mut v_____do__lift_6868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    v___x_6869_ =
        l_Lean_Compiler_LCNF_normFVarImp___redArg(v_____do__lift_6868_, v_fvarId_6865_, v_t_6866_);
    v___x_6870_ = lean_apply_2(v_toPure_6867_, lean_box(0), v___x_6869_);
    return v___x_6870_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed(
    mut v_fvarId_6871_: *mut LeanObject,
    mut v_t_6872_: *mut LeanObject,
    mut v_toPure_6873_: *mut LeanObject,
    mut v_____do__lift_6874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6875_: u8 = 0;
    let mut v_res_6876_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6875_ = (lean_unbox(v_t_6872_) as u8);
    v_res_6876_ = l_Lean_Compiler_LCNF_normFVar___redArg___lam__0(
        v_fvarId_6871_,
        v_t_boxed_6875_,
        v_toPure_6873_,
        v_____do__lift_6874_,
    );
    lean_dec_ref(v_____do__lift_6874_);
    return v_res_6876_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg(
    mut v_t_6877_: u8,
    mut v_inst_6878_: *mut LeanObject,
    mut v_inst_6879_: *mut LeanObject,
    mut v_fvarId_6880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6881_ = lean_ctor_get(v_inst_6879_, 0);
    lean_inc_ref(v_toApplicative_6881_);
    v_toBind_6882_ = lean_ctor_get(v_inst_6879_, 1);
    lean_inc(v_toBind_6882_);
    lean_dec_ref(v_inst_6879_);
    v_toPure_6883_ = lean_ctor_get(v_toApplicative_6881_, 1);
    lean_inc(v_toPure_6883_);
    lean_dec_ref(v_toApplicative_6881_);
    v___x_6884_ = lean_box((v_t_6877_) as usize);
    v___f_6885_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6885_, 0, v_fvarId_6880_);
    lean_closure_set(v___f_6885_, 1, v___x_6884_);
    lean_closure_set(v___f_6885_, 2, v_toPure_6883_);
    v___x_6886_ = lean_apply_4(
        v_toBind_6882_,
        lean_box(0),
        lean_box(0),
        v_inst_6878_,
        v___f_6885_,
    );
    return v___x_6886_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___redArg___boxed(
    mut v_t_6887_: *mut LeanObject,
    mut v_inst_6888_: *mut LeanObject,
    mut v_inst_6889_: *mut LeanObject,
    mut v_fvarId_6890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_6891_: u8 = 0;
    let mut v_res_6892_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_6891_ = (lean_unbox(v_t_6887_) as u8);
    v_res_6892_ = l_Lean_Compiler_LCNF_normFVar___redArg(
        v_t_boxed_6891_,
        v_inst_6888_,
        v_inst_6889_,
        v_fvarId_6890_,
    );
    return v_res_6892_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar(
    mut v_m_6893_: *mut LeanObject,
    mut v_pu_6894_: u8,
    mut v_t_6895_: u8,
    mut v_inst_6896_: *mut LeanObject,
    mut v_inst_6897_: *mut LeanObject,
    mut v_fvarId_6898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6899_ = lean_ctor_get(v_inst_6897_, 0);
    lean_inc_ref(v_toApplicative_6899_);
    v_toBind_6900_ = lean_ctor_get(v_inst_6897_, 1);
    lean_inc(v_toBind_6900_);
    lean_dec_ref(v_inst_6897_);
    v_toPure_6901_ = lean_ctor_get(v_toApplicative_6899_, 1);
    lean_inc(v_toPure_6901_);
    lean_dec_ref(v_toApplicative_6899_);
    v___x_6902_ = lean_box((v_t_6895_) as usize);
    v___f_6903_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFVar___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6903_, 0, v_fvarId_6898_);
    lean_closure_set(v___f_6903_, 1, v___x_6902_);
    lean_closure_set(v___f_6903_, 2, v_toPure_6901_);
    v___x_6904_ = lean_apply_4(
        v_toBind_6900_,
        lean_box(0),
        lean_box(0),
        v_inst_6896_,
        v___f_6903_,
    );
    return v___x_6904_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFVar___boxed(
    mut v_m_6905_: *mut LeanObject,
    mut v_pu_6906_: *mut LeanObject,
    mut v_t_6907_: *mut LeanObject,
    mut v_inst_6908_: *mut LeanObject,
    mut v_inst_6909_: *mut LeanObject,
    mut v_fvarId_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6911_: u8 = 0;
    let mut v_t_boxed_6912_: u8 = 0;
    let mut v_res_6913_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6911_ = (lean_unbox(v_pu_6906_) as u8);
    v_t_boxed_6912_ = (lean_unbox(v_t_6907_) as u8);
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
    mut v_e_6916_: *mut LeanObject,
    mut v_toPure_6917_: *mut LeanObject,
    mut v_____do__lift_6918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    v___x_6919_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_6914_,
        v_____do__lift_6918_,
        v_t_6915_,
        v_e_6916_,
    );
    v___x_6920_ = lean_apply_2(v_toPure_6917_, lean_box(0), v___x_6919_);
    return v___x_6920_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed(
    mut v_pu_6921_: *mut LeanObject,
    mut v_t_6922_: *mut LeanObject,
    mut v_e_6923_: *mut LeanObject,
    mut v_toPure_6924_: *mut LeanObject,
    mut v_____do__lift_6925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6926_: u8 = 0;
    let mut v_t_boxed_6927_: u8 = 0;
    let mut v_res_6928_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6926_ = (lean_unbox(v_pu_6921_) as u8);
    v_t_boxed_6927_ = (lean_unbox(v_t_6922_) as u8);
    v_res_6928_ = l_Lean_Compiler_LCNF_normExpr___redArg___lam__0(
        v_pu_boxed_6926_,
        v_t_boxed_6927_,
        v_e_6923_,
        v_toPure_6924_,
        v_____do__lift_6925_,
    );
    lean_dec_ref(v_____do__lift_6925_);
    return v_res_6928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg(
    mut v_pu_6929_: u8,
    mut v_t_6930_: u8,
    mut v_inst_6931_: *mut LeanObject,
    mut v_inst_6932_: *mut LeanObject,
    mut v_e_6933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6934_ = lean_ctor_get(v_inst_6932_, 0);
    lean_inc_ref(v_toApplicative_6934_);
    v_toBind_6935_ = lean_ctor_get(v_inst_6932_, 1);
    lean_inc(v_toBind_6935_);
    lean_dec_ref(v_inst_6932_);
    v_toPure_6936_ = lean_ctor_get(v_toApplicative_6934_, 1);
    lean_inc(v_toPure_6936_);
    lean_dec_ref(v_toApplicative_6934_);
    v___x_6937_ = lean_box((v_pu_6929_) as usize);
    v___x_6938_ = lean_box((v_t_6930_) as usize);
    v___f_6939_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6939_, 0, v___x_6937_);
    lean_closure_set(v___f_6939_, 1, v___x_6938_);
    lean_closure_set(v___f_6939_, 2, v_e_6933_);
    lean_closure_set(v___f_6939_, 3, v_toPure_6936_);
    v___x_6940_ = lean_apply_4(
        v_toBind_6935_,
        lean_box(0),
        lean_box(0),
        v_inst_6931_,
        v___f_6939_,
    );
    return v___x_6940_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___redArg___boxed(
    mut v_pu_6941_: *mut LeanObject,
    mut v_t_6942_: *mut LeanObject,
    mut v_inst_6943_: *mut LeanObject,
    mut v_inst_6944_: *mut LeanObject,
    mut v_e_6945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6946_: u8 = 0;
    let mut v_t_boxed_6947_: u8 = 0;
    let mut v_res_6948_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6946_ = (lean_unbox(v_pu_6941_) as u8);
    v_t_boxed_6947_ = (lean_unbox(v_t_6942_) as u8);
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
    mut v_m_6949_: *mut LeanObject,
    mut v_pu_6950_: u8,
    mut v_t_6951_: u8,
    mut v_inst_6952_: *mut LeanObject,
    mut v_inst_6953_: *mut LeanObject,
    mut v_e_6954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6955_ = lean_ctor_get(v_inst_6953_, 0);
    lean_inc_ref(v_toApplicative_6955_);
    v_toBind_6956_ = lean_ctor_get(v_inst_6953_, 1);
    lean_inc(v_toBind_6956_);
    lean_dec_ref(v_inst_6953_);
    v_toPure_6957_ = lean_ctor_get(v_toApplicative_6955_, 1);
    lean_inc(v_toPure_6957_);
    lean_dec_ref(v_toApplicative_6955_);
    v___x_6958_ = lean_box((v_pu_6950_) as usize);
    v___x_6959_ = lean_box((v_t_6951_) as usize);
    v___f_6960_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6960_, 0, v___x_6958_);
    lean_closure_set(v___f_6960_, 1, v___x_6959_);
    lean_closure_set(v___f_6960_, 2, v_e_6954_);
    lean_closure_set(v___f_6960_, 3, v_toPure_6957_);
    v___x_6961_ = lean_apply_4(
        v_toBind_6956_,
        lean_box(0),
        lean_box(0),
        v_inst_6952_,
        v___f_6960_,
    );
    return v___x_6961_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExpr___boxed(
    mut v_m_6962_: *mut LeanObject,
    mut v_pu_6963_: *mut LeanObject,
    mut v_t_6964_: *mut LeanObject,
    mut v_inst_6965_: *mut LeanObject,
    mut v_inst_6966_: *mut LeanObject,
    mut v_e_6967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6968_: u8 = 0;
    let mut v_t_boxed_6969_: u8 = 0;
    let mut v_res_6970_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6968_ = (lean_unbox(v_pu_6963_) as u8);
    v_t_boxed_6969_ = (lean_unbox(v_t_6964_) as u8);
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
    mut v_arg_6972_: *mut LeanObject,
    mut v_t_6973_: u8,
    mut v_toPure_6974_: *mut LeanObject,
    mut v_____do__lift_6975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    v___x_6976_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(
        v_pu_6971_,
        v_____do__lift_6975_,
        v_arg_6972_,
        v_t_6973_,
    );
    v___x_6977_ = lean_apply_2(v_toPure_6974_, lean_box(0), v___x_6976_);
    return v___x_6977_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed(
    mut v_pu_6978_: *mut LeanObject,
    mut v_arg_6979_: *mut LeanObject,
    mut v_t_6980_: *mut LeanObject,
    mut v_toPure_6981_: *mut LeanObject,
    mut v_____do__lift_6982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_6983_: u8 = 0;
    let mut v_t_boxed_6984_: u8 = 0;
    let mut v_res_6985_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_6983_ = (lean_unbox(v_pu_6978_) as u8);
    v_t_boxed_6984_ = (lean_unbox(v_t_6980_) as u8);
    v_res_6985_ = l_Lean_Compiler_LCNF_normArg___redArg___lam__0(
        v_pu_boxed_6983_,
        v_arg_6979_,
        v_t_boxed_6984_,
        v_toPure_6981_,
        v_____do__lift_6982_,
    );
    lean_dec_ref(v_____do__lift_6982_);
    return v_res_6985_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg(
    mut v_pu_6986_: u8,
    mut v_t_6987_: u8,
    mut v_inst_6988_: *mut LeanObject,
    mut v_inst_6989_: *mut LeanObject,
    mut v_arg_6990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6991_ = lean_ctor_get(v_inst_6989_, 0);
    lean_inc_ref(v_toApplicative_6991_);
    v_toBind_6992_ = lean_ctor_get(v_inst_6989_, 1);
    lean_inc(v_toBind_6992_);
    lean_dec_ref(v_inst_6989_);
    v_toPure_6993_ = lean_ctor_get(v_toApplicative_6991_, 1);
    lean_inc(v_toPure_6993_);
    lean_dec_ref(v_toApplicative_6991_);
    v___x_6994_ = lean_box((v_pu_6986_) as usize);
    v___x_6995_ = lean_box((v_t_6987_) as usize);
    v___f_6996_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6996_, 0, v___x_6994_);
    lean_closure_set(v___f_6996_, 1, v_arg_6990_);
    lean_closure_set(v___f_6996_, 2, v___x_6995_);
    lean_closure_set(v___f_6996_, 3, v_toPure_6993_);
    v___x_6997_ = lean_apply_4(
        v_toBind_6992_,
        lean_box(0),
        lean_box(0),
        v_inst_6988_,
        v___f_6996_,
    );
    return v___x_6997_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___redArg___boxed(
    mut v_pu_6998_: *mut LeanObject,
    mut v_t_6999_: *mut LeanObject,
    mut v_inst_7000_: *mut LeanObject,
    mut v_inst_7001_: *mut LeanObject,
    mut v_arg_7002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7003_: u8 = 0;
    let mut v_t_boxed_7004_: u8 = 0;
    let mut v_res_7005_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7003_ = (lean_unbox(v_pu_6998_) as u8);
    v_t_boxed_7004_ = (lean_unbox(v_t_6999_) as u8);
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
    mut v_m_7006_: *mut LeanObject,
    mut v_pu_7007_: u8,
    mut v_t_7008_: u8,
    mut v_inst_7009_: *mut LeanObject,
    mut v_inst_7010_: *mut LeanObject,
    mut v_arg_7011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7012_ = lean_ctor_get(v_inst_7010_, 0);
    lean_inc_ref(v_toApplicative_7012_);
    v_toBind_7013_ = lean_ctor_get(v_inst_7010_, 1);
    lean_inc(v_toBind_7013_);
    lean_dec_ref(v_inst_7010_);
    v_toPure_7014_ = lean_ctor_get(v_toApplicative_7012_, 1);
    lean_inc(v_toPure_7014_);
    lean_dec_ref(v_toApplicative_7012_);
    v___x_7015_ = lean_box((v_pu_7007_) as usize);
    v___x_7016_ = lean_box((v_t_7008_) as usize);
    v___f_7017_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArg___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7017_, 0, v___x_7015_);
    lean_closure_set(v___f_7017_, 1, v_arg_7011_);
    lean_closure_set(v___f_7017_, 2, v___x_7016_);
    lean_closure_set(v___f_7017_, 3, v_toPure_7014_);
    v___x_7018_ = lean_apply_4(
        v_toBind_7013_,
        lean_box(0),
        lean_box(0),
        v_inst_7009_,
        v___f_7017_,
    );
    return v___x_7018_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArg___boxed(
    mut v_m_7019_: *mut LeanObject,
    mut v_pu_7020_: *mut LeanObject,
    mut v_t_7021_: *mut LeanObject,
    mut v_inst_7022_: *mut LeanObject,
    mut v_inst_7023_: *mut LeanObject,
    mut v_arg_7024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7025_: u8 = 0;
    let mut v_t_boxed_7026_: u8 = 0;
    let mut v_res_7027_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7025_ = (lean_unbox(v_pu_7020_) as u8);
    v_t_boxed_7026_ = (lean_unbox(v_t_7021_) as u8);
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
    mut v_e_7029_: *mut LeanObject,
    mut v_t_7030_: u8,
    mut v_toPure_7031_: *mut LeanObject,
    mut v_____do__lift_7032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    v___x_7033_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_7028_,
        v_____do__lift_7032_,
        v_e_7029_,
        v_t_7030_,
    );
    v___x_7034_ = lean_apply_2(v_toPure_7031_, lean_box(0), v___x_7033_);
    return v___x_7034_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed(
    mut v_pu_7035_: *mut LeanObject,
    mut v_e_7036_: *mut LeanObject,
    mut v_t_7037_: *mut LeanObject,
    mut v_toPure_7038_: *mut LeanObject,
    mut v_____do__lift_7039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7040_: u8 = 0;
    let mut v_t_boxed_7041_: u8 = 0;
    let mut v_res_7042_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7040_ = (lean_unbox(v_pu_7035_) as u8);
    v_t_boxed_7041_ = (lean_unbox(v_t_7037_) as u8);
    v_res_7042_ = l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0(
        v_pu_boxed_7040_,
        v_e_7036_,
        v_t_boxed_7041_,
        v_toPure_7038_,
        v_____do__lift_7039_,
    );
    lean_dec_ref(v_____do__lift_7039_);
    return v_res_7042_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg(
    mut v_pu_7043_: u8,
    mut v_t_7044_: u8,
    mut v_inst_7045_: *mut LeanObject,
    mut v_inst_7046_: *mut LeanObject,
    mut v_e_7047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7048_ = lean_ctor_get(v_inst_7046_, 0);
    lean_inc_ref(v_toApplicative_7048_);
    v_toBind_7049_ = lean_ctor_get(v_inst_7046_, 1);
    lean_inc(v_toBind_7049_);
    lean_dec_ref(v_inst_7046_);
    v_toPure_7050_ = lean_ctor_get(v_toApplicative_7048_, 1);
    lean_inc(v_toPure_7050_);
    lean_dec_ref(v_toApplicative_7048_);
    v___x_7051_ = lean_box((v_pu_7043_) as usize);
    v___x_7052_ = lean_box((v_t_7044_) as usize);
    v___f_7053_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7053_, 0, v___x_7051_);
    lean_closure_set(v___f_7053_, 1, v_e_7047_);
    lean_closure_set(v___f_7053_, 2, v___x_7052_);
    lean_closure_set(v___f_7053_, 3, v_toPure_7050_);
    v___x_7054_ = lean_apply_4(
        v_toBind_7049_,
        lean_box(0),
        lean_box(0),
        v_inst_7045_,
        v___f_7053_,
    );
    return v___x_7054_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___redArg___boxed(
    mut v_pu_7055_: *mut LeanObject,
    mut v_t_7056_: *mut LeanObject,
    mut v_inst_7057_: *mut LeanObject,
    mut v_inst_7058_: *mut LeanObject,
    mut v_e_7059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7060_: u8 = 0;
    let mut v_t_boxed_7061_: u8 = 0;
    let mut v_res_7062_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7060_ = (lean_unbox(v_pu_7055_) as u8);
    v_t_boxed_7061_ = (lean_unbox(v_t_7056_) as u8);
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
    mut v_m_7063_: *mut LeanObject,
    mut v_pu_7064_: u8,
    mut v_t_7065_: u8,
    mut v_inst_7066_: *mut LeanObject,
    mut v_inst_7067_: *mut LeanObject,
    mut v_e_7068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7069_ = lean_ctor_get(v_inst_7067_, 0);
    lean_inc_ref(v_toApplicative_7069_);
    v_toBind_7070_ = lean_ctor_get(v_inst_7067_, 1);
    lean_inc(v_toBind_7070_);
    lean_dec_ref(v_inst_7067_);
    v_toPure_7071_ = lean_ctor_get(v_toApplicative_7069_, 1);
    lean_inc(v_toPure_7071_);
    lean_dec_ref(v_toApplicative_7069_);
    v___x_7072_ = lean_box((v_pu_7064_) as usize);
    v___x_7073_ = lean_box((v_t_7065_) as usize);
    v___f_7074_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetValue___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7074_, 0, v___x_7072_);
    lean_closure_set(v___f_7074_, 1, v_e_7068_);
    lean_closure_set(v___f_7074_, 2, v___x_7073_);
    lean_closure_set(v___f_7074_, 3, v_toPure_7071_);
    v___x_7075_ = lean_apply_4(
        v_toBind_7070_,
        lean_box(0),
        lean_box(0),
        v_inst_7066_,
        v___f_7074_,
    );
    return v___x_7075_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetValue___boxed(
    mut v_m_7076_: *mut LeanObject,
    mut v_pu_7077_: *mut LeanObject,
    mut v_t_7078_: *mut LeanObject,
    mut v_inst_7079_: *mut LeanObject,
    mut v_inst_7080_: *mut LeanObject,
    mut v_e_7081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7082_: u8 = 0;
    let mut v_t_boxed_7083_: u8 = 0;
    let mut v_res_7084_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7082_ = (lean_unbox(v_pu_7077_) as u8);
    v_t_boxed_7083_ = (lean_unbox(v_t_7078_) as u8);
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
    mut v_s_7086_: *mut LeanObject,
    mut v_e_7087_: *mut LeanObject,
    mut v_translator_7088_: u8,
) -> *mut LeanObject {
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    v___x_7089_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_7085_,
        v_s_7086_,
        v_translator_7088_,
        v_e_7087_,
    );
    return v___x_7089_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normExprCore___boxed(
    mut v_pu_7090_: *mut LeanObject,
    mut v_s_7091_: *mut LeanObject,
    mut v_e_7092_: *mut LeanObject,
    mut v_translator_7093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7094_: u8 = 0;
    let mut v_translator_boxed_7095_: u8 = 0;
    let mut v_res_7096_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7094_ = (lean_unbox(v_pu_7090_) as u8);
    v_translator_boxed_7095_ = (lean_unbox(v_translator_7093_) as u8);
    v_res_7096_ = l_Lean_Compiler_LCNF_normExprCore(
        v_pu_boxed_7094_,
        v_s_7091_,
        v_e_7092_,
        v_translator_boxed_7095_,
    );
    lean_dec_ref(v_s_7091_);
    return v_res_7096_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(
    mut v_pu_7097_: u8,
    mut v_args_7098_: *mut LeanObject,
    mut v_t_7099_: u8,
    mut v_toPure_7100_: *mut LeanObject,
    mut v_____do__lift_7101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut LeanObject = core::ptr::null_mut();
    v___x_7102_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_7097_,
        v_____do__lift_7101_,
        v_args_7098_,
        v_t_7099_,
    );
    v___x_7103_ = lean_apply_2(v_toPure_7100_, lean_box(0), v___x_7102_);
    return v___x_7103_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed(
    mut v_pu_7104_: *mut LeanObject,
    mut v_args_7105_: *mut LeanObject,
    mut v_t_7106_: *mut LeanObject,
    mut v_toPure_7107_: *mut LeanObject,
    mut v_____do__lift_7108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7109_: u8 = 0;
    let mut v_t_boxed_7110_: u8 = 0;
    let mut v_res_7111_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7109_ = (lean_unbox(v_pu_7104_) as u8);
    v_t_boxed_7110_ = (lean_unbox(v_t_7106_) as u8);
    v_res_7111_ = l_Lean_Compiler_LCNF_normArgs___redArg___lam__0(
        v_pu_boxed_7109_,
        v_args_7105_,
        v_t_boxed_7110_,
        v_toPure_7107_,
        v_____do__lift_7108_,
    );
    lean_dec_ref(v_____do__lift_7108_);
    return v_res_7111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg(
    mut v_pu_7112_: u8,
    mut v_t_7113_: u8,
    mut v_inst_7114_: *mut LeanObject,
    mut v_inst_7115_: *mut LeanObject,
    mut v_args_7116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7117_ = lean_ctor_get(v_inst_7115_, 0);
    lean_inc_ref(v_toApplicative_7117_);
    v_toBind_7118_ = lean_ctor_get(v_inst_7115_, 1);
    lean_inc(v_toBind_7118_);
    lean_dec_ref(v_inst_7115_);
    v_toPure_7119_ = lean_ctor_get(v_toApplicative_7117_, 1);
    lean_inc(v_toPure_7119_);
    lean_dec_ref(v_toApplicative_7117_);
    v___x_7120_ = lean_box((v_pu_7112_) as usize);
    v___x_7121_ = lean_box((v_t_7113_) as usize);
    v___f_7122_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normArgs___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7122_, 0, v___x_7120_);
    lean_closure_set(v___f_7122_, 1, v_args_7116_);
    lean_closure_set(v___f_7122_, 2, v___x_7121_);
    lean_closure_set(v___f_7122_, 3, v_toPure_7119_);
    v___x_7123_ = lean_apply_4(
        v_toBind_7118_,
        lean_box(0),
        lean_box(0),
        v_inst_7114_,
        v___f_7122_,
    );
    return v___x_7123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___redArg___boxed(
    mut v_pu_7124_: *mut LeanObject,
    mut v_t_7125_: *mut LeanObject,
    mut v_inst_7126_: *mut LeanObject,
    mut v_inst_7127_: *mut LeanObject,
    mut v_args_7128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7129_: u8 = 0;
    let mut v_t_boxed_7130_: u8 = 0;
    let mut v_res_7131_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7129_ = (lean_unbox(v_pu_7124_) as u8);
    v_t_boxed_7130_ = (lean_unbox(v_t_7125_) as u8);
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
    mut v_m_7132_: *mut LeanObject,
    mut v_pu_7133_: u8,
    mut v_t_7134_: u8,
    mut v_inst_7135_: *mut LeanObject,
    mut v_inst_7136_: *mut LeanObject,
    mut v_args_7137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_7139_: *mut LeanObject,
    mut v_pu_7140_: *mut LeanObject,
    mut v_t_7141_: *mut LeanObject,
    mut v_inst_7142_: *mut LeanObject,
    mut v_inst_7143_: *mut LeanObject,
    mut v_args_7144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7145_: u8 = 0;
    let mut v_t_boxed_7146_: u8 = 0;
    let mut v_res_7147_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7145_ = (lean_unbox(v_pu_7140_) as u8);
    v_t_boxed_7146_ = (lean_unbox(v_t_7141_) as u8);
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
    mut v_binderName_7148_: *mut LeanObject,
    mut v_a_7149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7157_: u8 = 0;
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7151_ = lean_st_ref_get(v_a_7149_);
                v___x_7152_ = lean_st_ref_take(v_a_7149_);
                v_lctx_7153_ = lean_ctor_get(v___x_7152_, 0);
                v_nextIdx_7154_ = lean_ctor_get(v___x_7152_, 1);
                v_isSharedCheck_7167_ = (!lean_is_exclusive(v___x_7152_)) as u8;
                if v_isSharedCheck_7167_ == 0 {
                    v___x_7156_ = v___x_7152_;
                    v_isShared_7157_ = v_isSharedCheck_7167_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7154_);
                    lean_inc(v_lctx_7153_);
                    lean_dec(v___x_7152_);
                    v___x_7156_ = lean_box(0);
                    v_isShared_7157_ = v_isSharedCheck_7167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7158_ = lean_unsigned_to_nat(1);
                v___x_7159_ = lean_nat_add(v_nextIdx_7154_, v___x_7158_);
                lean_dec(v_nextIdx_7154_);
                if v_isShared_7157_ == 0 {
                    lean_ctor_set(v___x_7156_, 1, v___x_7159_);
                    v___x_7161_ = v___x_7156_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7166_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7166_, 0, v_lctx_7153_);
                    lean_ctor_set(v_reuseFailAlloc_7166_, 1, v___x_7159_);
                    v___x_7161_ = v_reuseFailAlloc_7166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7162_ = lean_st_ref_set(v_a_7149_, v___x_7161_);
                v_nextIdx_7163_ = lean_ctor_get(v___x_7151_, 1);
                lean_inc(v_nextIdx_7163_);
                lean_dec(v___x_7151_);
                v___x_7164_ = l_Lean_Name_num___override(v_binderName_7148_, v_nextIdx_7163_);
                v___x_7165_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7165_, 0, v___x_7164_);
                return v___x_7165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName___redArg___boxed(
    mut v_binderName_7168_: *mut LeanObject,
    mut v_a_7169_: *mut LeanObject,
    mut v_a_7170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7171_: *mut LeanObject = core::ptr::null_mut();
    v_res_7171_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_7168_, v_a_7169_);
    lean_dec(v_a_7169_);
    return v_res_7171_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName(
    mut v_binderName_7172_: *mut LeanObject,
    mut v_a_7173_: *mut LeanObject,
    mut v_a_7174_: *mut LeanObject,
    mut v_a_7175_: *mut LeanObject,
    mut v_a_7176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    v___x_7178_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_binderName_7172_, v_a_7174_);
    return v___x_7178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshBinderName___boxed(
    mut v_binderName_7179_: *mut LeanObject,
    mut v_a_7180_: *mut LeanObject,
    mut v_a_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
    mut v_a_7183_: *mut LeanObject,
    mut v_a_7184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7185_: *mut LeanObject = core::ptr::null_mut();
    v_res_7185_ = l_Lean_Compiler_LCNF_mkFreshBinderName(
        v_binderName_7179_,
        v_a_7180_,
        v_a_7181_,
        v_a_7182_,
        v_a_7183_,
    );
    lean_dec(v_a_7183_);
    lean_dec_ref(v_a_7182_);
    lean_dec(v_a_7181_);
    lean_dec_ref(v_a_7180_);
    return v_res_7185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
    mut v_binderName_7186_: *mut LeanObject,
    mut v_baseName_7187_: *mut LeanObject,
    mut v_a_7188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7190_: u8 = 0;
    v___x_7190_ = l_Lean_Name_isAnonymous(v_binderName_7186_);
    if v___x_7190_ == 0 {
        let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_baseName_7187_);
        v___x_7191_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7191_, 0, v_binderName_7186_);
        return v___x_7191_;
    } else {
        let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_binderName_7186_);
        v___x_7192_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_baseName_7187_, v_a_7188_);
        return v___x_7192_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg___boxed(
    mut v_binderName_7193_: *mut LeanObject,
    mut v_baseName_7194_: *mut LeanObject,
    mut v_a_7195_: *mut LeanObject,
    mut v_a_7196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7197_: *mut LeanObject = core::ptr::null_mut();
    v_res_7197_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
        v_binderName_7193_,
        v_baseName_7194_,
        v_a_7195_,
    );
    lean_dec(v_a_7195_);
    return v_res_7197_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous(
    mut v_binderName_7198_: *mut LeanObject,
    mut v_baseName_7199_: *mut LeanObject,
    mut v_a_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    v___x_7205_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
        v_binderName_7198_,
        v_baseName_7199_,
        v_a_7201_,
    );
    return v___x_7205_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ensureNotAnonymous___boxed(
    mut v_binderName_7206_: *mut LeanObject,
    mut v_baseName_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
    mut v_a_7209_: *mut LeanObject,
    mut v_a_7210_: *mut LeanObject,
    mut v_a_7211_: *mut LeanObject,
    mut v_a_7212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7213_: *mut LeanObject = core::ptr::null_mut();
    v_res_7213_ = l_Lean_Compiler_LCNF_ensureNotAnonymous(
        v_binderName_7206_,
        v_baseName_7207_,
        v_a_7208_,
        v_a_7209_,
        v_a_7210_,
        v_a_7211_,
    );
    lean_dec(v_a_7211_);
    lean_dec_ref(v_a_7210_);
    lean_dec(v_a_7209_);
    lean_dec_ref(v_a_7208_);
    return v_res_7213_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(
    mut v___y_7214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7234_: u8 = 0;
    let mut v_r_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7246_: u8 = 0;
    let mut v_unused_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7216_ = lean_st_ref_get(v___y_7214_);
                v_ngen_7217_ = lean_ctor_get(v___x_7216_, 2);
                lean_inc_ref(v_ngen_7217_);
                lean_dec(v___x_7216_);
                v_namePrefix_7218_ = lean_ctor_get(v_ngen_7217_, 0);
                v_idx_7219_ = lean_ctor_get(v_ngen_7217_, 1);
                v_isSharedCheck_7248_ = (!lean_is_exclusive(v_ngen_7217_)) as u8;
                if v_isSharedCheck_7248_ == 0 {
                    v___x_7221_ = v_ngen_7217_;
                    v_isShared_7222_ = v_isSharedCheck_7248_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_7219_);
                    lean_inc(v_namePrefix_7218_);
                    lean_dec(v_ngen_7217_);
                    v___x_7221_ = lean_box(0);
                    v_isShared_7222_ = v_isSharedCheck_7248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7223_ = lean_st_ref_take(v___y_7214_);
                v_env_7224_ = lean_ctor_get(v___x_7223_, 0);
                v_nextMacroScope_7225_ = lean_ctor_get(v___x_7223_, 1);
                v_auxDeclNGen_7226_ = lean_ctor_get(v___x_7223_, 3);
                v_traceState_7227_ = lean_ctor_get(v___x_7223_, 4);
                v_cache_7228_ = lean_ctor_get(v___x_7223_, 5);
                v_messages_7229_ = lean_ctor_get(v___x_7223_, 6);
                v_infoState_7230_ = lean_ctor_get(v___x_7223_, 7);
                v_snapshotTasks_7231_ = lean_ctor_get(v___x_7223_, 8);
                v_isSharedCheck_7246_ = (!lean_is_exclusive(v___x_7223_)) as u8;
                if v_isSharedCheck_7246_ == 0 {
                    v_unused_7247_ = lean_ctor_get(v___x_7223_, 2);
                    lean_dec(v_unused_7247_);
                    v___x_7233_ = v___x_7223_;
                    v_isShared_7234_ = v_isSharedCheck_7246_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_7231_);
                    lean_inc(v_infoState_7230_);
                    lean_inc(v_messages_7229_);
                    lean_inc(v_cache_7228_);
                    lean_inc(v_traceState_7227_);
                    lean_inc(v_auxDeclNGen_7226_);
                    lean_inc(v_nextMacroScope_7225_);
                    lean_inc(v_env_7224_);
                    lean_dec(v___x_7223_);
                    v___x_7233_ = lean_box(0);
                    v_isShared_7234_ = v_isSharedCheck_7246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_7219_);
                lean_inc(v_namePrefix_7218_);
                v_r_7235_ = l_Lean_Name_num___override(v_namePrefix_7218_, v_idx_7219_);
                v___x_7236_ = lean_unsigned_to_nat(1);
                v___x_7237_ = lean_nat_add(v_idx_7219_, v___x_7236_);
                lean_dec(v_idx_7219_);
                if v_isShared_7222_ == 0 {
                    lean_ctor_set(v___x_7221_, 1, v___x_7237_);
                    v___x_7239_ = v___x_7221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7245_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7245_, 0, v_namePrefix_7218_);
                    lean_ctor_set(v_reuseFailAlloc_7245_, 1, v___x_7237_);
                    v___x_7239_ = v_reuseFailAlloc_7245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7234_ == 0 {
                    lean_ctor_set(v___x_7233_, 2, v___x_7239_);
                    v___x_7241_ = v___x_7233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7244_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 0, v_env_7224_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 1, v_nextMacroScope_7225_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 2, v___x_7239_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 3, v_auxDeclNGen_7226_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 4, v_traceState_7227_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 5, v_cache_7228_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 6, v_messages_7229_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 7, v_infoState_7230_);
                    lean_ctor_set(v_reuseFailAlloc_7244_, 8, v_snapshotTasks_7231_);
                    v___x_7241_ = v_reuseFailAlloc_7244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7242_ = lean_st_ref_set(v___y_7214_, v___x_7241_);
                v___x_7243_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7243_, 0, v_r_7235_);
                return v___x_7243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg___boxed(
    mut v___y_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7251_: *mut LeanObject = core::ptr::null_mut();
    v_res_7251_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7249_);
    lean_dec(v___y_7249_);
    return v_res_7251_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
    mut v___y_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
    mut v___y_7254_: *mut LeanObject,
    mut v___y_7255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7261_: u8 = 0;
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7257_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7255_);
                v_a_7258_ = lean_ctor_get(v___x_7257_, 0);
                v_isSharedCheck_7265_ = (!lean_is_exclusive(v___x_7257_)) as u8;
                if v_isSharedCheck_7265_ == 0 {
                    v___x_7260_ = v___x_7257_;
                    v_isShared_7261_ = v_isSharedCheck_7265_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7258_);
                    lean_dec(v___x_7257_);
                    v___x_7260_ = lean_box(0);
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
                    v_reuseFailAlloc_7264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7264_, 0, v_a_7258_);
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
    mut v___y_7266_: *mut LeanObject,
    mut v___y_7267_: *mut LeanObject,
    mut v___y_7268_: *mut LeanObject,
    mut v___y_7269_: *mut LeanObject,
    mut v___y_7270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7271_: *mut LeanObject = core::ptr::null_mut();
    v_res_7271_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
        v___y_7266_,
        v___y_7267_,
        v___y_7268_,
        v___y_7269_,
    );
    lean_dec(v___y_7269_);
    lean_dec_ref(v___y_7268_);
    lean_dec(v___y_7267_);
    lean_dec_ref(v___y_7266_);
    return v_res_7271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkParam(
    mut v_pu_7275_: u8,
    mut v_binderName_7276_: *mut LeanObject,
    mut v_type_7277_: *mut LeanObject,
    mut v_borrow_7278_: u8,
    mut v_a_7279_: *mut LeanObject,
    mut v_a_7280_: *mut LeanObject,
    mut v_a_7281_: *mut LeanObject,
    mut v_a_7282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7291_: u8 = 0;
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7297_: u8 = 0;
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7307_: u8 = 0;
    let mut v_isSharedCheck_7308_: u8 = 0;
    let mut v_a_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7312_: u8 = 0;
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7284_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7279_, v_a_7280_, v_a_7281_, v_a_7282_,
                );
                if lean_obj_tag(v___x_7284_) == 0 {
                    v_a_7285_ = lean_ctor_get(v___x_7284_, 0);
                    lean_inc(v_a_7285_);
                    lean_dec_ref_known(v___x_7284_, 1);
                    v___x_7286_ = l_Lean_Compiler_LCNF_mkParam___closed__1;
                    v___x_7287_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7276_,
                        v___x_7286_,
                        v_a_7280_,
                    );
                    v_a_7288_ = lean_ctor_get(v___x_7287_, 0);
                    v_isSharedCheck_7308_ = (!lean_is_exclusive(v___x_7287_)) as u8;
                    if v_isSharedCheck_7308_ == 0 {
                        v___x_7290_ = v___x_7287_;
                        v_isShared_7291_ = v_isSharedCheck_7308_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7288_);
                        lean_dec(v___x_7287_);
                        v___x_7290_ = lean_box(0);
                        v_isShared_7291_ = v_isSharedCheck_7308_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_7277_);
                    lean_dec(v_binderName_7276_);
                    v_a_7309_ = lean_ctor_get(v___x_7284_, 0);
                    v_isSharedCheck_7316_ = (!lean_is_exclusive(v___x_7284_)) as u8;
                    if v_isSharedCheck_7316_ == 0 {
                        v___x_7311_ = v___x_7284_;
                        v_isShared_7312_ = v_isSharedCheck_7316_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7309_);
                        lean_dec(v___x_7284_);
                        v___x_7311_ = lean_box(0);
                        v_isShared_7312_ = v_isSharedCheck_7316_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7292_ = lean_st_ref_take(v_a_7280_);
                v_lctx_7293_ = lean_ctor_get(v___x_7292_, 0);
                v_nextIdx_7294_ = lean_ctor_get(v___x_7292_, 1);
                v_isSharedCheck_7307_ = (!lean_is_exclusive(v___x_7292_)) as u8;
                if v_isSharedCheck_7307_ == 0 {
                    v___x_7296_ = v___x_7292_;
                    v_isShared_7297_ = v_isSharedCheck_7307_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7294_);
                    lean_inc(v_lctx_7293_);
                    lean_dec(v___x_7292_);
                    v___x_7296_ = lean_box(0);
                    v_isShared_7297_ = v_isSharedCheck_7307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7298_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_7298_, 0, v_a_7285_);
                lean_ctor_set(v___x_7298_, 1, v_a_7288_);
                lean_ctor_set(v___x_7298_, 2, v_type_7277_);
                lean_ctor_set_uint8(
                    v___x_7298_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_borrow_7278_,
                );
                lean_inc_ref(v___x_7298_);
                v___x_7299_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7275_, v_lctx_7293_, v___x_7298_);
                if v_isShared_7297_ == 0 {
                    lean_ctor_set(v___x_7296_, 0, v___x_7299_);
                    v___x_7301_ = v___x_7296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7306_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7306_, 0, v___x_7299_);
                    lean_ctor_set(v_reuseFailAlloc_7306_, 1, v_nextIdx_7294_);
                    v___x_7301_ = v_reuseFailAlloc_7306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7302_ = lean_st_ref_set(v_a_7280_, v___x_7301_);
                if v_isShared_7291_ == 0 {
                    lean_ctor_set(v___x_7290_, 0, v___x_7298_);
                    v___x_7304_ = v___x_7290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7305_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7305_, 0, v___x_7298_);
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
                    v_reuseFailAlloc_7315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7315_, 0, v_a_7309_);
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
    mut v_pu_7317_: *mut LeanObject,
    mut v_binderName_7318_: *mut LeanObject,
    mut v_type_7319_: *mut LeanObject,
    mut v_borrow_7320_: *mut LeanObject,
    mut v_a_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
    mut v_a_7323_: *mut LeanObject,
    mut v_a_7324_: *mut LeanObject,
    mut v_a_7325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7326_: u8 = 0;
    let mut v_borrow_boxed_7327_: u8 = 0;
    let mut v_res_7328_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7326_ = (lean_unbox(v_pu_7317_) as u8);
    v_borrow_boxed_7327_ = (lean_unbox(v_borrow_7320_) as u8);
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
    lean_dec(v_a_7324_);
    lean_dec_ref(v_a_7323_);
    lean_dec(v_a_7322_);
    lean_dec_ref(v_a_7321_);
    return v_res_7328_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(
    mut v___y_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
    mut v___y_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    v___x_7334_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___redArg(v___y_7332_);
    return v___x_7334_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0___boxed(
    mut v___y_7335_: *mut LeanObject,
    mut v___y_7336_: *mut LeanObject,
    mut v___y_7337_: *mut LeanObject,
    mut v___y_7338_: *mut LeanObject,
    mut v___y_7339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7340_: *mut LeanObject = core::ptr::null_mut();
    v_res_7340_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0_spec__0(v___y_7335_, v___y_7336_, v___y_7337_, v___y_7338_);
    lean_dec(v___y_7338_);
    lean_dec_ref(v___y_7337_);
    lean_dec(v___y_7336_);
    lean_dec_ref(v___y_7335_);
    return v_res_7340_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDecl(
    mut v_pu_7344_: u8,
    mut v_binderName_7345_: *mut LeanObject,
    mut v_type_7346_: *mut LeanObject,
    mut v_value_7347_: *mut LeanObject,
    mut v_a_7348_: *mut LeanObject,
    mut v_a_7349_: *mut LeanObject,
    mut v_a_7350_: *mut LeanObject,
    mut v_a_7351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7360_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7366_: u8 = 0;
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7376_: u8 = 0;
    let mut v_isSharedCheck_7377_: u8 = 0;
    let mut v_a_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7381_: u8 = 0;
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7353_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7348_, v_a_7349_, v_a_7350_, v_a_7351_,
                );
                if lean_obj_tag(v___x_7353_) == 0 {
                    v_a_7354_ = lean_ctor_get(v___x_7353_, 0);
                    lean_inc(v_a_7354_);
                    lean_dec_ref_known(v___x_7353_, 1);
                    v___x_7355_ = l_Lean_Compiler_LCNF_mkLetDecl___closed__1;
                    v___x_7356_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7345_,
                        v___x_7355_,
                        v_a_7349_,
                    );
                    v_a_7357_ = lean_ctor_get(v___x_7356_, 0);
                    v_isSharedCheck_7377_ = (!lean_is_exclusive(v___x_7356_)) as u8;
                    if v_isSharedCheck_7377_ == 0 {
                        v___x_7359_ = v___x_7356_;
                        v_isShared_7360_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7357_);
                        lean_dec(v___x_7356_);
                        v___x_7359_ = lean_box(0);
                        v_isShared_7360_ = v_isSharedCheck_7377_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_value_7347_);
                    lean_dec_ref(v_type_7346_);
                    lean_dec(v_binderName_7345_);
                    v_a_7378_ = lean_ctor_get(v___x_7353_, 0);
                    v_isSharedCheck_7385_ = (!lean_is_exclusive(v___x_7353_)) as u8;
                    if v_isSharedCheck_7385_ == 0 {
                        v___x_7380_ = v___x_7353_;
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7378_);
                        lean_dec(v___x_7353_);
                        v___x_7380_ = lean_box(0);
                        v_isShared_7381_ = v_isSharedCheck_7385_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7361_ = lean_st_ref_take(v_a_7349_);
                v_lctx_7362_ = lean_ctor_get(v___x_7361_, 0);
                v_nextIdx_7363_ = lean_ctor_get(v___x_7361_, 1);
                v_isSharedCheck_7376_ = (!lean_is_exclusive(v___x_7361_)) as u8;
                if v_isSharedCheck_7376_ == 0 {
                    v___x_7365_ = v___x_7361_;
                    v_isShared_7366_ = v_isSharedCheck_7376_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7363_);
                    lean_inc(v_lctx_7362_);
                    lean_dec(v___x_7361_);
                    v___x_7365_ = lean_box(0);
                    v_isShared_7366_ = v_isSharedCheck_7376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7367_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_7367_, 0, v_a_7354_);
                lean_ctor_set(v___x_7367_, 1, v_a_7357_);
                lean_ctor_set(v___x_7367_, 2, v_type_7346_);
                lean_ctor_set(v___x_7367_, 3, v_value_7347_);
                lean_inc_ref(v___x_7367_);
                v___x_7368_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_7344_, v_lctx_7362_, v___x_7367_);
                if v_isShared_7366_ == 0 {
                    lean_ctor_set(v___x_7365_, 0, v___x_7368_);
                    v___x_7370_ = v___x_7365_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7375_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7375_, 0, v___x_7368_);
                    lean_ctor_set(v_reuseFailAlloc_7375_, 1, v_nextIdx_7363_);
                    v___x_7370_ = v_reuseFailAlloc_7375_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7371_ = lean_st_ref_set(v_a_7349_, v___x_7370_);
                if v_isShared_7360_ == 0 {
                    lean_ctor_set(v___x_7359_, 0, v___x_7367_);
                    v___x_7373_ = v___x_7359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7374_, 0, v___x_7367_);
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
                    v_reuseFailAlloc_7384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7384_, 0, v_a_7378_);
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
    mut v_pu_7386_: *mut LeanObject,
    mut v_binderName_7387_: *mut LeanObject,
    mut v_type_7388_: *mut LeanObject,
    mut v_value_7389_: *mut LeanObject,
    mut v_a_7390_: *mut LeanObject,
    mut v_a_7391_: *mut LeanObject,
    mut v_a_7392_: *mut LeanObject,
    mut v_a_7393_: *mut LeanObject,
    mut v_a_7394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7395_: u8 = 0;
    let mut v_res_7396_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7395_ = (lean_unbox(v_pu_7386_) as u8);
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
    lean_dec(v_a_7393_);
    lean_dec_ref(v_a_7392_);
    lean_dec(v_a_7391_);
    lean_dec_ref(v_a_7390_);
    return v_res_7396_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFunDecl(
    mut v_pu_7400_: u8,
    mut v_binderName_7401_: *mut LeanObject,
    mut v_type_7402_: *mut LeanObject,
    mut v_params_7403_: *mut LeanObject,
    mut v_value_7404_: *mut LeanObject,
    mut v_a_7405_: *mut LeanObject,
    mut v_a_7406_: *mut LeanObject,
    mut v_a_7407_: *mut LeanObject,
    mut v_a_7408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7417_: u8 = 0;
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7423_: u8 = 0;
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7433_: u8 = 0;
    let mut v_isSharedCheck_7434_: u8 = 0;
    let mut v_a_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v___x_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7410_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_mkParam_spec__0(
                    v_a_7405_, v_a_7406_, v_a_7407_, v_a_7408_,
                );
                if lean_obj_tag(v___x_7410_) == 0 {
                    v_a_7411_ = lean_ctor_get(v___x_7410_, 0);
                    lean_inc(v_a_7411_);
                    lean_dec_ref_known(v___x_7410_, 1);
                    v___x_7412_ = l_Lean_Compiler_LCNF_mkFunDecl___closed__1;
                    v___x_7413_ = l_Lean_Compiler_LCNF_ensureNotAnonymous___redArg(
                        v_binderName_7401_,
                        v___x_7412_,
                        v_a_7406_,
                    );
                    v_a_7414_ = lean_ctor_get(v___x_7413_, 0);
                    v_isSharedCheck_7434_ = (!lean_is_exclusive(v___x_7413_)) as u8;
                    if v_isSharedCheck_7434_ == 0 {
                        v___x_7416_ = v___x_7413_;
                        v_isShared_7417_ = v_isSharedCheck_7434_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7414_);
                        lean_dec(v___x_7413_);
                        v___x_7416_ = lean_box(0);
                        v_isShared_7417_ = v_isSharedCheck_7434_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_7404_);
                    lean_dec_ref(v_params_7403_);
                    lean_dec_ref(v_type_7402_);
                    lean_dec(v_binderName_7401_);
                    v_a_7435_ = lean_ctor_get(v___x_7410_, 0);
                    v_isSharedCheck_7442_ = (!lean_is_exclusive(v___x_7410_)) as u8;
                    if v_isSharedCheck_7442_ == 0 {
                        v___x_7437_ = v___x_7410_;
                        v_isShared_7438_ = v_isSharedCheck_7442_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_7435_);
                        lean_dec(v___x_7410_);
                        v___x_7437_ = lean_box(0);
                        v_isShared_7438_ = v_isSharedCheck_7442_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7418_ = lean_st_ref_take(v_a_7406_);
                v_lctx_7419_ = lean_ctor_get(v___x_7418_, 0);
                v_nextIdx_7420_ = lean_ctor_get(v___x_7418_, 1);
                v_isSharedCheck_7433_ = (!lean_is_exclusive(v___x_7418_)) as u8;
                if v_isSharedCheck_7433_ == 0 {
                    v___x_7422_ = v___x_7418_;
                    v_isShared_7423_ = v_isSharedCheck_7433_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7420_);
                    lean_inc(v_lctx_7419_);
                    lean_dec(v___x_7418_);
                    v___x_7422_ = lean_box(0);
                    v_isShared_7423_ = v_isSharedCheck_7433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7424_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_7424_, 0, v_a_7411_);
                lean_ctor_set(v___x_7424_, 1, v_a_7414_);
                lean_ctor_set(v___x_7424_, 2, v_params_7403_);
                lean_ctor_set(v___x_7424_, 3, v_type_7402_);
                lean_ctor_set(v___x_7424_, 4, v_value_7404_);
                lean_inc_ref(v___x_7424_);
                v___x_7425_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_7400_, v_lctx_7419_, v___x_7424_);
                if v_isShared_7423_ == 0 {
                    lean_ctor_set(v___x_7422_, 0, v___x_7425_);
                    v___x_7427_ = v___x_7422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7432_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7432_, 0, v___x_7425_);
                    lean_ctor_set(v_reuseFailAlloc_7432_, 1, v_nextIdx_7420_);
                    v___x_7427_ = v_reuseFailAlloc_7432_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7428_ = lean_st_ref_set(v_a_7406_, v___x_7427_);
                if v_isShared_7417_ == 0 {
                    lean_ctor_set(v___x_7416_, 0, v___x_7424_);
                    v___x_7430_ = v___x_7416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7431_, 0, v___x_7424_);
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
                    v_reuseFailAlloc_7441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7441_, 0, v_a_7435_);
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
    mut v_pu_7443_: *mut LeanObject,
    mut v_binderName_7444_: *mut LeanObject,
    mut v_type_7445_: *mut LeanObject,
    mut v_params_7446_: *mut LeanObject,
    mut v_value_7447_: *mut LeanObject,
    mut v_a_7448_: *mut LeanObject,
    mut v_a_7449_: *mut LeanObject,
    mut v_a_7450_: *mut LeanObject,
    mut v_a_7451_: *mut LeanObject,
    mut v_a_7452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7453_ = (lean_unbox(v_pu_7443_) as u8);
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
    lean_dec(v_a_7451_);
    lean_dec_ref(v_a_7450_);
    lean_dec(v_a_7449_);
    lean_dec_ref(v_a_7448_);
    return v_res_7454_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkLetDeclErased(
    mut v_pu_7455_: u8,
    mut v_a_7456_: *mut LeanObject,
    mut v_a_7457_: *mut LeanObject,
    mut v_a_7458_: *mut LeanObject,
    mut v_a_7459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    v___x_7461_ = l_Lean_Compiler_LCNF_mkLetDecl___closed__1;
    v___x_7462_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_7461_, v_a_7457_);
    v_a_7463_ = lean_ctor_get(v___x_7462_, 0);
    lean_inc(v_a_7463_);
    lean_dec_ref(v___x_7462_);
    v___x_7464_ = l_Lean_Compiler_LCNF_erasedExpr;
    v___x_7465_ = lean_box(1);
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
    mut v_pu_7467_: *mut LeanObject,
    mut v_a_7468_: *mut LeanObject,
    mut v_a_7469_: *mut LeanObject,
    mut v_a_7470_: *mut LeanObject,
    mut v_a_7471_: *mut LeanObject,
    mut v_a_7472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7473_: u8 = 0;
    let mut v_res_7474_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7473_ = (lean_unbox(v_pu_7467_) as u8);
    v_res_7474_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
        v_pu_boxed_7473_,
        v_a_7468_,
        v_a_7469_,
        v_a_7470_,
        v_a_7471_,
    );
    lean_dec(v_a_7471_);
    lean_dec_ref(v_a_7470_);
    lean_dec(v_a_7469_);
    lean_dec_ref(v_a_7468_);
    return v_res_7474_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkReturnErased(
    mut v_pu_7475_: u8,
    mut v_a_7476_: *mut LeanObject,
    mut v_a_7477_: *mut LeanObject,
    mut v_a_7478_: *mut LeanObject,
    mut v_a_7479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7485_: u8 = 0;
    let mut v_fvarId_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7492_: u8 = 0;
    let mut v_a_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7496_: u8 = 0;
    let mut v___x_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7481_ = l_Lean_Compiler_LCNF_mkLetDeclErased(
                    v_pu_7475_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_,
                );
                if lean_obj_tag(v___x_7481_) == 0 {
                    v_a_7482_ = lean_ctor_get(v___x_7481_, 0);
                    v_isSharedCheck_7492_ = (!lean_is_exclusive(v___x_7481_)) as u8;
                    if v_isSharedCheck_7492_ == 0 {
                        v___x_7484_ = v___x_7481_;
                        v_isShared_7485_ = v_isSharedCheck_7492_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7482_);
                        lean_dec(v___x_7481_);
                        v___x_7484_ = lean_box(0);
                        v_isShared_7485_ = v_isSharedCheck_7492_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7493_ = lean_ctor_get(v___x_7481_, 0);
                    v_isSharedCheck_7500_ = (!lean_is_exclusive(v___x_7481_)) as u8;
                    if v_isSharedCheck_7500_ == 0 {
                        v___x_7495_ = v___x_7481_;
                        v_isShared_7496_ = v_isSharedCheck_7500_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7493_);
                        lean_dec(v___x_7481_);
                        v___x_7495_ = lean_box(0);
                        v_isShared_7496_ = v_isSharedCheck_7500_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_7486_ = lean_ctor_get(v_a_7482_, 0);
                lean_inc(v_fvarId_7486_);
                v___x_7487_ = lean_alloc_ctor(5, 1, (0) as u32);
                lean_ctor_set(v___x_7487_, 0, v_fvarId_7486_);
                v___x_7488_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7488_, 0, v_a_7482_);
                lean_ctor_set(v___x_7488_, 1, v___x_7487_);
                if v_isShared_7485_ == 0 {
                    lean_ctor_set(v___x_7484_, 0, v___x_7488_);
                    v___x_7490_ = v___x_7484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7491_, 0, v___x_7488_);
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
                    v_reuseFailAlloc_7499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7499_, 0, v_a_7493_);
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
    mut v_pu_7501_: *mut LeanObject,
    mut v_a_7502_: *mut LeanObject,
    mut v_a_7503_: *mut LeanObject,
    mut v_a_7504_: *mut LeanObject,
    mut v_a_7505_: *mut LeanObject,
    mut v_a_7506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7507_: u8 = 0;
    let mut v_res_7508_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7507_ = (lean_unbox(v_pu_7501_) as u8);
    v_res_7508_ = l_Lean_Compiler_LCNF_mkReturnErased(
        v_pu_boxed_7507_,
        v_a_7502_,
        v_a_7503_,
        v_a_7504_,
        v_a_7505_,
    );
    lean_dec(v_a_7505_);
    lean_dec_ref(v_a_7504_);
    lean_dec(v_a_7503_);
    lean_dec_ref(v_a_7502_);
    return v_res_7508_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(
    mut v_pu_7509_: u8,
    mut v_p_7510_: *mut LeanObject,
    mut v_type_7511_: *mut LeanObject,
    mut v_a_7512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_7517_: u8 = 0;
    let mut v___x_7518_: usize = 0;
    let mut v___x_7519_: usize = 0;
    let mut v___x_7520_: u8 = 0;
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7523_: u8 = 0;
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7529_: u8 = 0;
    let mut v_p_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7539_: u8 = 0;
    let mut v_isSharedCheck_7540_: u8 = 0;
    let mut v_unused_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7514_ = lean_ctor_get(v_p_7510_, 0);
                v_binderName_7515_ = lean_ctor_get(v_p_7510_, 1);
                v_type_7516_ = lean_ctor_get(v_p_7510_, 2);
                v_borrow_7517_ = lean_ctor_get_uint8(
                    v_p_7510_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v___x_7518_ = lean_ptr_addr(v_type_7511_);
                v___x_7519_ = lean_ptr_addr(v_type_7516_);
                v___x_7520_ = lean_usize_dec_eq(v___x_7518_, v___x_7519_);
                if v___x_7520_ == 0 {
                    lean_inc(v_binderName_7515_);
                    lean_inc(v_fvarId_7514_);
                    v_isSharedCheck_7540_ = (!lean_is_exclusive(v_p_7510_)) as u8;
                    if v_isSharedCheck_7540_ == 0 {
                        v_unused_7541_ = lean_ctor_get(v_p_7510_, 2);
                        lean_dec(v_unused_7541_);
                        v_unused_7542_ = lean_ctor_get(v_p_7510_, 1);
                        lean_dec(v_unused_7542_);
                        v_unused_7543_ = lean_ctor_get(v_p_7510_, 0);
                        lean_dec(v_unused_7543_);
                        v___x_7522_ = v_p_7510_;
                        v_isShared_7523_ = v_isSharedCheck_7540_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_p_7510_);
                        v___x_7522_ = lean_box(0);
                        v_isShared_7523_ = v_isSharedCheck_7540_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_7511_);
                    v___x_7544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7544_, 0, v_p_7510_);
                    return v___x_7544_;
                }
            }
            1 => {
                v___x_7524_ = lean_st_ref_take(v_a_7512_);
                v_lctx_7525_ = lean_ctor_get(v___x_7524_, 0);
                v_nextIdx_7526_ = lean_ctor_get(v___x_7524_, 1);
                v_isSharedCheck_7539_ = (!lean_is_exclusive(v___x_7524_)) as u8;
                if v_isSharedCheck_7539_ == 0 {
                    v___x_7528_ = v___x_7524_;
                    v_isShared_7529_ = v_isSharedCheck_7539_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7526_);
                    lean_inc(v_lctx_7525_);
                    lean_dec(v___x_7524_);
                    v___x_7528_ = lean_box(0);
                    v_isShared_7529_ = v_isSharedCheck_7539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_7523_ == 0 {
                    lean_ctor_set(v___x_7522_, 2, v_type_7511_);
                    v_p_7531_ = v___x_7522_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7538_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7538_, 0, v_fvarId_7514_);
                    lean_ctor_set(v_reuseFailAlloc_7538_, 1, v_binderName_7515_);
                    lean_ctor_set(v_reuseFailAlloc_7538_, 2, v_type_7511_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7538_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_borrow_7517_,
                    );
                    v_p_7531_ = v_reuseFailAlloc_7538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_p_7531_);
                v___x_7532_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7509_, v_lctx_7525_, v_p_7531_);
                if v_isShared_7529_ == 0 {
                    lean_ctor_set(v___x_7528_, 0, v___x_7532_);
                    v___x_7534_ = v___x_7528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7537_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7537_, 0, v___x_7532_);
                    lean_ctor_set(v_reuseFailAlloc_7537_, 1, v_nextIdx_7526_);
                    v___x_7534_ = v_reuseFailAlloc_7537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7535_ = lean_st_ref_set(v_a_7512_, v___x_7534_);
                v___x_7536_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7536_, 0, v_p_7531_);
                return v___x_7536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg___boxed(
    mut v_pu_7545_: *mut LeanObject,
    mut v_p_7546_: *mut LeanObject,
    mut v_type_7547_: *mut LeanObject,
    mut v_a_7548_: *mut LeanObject,
    mut v_a_7549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7550_: u8 = 0;
    let mut v_res_7551_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7550_ = (lean_unbox(v_pu_7545_) as u8);
    v_res_7551_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(
            v_pu_boxed_7550_,
            v_p_7546_,
            v_type_7547_,
            v_a_7548_,
        );
    lean_dec(v_a_7548_);
    return v_res_7551_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(
    mut v_pu_7552_: u8,
    mut v_p_7553_: *mut LeanObject,
    mut v_type_7554_: *mut LeanObject,
    mut v_a_7555_: *mut LeanObject,
    mut v_a_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
    mut v_a_7558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_7561_: *mut LeanObject,
    mut v_p_7562_: *mut LeanObject,
    mut v_type_7563_: *mut LeanObject,
    mut v_a_7564_: *mut LeanObject,
    mut v_a_7565_: *mut LeanObject,
    mut v_a_7566_: *mut LeanObject,
    mut v_a_7567_: *mut LeanObject,
    mut v_a_7568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7569_: u8 = 0;
    let mut v_res_7570_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7569_ = (lean_unbox(v_pu_7561_) as u8);
    v_res_7570_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(
        v_pu_boxed_7569_,
        v_p_7562_,
        v_type_7563_,
        v_a_7564_,
        v_a_7565_,
        v_a_7566_,
        v_a_7567_,
    );
    lean_dec(v_a_7567_);
    lean_dec_ref(v_a_7566_);
    lean_dec(v_a_7565_);
    lean_dec_ref(v_a_7564_);
    return v_res_7570_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(
    mut v_pu_7571_: u8,
    mut v_p_7572_: *mut LeanObject,
    mut v_borrow_7573_: u8,
    mut v_a_7574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_7579_: u8 = 0;
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7586_: u8 = 0;
    let mut v_p_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7594_: u8 = 0;
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_7576_ = lean_ctor_get(v_p_7572_, 0);
                v_binderName_7577_ = lean_ctor_get(v_p_7572_, 1);
                v_type_7578_ = lean_ctor_get(v_p_7572_, 2);
                v_borrow_7579_ = lean_ctor_get_uint8(
                    v_p_7572_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_borrow_7573_ == 0 {
                    if v_borrow_7579_ == 0 {
                        v___x_7595_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7595_, 0, v_p_7572_);
                        return v___x_7595_;
                    } else {
                        lean_inc_ref(v_type_7578_);
                        lean_inc(v_binderName_7577_);
                        lean_inc(v_fvarId_7576_);
                        lean_dec_ref(v_p_7572_);
                        state = 1;
                        continue;
                    }
                } else {
                    if v_borrow_7579_ == 0 {
                        lean_inc_ref(v_type_7578_);
                        lean_inc(v_binderName_7577_);
                        lean_inc(v_fvarId_7576_);
                        lean_dec_ref(v_p_7572_);
                        state = 1;
                        continue;
                    } else {
                        v___x_7596_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7596_, 0, v_p_7572_);
                        return v___x_7596_;
                    }
                }
            }
            1 => {
                v___x_7581_ = lean_st_ref_take(v_a_7574_);
                v_lctx_7582_ = lean_ctor_get(v___x_7581_, 0);
                v_nextIdx_7583_ = lean_ctor_get(v___x_7581_, 1);
                v_isSharedCheck_7594_ = (!lean_is_exclusive(v___x_7581_)) as u8;
                if v_isSharedCheck_7594_ == 0 {
                    v___x_7585_ = v___x_7581_;
                    v_isShared_7586_ = v_isSharedCheck_7594_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7583_);
                    lean_inc(v_lctx_7582_);
                    lean_dec(v___x_7581_);
                    v___x_7585_ = lean_box(0);
                    v_isShared_7586_ = v_isSharedCheck_7594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_p_7587_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v_p_7587_, 0, v_fvarId_7576_);
                lean_ctor_set(v_p_7587_, 1, v_binderName_7577_);
                lean_ctor_set(v_p_7587_, 2, v_type_7578_);
                lean_ctor_set_uint8(
                    v_p_7587_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_borrow_7573_,
                );
                lean_inc_ref(v_p_7587_);
                v___x_7588_ =
                    l_Lean_Compiler_LCNF_LCtx_addParam(v_pu_7571_, v_lctx_7582_, v_p_7587_);
                if v_isShared_7586_ == 0 {
                    lean_ctor_set(v___x_7585_, 0, v___x_7588_);
                    v___x_7590_ = v___x_7585_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7593_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7593_, 0, v___x_7588_);
                    lean_ctor_set(v_reuseFailAlloc_7593_, 1, v_nextIdx_7583_);
                    v___x_7590_ = v_reuseFailAlloc_7593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7591_ = lean_st_ref_set(v_a_7574_, v___x_7590_);
                v___x_7592_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7592_, 0, v_p_7587_);
                return v___x_7592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg___boxed(
    mut v_pu_7597_: *mut LeanObject,
    mut v_p_7598_: *mut LeanObject,
    mut v_borrow_7599_: *mut LeanObject,
    mut v_a_7600_: *mut LeanObject,
    mut v_a_7601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7602_: u8 = 0;
    let mut v_borrow_boxed_7603_: u8 = 0;
    let mut v_res_7604_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7602_ = (lean_unbox(v_pu_7597_) as u8);
    v_borrow_boxed_7603_ = (lean_unbox(v_borrow_7599_) as u8);
    v_res_7604_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_boxed_7602_, v_p_7598_, v_borrow_boxed_7603_, v_a_7600_);
    lean_dec(v_a_7600_);
    return v_res_7604_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp(
    mut v_pu_7605_: u8,
    mut v_p_7606_: *mut LeanObject,
    mut v_borrow_7607_: u8,
    mut v_a_7608_: *mut LeanObject,
    mut v_a_7609_: *mut LeanObject,
    mut v_a_7610_: *mut LeanObject,
    mut v_a_7611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    v___x_7613_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v_pu_7605_, v_p_7606_, v_borrow_7607_, v_a_7609_);
    return v___x_7613_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___boxed(
    mut v_pu_7614_: *mut LeanObject,
    mut v_p_7615_: *mut LeanObject,
    mut v_borrow_7616_: *mut LeanObject,
    mut v_a_7617_: *mut LeanObject,
    mut v_a_7618_: *mut LeanObject,
    mut v_a_7619_: *mut LeanObject,
    mut v_a_7620_: *mut LeanObject,
    mut v_a_7621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7622_: u8 = 0;
    let mut v_borrow_boxed_7623_: u8 = 0;
    let mut v_res_7624_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7622_ = (lean_unbox(v_pu_7614_) as u8);
    v_borrow_boxed_7623_ = (lean_unbox(v_borrow_7616_) as u8);
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
    lean_dec(v_a_7620_);
    lean_dec_ref(v_a_7619_);
    lean_dec(v_a_7618_);
    lean_dec_ref(v_a_7617_);
    return v_res_7624_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
    mut v_pu_7625_: u8,
    mut v_decl_7626_: *mut LeanObject,
    mut v_type_7627_: *mut LeanObject,
    mut v_value_7628_: *mut LeanObject,
    mut v_a_7629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7636_: u8 = 0;
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7639_: u8 = 0;
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7645_: u8 = 0;
    let mut v_decl_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7655_: u8 = 0;
    let mut v_isSharedCheck_7656_: u8 = 0;
    let mut v_unused_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
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
                v_fvarId_7631_ = lean_ctor_get(v_decl_7626_, 0);
                v_binderName_7632_ = lean_ctor_get(v_decl_7626_, 1);
                v_type_7633_ = lean_ctor_get(v_decl_7626_, 2);
                v_value_7634_ = lean_ctor_get(v_decl_7626_, 3);
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
                    lean_inc(v_binderName_7632_);
                    lean_inc(v_fvarId_7631_);
                    v_isSharedCheck_7656_ = (!lean_is_exclusive(v_decl_7626_)) as u8;
                    if v_isSharedCheck_7656_ == 0 {
                        v_unused_7657_ = lean_ctor_get(v_decl_7626_, 3);
                        lean_dec(v_unused_7657_);
                        v_unused_7658_ = lean_ctor_get(v_decl_7626_, 2);
                        lean_dec(v_unused_7658_);
                        v_unused_7659_ = lean_ctor_get(v_decl_7626_, 1);
                        lean_dec(v_unused_7659_);
                        v_unused_7660_ = lean_ctor_get(v_decl_7626_, 0);
                        lean_dec(v_unused_7660_);
                        v___x_7638_ = v_decl_7626_;
                        v_isShared_7639_ = v_isSharedCheck_7656_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_decl_7626_);
                        v___x_7638_ = lean_box(0);
                        v_isShared_7639_ = v_isSharedCheck_7656_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_7628_);
                    lean_dec_ref(v_type_7627_);
                    v___x_7661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7661_, 0, v_decl_7626_);
                    return v___x_7661_;
                }
            }
            2 => {
                v___x_7640_ = lean_st_ref_take(v_a_7629_);
                v_lctx_7641_ = lean_ctor_get(v___x_7640_, 0);
                v_nextIdx_7642_ = lean_ctor_get(v___x_7640_, 1);
                v_isSharedCheck_7655_ = (!lean_is_exclusive(v___x_7640_)) as u8;
                if v_isSharedCheck_7655_ == 0 {
                    v___x_7644_ = v___x_7640_;
                    v_isShared_7645_ = v_isSharedCheck_7655_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7642_);
                    lean_inc(v_lctx_7641_);
                    lean_dec(v___x_7640_);
                    v___x_7644_ = lean_box(0);
                    v_isShared_7645_ = v_isSharedCheck_7655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7639_ == 0 {
                    lean_ctor_set(v___x_7638_, 3, v_value_7628_);
                    lean_ctor_set(v___x_7638_, 2, v_type_7627_);
                    v_decl_7647_ = v___x_7638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7654_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7654_, 0, v_fvarId_7631_);
                    lean_ctor_set(v_reuseFailAlloc_7654_, 1, v_binderName_7632_);
                    lean_ctor_set(v_reuseFailAlloc_7654_, 2, v_type_7627_);
                    lean_ctor_set(v_reuseFailAlloc_7654_, 3, v_value_7628_);
                    v_decl_7647_ = v_reuseFailAlloc_7654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_decl_7647_);
                v___x_7648_ =
                    l_Lean_Compiler_LCNF_LCtx_addLetDecl(v_pu_7625_, v_lctx_7641_, v_decl_7647_);
                if v_isShared_7645_ == 0 {
                    lean_ctor_set(v___x_7644_, 0, v___x_7648_);
                    v___x_7650_ = v___x_7644_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7653_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 0, v___x_7648_);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 1, v_nextIdx_7642_);
                    v___x_7650_ = v_reuseFailAlloc_7653_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7651_ = lean_st_ref_set(v_a_7629_, v___x_7650_);
                v___x_7652_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7652_, 0, v_decl_7647_);
                return v___x_7652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg___boxed(
    mut v_pu_7668_: *mut LeanObject,
    mut v_decl_7669_: *mut LeanObject,
    mut v_type_7670_: *mut LeanObject,
    mut v_value_7671_: *mut LeanObject,
    mut v_a_7672_: *mut LeanObject,
    mut v_a_7673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7674_ = (lean_unbox(v_pu_7668_) as u8);
    v_res_7675_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_boxed_7674_,
            v_decl_7669_,
            v_type_7670_,
            v_value_7671_,
            v_a_7672_,
        );
    lean_dec(v_a_7672_);
    return v_res_7675_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(
    mut v_pu_7676_: u8,
    mut v_decl_7677_: *mut LeanObject,
    mut v_type_7678_: *mut LeanObject,
    mut v_value_7679_: *mut LeanObject,
    mut v_a_7680_: *mut LeanObject,
    mut v_a_7681_: *mut LeanObject,
    mut v_a_7682_: *mut LeanObject,
    mut v_a_7683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_7686_: *mut LeanObject,
    mut v_decl_7687_: *mut LeanObject,
    mut v_type_7688_: *mut LeanObject,
    mut v_value_7689_: *mut LeanObject,
    mut v_a_7690_: *mut LeanObject,
    mut v_a_7691_: *mut LeanObject,
    mut v_a_7692_: *mut LeanObject,
    mut v_a_7693_: *mut LeanObject,
    mut v_a_7694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7695_: u8 = 0;
    let mut v_res_7696_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7695_ = (lean_unbox(v_pu_7686_) as u8);
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
    lean_dec(v_a_7693_);
    lean_dec_ref(v_a_7692_);
    lean_dec(v_a_7691_);
    lean_dec_ref(v_a_7690_);
    return v_res_7696_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
    mut v_pu_7697_: u8,
    mut v_decl_7698_: *mut LeanObject,
    mut v_value_7699_: *mut LeanObject,
    mut v_a_7700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    v_type_7702_ = lean_ctor_get(v_decl_7698_, 2);
    lean_inc_ref(v_type_7702_);
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
    mut v_pu_7704_: *mut LeanObject,
    mut v_decl_7705_: *mut LeanObject,
    mut v_value_7706_: *mut LeanObject,
    mut v_a_7707_: *mut LeanObject,
    mut v_a_7708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7709_: u8 = 0;
    let mut v_res_7710_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7709_ = (lean_unbox(v_pu_7704_) as u8);
    v_res_7710_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
        v_pu_boxed_7709_,
        v_decl_7705_,
        v_value_7706_,
        v_a_7707_,
    );
    lean_dec(v_a_7707_);
    return v_res_7710_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue(
    mut v_pu_7711_: u8,
    mut v_decl_7712_: *mut LeanObject,
    mut v_value_7713_: *mut LeanObject,
    mut v_a_7714_: *mut LeanObject,
    mut v_a_7715_: *mut LeanObject,
    mut v_a_7716_: *mut LeanObject,
    mut v_a_7717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    v___x_7719_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
        v_pu_7711_,
        v_decl_7712_,
        v_value_7713_,
        v_a_7715_,
    );
    return v___x_7719_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_updateValue___boxed(
    mut v_pu_7720_: *mut LeanObject,
    mut v_decl_7721_: *mut LeanObject,
    mut v_value_7722_: *mut LeanObject,
    mut v_a_7723_: *mut LeanObject,
    mut v_a_7724_: *mut LeanObject,
    mut v_a_7725_: *mut LeanObject,
    mut v_a_7726_: *mut LeanObject,
    mut v_a_7727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7728_: u8 = 0;
    let mut v_res_7729_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7728_ = (lean_unbox(v_pu_7720_) as u8);
    v_res_7729_ = l_Lean_Compiler_LCNF_LetDecl_updateValue(
        v_pu_boxed_7728_,
        v_decl_7721_,
        v_value_7722_,
        v_a_7723_,
        v_a_7724_,
        v_a_7725_,
        v_a_7726_,
    );
    lean_dec(v_a_7726_);
    lean_dec_ref(v_a_7725_);
    lean_dec(v_a_7724_);
    lean_dec_ref(v_a_7723_);
    return v_res_7729_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
    mut v_pu_7730_: u8,
    mut v_decl_7731_: *mut LeanObject,
    mut v_type_7732_: *mut LeanObject,
    mut v_params_7733_: *mut LeanObject,
    mut v_value_7734_: *mut LeanObject,
    mut v_a_7735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_7738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_7739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7748_: u8 = 0;
    let mut v_decl_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7756_: u8 = 0;
    let mut v___y_7758_: u8 = 0;
    let mut v___x_7759_: usize = 0;
    let mut v___x_7760_: usize = 0;
    let mut v___x_7761_: u8 = 0;
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
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
                v_fvarId_7737_ = lean_ctor_get(v_decl_7731_, 0);
                v_binderName_7738_ = lean_ctor_get(v_decl_7731_, 1);
                v_params_7739_ = lean_ctor_get(v_decl_7731_, 2);
                v_type_7740_ = lean_ctor_get(v_decl_7731_, 3);
                v_value_7741_ = lean_ctor_get(v_decl_7731_, 4);
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
                v_lctx_7744_ = lean_ctor_get(v___x_7743_, 0);
                v_nextIdx_7745_ = lean_ctor_get(v___x_7743_, 1);
                v_isSharedCheck_7756_ = (!lean_is_exclusive(v___x_7743_)) as u8;
                if v_isSharedCheck_7756_ == 0 {
                    v___x_7747_ = v___x_7743_;
                    v_isShared_7748_ = v_isSharedCheck_7756_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nextIdx_7745_);
                    lean_inc(v_lctx_7744_);
                    lean_dec(v___x_7743_);
                    v___x_7747_ = lean_box(0);
                    v_isShared_7748_ = v_isSharedCheck_7756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_decl_7749_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v_decl_7749_, 0, v_fvarId_7737_);
                lean_ctor_set(v_decl_7749_, 1, v_binderName_7738_);
                lean_ctor_set(v_decl_7749_, 2, v_params_7733_);
                lean_ctor_set(v_decl_7749_, 3, v_type_7732_);
                lean_ctor_set(v_decl_7749_, 4, v_value_7734_);
                lean_inc_ref(v_decl_7749_);
                v___x_7750_ =
                    l_Lean_Compiler_LCNF_LCtx_addFunDecl(v_pu_7730_, v_lctx_7744_, v_decl_7749_);
                if v_isShared_7748_ == 0 {
                    lean_ctor_set(v___x_7747_, 0, v___x_7750_);
                    v___x_7752_ = v___x_7747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7755_, 0, v___x_7750_);
                    lean_ctor_set(v_reuseFailAlloc_7755_, 1, v_nextIdx_7745_);
                    v___x_7752_ = v_reuseFailAlloc_7755_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7753_ = lean_st_ref_set(v_a_7735_, v___x_7752_);
                v___x_7754_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7754_, 0, v_decl_7749_);
                return v___x_7754_;
            }
            4 => {
                if v___y_7758_ == 0 {
                    lean_inc(v_binderName_7738_);
                    lean_inc(v_fvarId_7737_);
                    lean_dec_ref(v_decl_7731_);
                    state = 1;
                    continue;
                } else {
                    v___x_7759_ = lean_ptr_addr(v_value_7734_);
                    v___x_7760_ = lean_ptr_addr(v_value_7741_);
                    v___x_7761_ = lean_usize_dec_eq(v___x_7759_, v___x_7760_);
                    if v___x_7761_ == 0 {
                        lean_inc(v_binderName_7738_);
                        lean_inc(v_fvarId_7737_);
                        lean_dec_ref(v_decl_7731_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_value_7734_);
                        lean_dec_ref(v_params_7733_);
                        lean_dec_ref(v_type_7732_);
                        v___x_7762_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7762_, 0, v_decl_7731_);
                        return v___x_7762_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg___boxed(
    mut v_pu_7769_: *mut LeanObject,
    mut v_decl_7770_: *mut LeanObject,
    mut v_type_7771_: *mut LeanObject,
    mut v_params_7772_: *mut LeanObject,
    mut v_value_7773_: *mut LeanObject,
    mut v_a_7774_: *mut LeanObject,
    mut v_a_7775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7776_: u8 = 0;
    let mut v_res_7777_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7776_ = (lean_unbox(v_pu_7769_) as u8);
    v_res_7777_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(
            v_pu_boxed_7776_,
            v_decl_7770_,
            v_type_7771_,
            v_params_7772_,
            v_value_7773_,
            v_a_7774_,
        );
    lean_dec(v_a_7774_);
    return v_res_7777_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(
    mut v_pu_7778_: u8,
    mut v_decl_7779_: *mut LeanObject,
    mut v_type_7780_: *mut LeanObject,
    mut v_params_7781_: *mut LeanObject,
    mut v_value_7782_: *mut LeanObject,
    mut v_a_7783_: *mut LeanObject,
    mut v_a_7784_: *mut LeanObject,
    mut v_a_7785_: *mut LeanObject,
    mut v_a_7786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_7789_: *mut LeanObject,
    mut v_decl_7790_: *mut LeanObject,
    mut v_type_7791_: *mut LeanObject,
    mut v_params_7792_: *mut LeanObject,
    mut v_value_7793_: *mut LeanObject,
    mut v_a_7794_: *mut LeanObject,
    mut v_a_7795_: *mut LeanObject,
    mut v_a_7796_: *mut LeanObject,
    mut v_a_7797_: *mut LeanObject,
    mut v_a_7798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7799_: u8 = 0;
    let mut v_res_7800_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7799_ = (lean_unbox(v_pu_7789_) as u8);
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
    lean_dec(v_a_7797_);
    lean_dec_ref(v_a_7796_);
    lean_dec(v_a_7795_);
    lean_dec_ref(v_a_7794_);
    return v_res_7800_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(
    mut v_pu_7801_: u8,
    mut v_decl_7802_: *mut LeanObject,
    mut v_type_7803_: *mut LeanObject,
    mut v_value_7804_: *mut LeanObject,
    mut v_a_7805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    v_params_7807_ = lean_ctor_get(v_decl_7802_, 2);
    lean_inc_ref(v_params_7807_);
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
    mut v_pu_7809_: *mut LeanObject,
    mut v_decl_7810_: *mut LeanObject,
    mut v_type_7811_: *mut LeanObject,
    mut v_value_7812_: *mut LeanObject,
    mut v_a_7813_: *mut LeanObject,
    mut v_a_7814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7815_: u8 = 0;
    let mut v_res_7816_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7815_ = (lean_unbox(v_pu_7809_) as u8);
    v_res_7816_ = l_Lean_Compiler_LCNF_FunDecl_update_x27___redArg(
        v_pu_boxed_7815_,
        v_decl_7810_,
        v_type_7811_,
        v_value_7812_,
        v_a_7813_,
    );
    lean_dec(v_a_7813_);
    return v_res_7816_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_update_x27(
    mut v_pu_7817_: u8,
    mut v_decl_7818_: *mut LeanObject,
    mut v_type_7819_: *mut LeanObject,
    mut v_value_7820_: *mut LeanObject,
    mut v_a_7821_: *mut LeanObject,
    mut v_a_7822_: *mut LeanObject,
    mut v_a_7823_: *mut LeanObject,
    mut v_a_7824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    v_params_7826_ = lean_ctor_get(v_decl_7818_, 2);
    lean_inc_ref(v_params_7826_);
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
    mut v_pu_7828_: *mut LeanObject,
    mut v_decl_7829_: *mut LeanObject,
    mut v_type_7830_: *mut LeanObject,
    mut v_value_7831_: *mut LeanObject,
    mut v_a_7832_: *mut LeanObject,
    mut v_a_7833_: *mut LeanObject,
    mut v_a_7834_: *mut LeanObject,
    mut v_a_7835_: *mut LeanObject,
    mut v_a_7836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7837_: u8 = 0;
    let mut v_res_7838_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7837_ = (lean_unbox(v_pu_7828_) as u8);
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
    lean_dec(v_a_7835_);
    lean_dec_ref(v_a_7834_);
    lean_dec(v_a_7833_);
    lean_dec_ref(v_a_7832_);
    return v_res_7838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(
    mut v_pu_7839_: u8,
    mut v_decl_7840_: *mut LeanObject,
    mut v_value_7841_: *mut LeanObject,
    mut v_a_7842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    v_params_7844_ = lean_ctor_get(v_decl_7840_, 2);
    lean_inc_ref(v_params_7844_);
    v_type_7845_ = lean_ctor_get(v_decl_7840_, 3);
    lean_inc_ref(v_type_7845_);
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
    mut v_pu_7847_: *mut LeanObject,
    mut v_decl_7848_: *mut LeanObject,
    mut v_value_7849_: *mut LeanObject,
    mut v_a_7850_: *mut LeanObject,
    mut v_a_7851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7852_: u8 = 0;
    let mut v_res_7853_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7852_ = (lean_unbox(v_pu_7847_) as u8);
    v_res_7853_ = l_Lean_Compiler_LCNF_FunDecl_updateValue___redArg(
        v_pu_boxed_7852_,
        v_decl_7848_,
        v_value_7849_,
        v_a_7850_,
    );
    lean_dec(v_a_7850_);
    return v_res_7853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_updateValue(
    mut v_pu_7854_: u8,
    mut v_decl_7855_: *mut LeanObject,
    mut v_value_7856_: *mut LeanObject,
    mut v_a_7857_: *mut LeanObject,
    mut v_a_7858_: *mut LeanObject,
    mut v_a_7859_: *mut LeanObject,
    mut v_a_7860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    v_params_7862_ = lean_ctor_get(v_decl_7855_, 2);
    lean_inc_ref(v_params_7862_);
    v_type_7863_ = lean_ctor_get(v_decl_7855_, 3);
    lean_inc_ref(v_type_7863_);
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
    mut v_pu_7865_: *mut LeanObject,
    mut v_decl_7866_: *mut LeanObject,
    mut v_value_7867_: *mut LeanObject,
    mut v_a_7868_: *mut LeanObject,
    mut v_a_7869_: *mut LeanObject,
    mut v_a_7870_: *mut LeanObject,
    mut v_a_7871_: *mut LeanObject,
    mut v_a_7872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7873_: u8 = 0;
    let mut v_res_7874_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7873_ = (lean_unbox(v_pu_7865_) as u8);
    v_res_7874_ = l_Lean_Compiler_LCNF_FunDecl_updateValue(
        v_pu_boxed_7873_,
        v_decl_7866_,
        v_value_7867_,
        v_a_7868_,
        v_a_7869_,
        v_a_7870_,
        v_a_7871_,
    );
    lean_dec(v_a_7871_);
    lean_dec_ref(v_a_7870_);
    lean_dec(v_a_7869_);
    lean_dec_ref(v_a_7868_);
    return v_res_7874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__0(
    mut v_pu_7875_: u8,
    mut v_p_7876_: *mut LeanObject,
    mut v_inst_7877_: *mut LeanObject,
    mut v_____do__lift_7878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    v___x_7879_ = lean_box((v_pu_7875_) as usize);
    v___x_7880_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_7880_, 0, v___x_7879_);
    lean_closure_set(v___x_7880_, 1, v_p_7876_);
    lean_closure_set(v___x_7880_, 2, v_____do__lift_7878_);
    v___x_7881_ = lean_apply_2(v_inst_7877_, lean_box(0), v___x_7880_);
    return v___x_7881_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed(
    mut v_pu_7882_: *mut LeanObject,
    mut v_p_7883_: *mut LeanObject,
    mut v_inst_7884_: *mut LeanObject,
    mut v_____do__lift_7885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7886_: u8 = 0;
    let mut v_res_7887_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7886_ = (lean_unbox(v_pu_7882_) as u8);
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
    mut v_type_7890_: *mut LeanObject,
    mut v_toPure_7891_: *mut LeanObject,
    mut v_____do__lift_7892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    v___x_7893_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_7888_,
        v_____do__lift_7892_,
        v_t_7889_,
        v_type_7890_,
    );
    v___x_7894_ = lean_apply_2(v_toPure_7891_, lean_box(0), v___x_7893_);
    return v___x_7894_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed(
    mut v_pu_7895_: *mut LeanObject,
    mut v_t_7896_: *mut LeanObject,
    mut v_type_7897_: *mut LeanObject,
    mut v_toPure_7898_: *mut LeanObject,
    mut v_____do__lift_7899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7900_: u8 = 0;
    let mut v_t_boxed_7901_: u8 = 0;
    let mut v_res_7902_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7900_ = (lean_unbox(v_pu_7895_) as u8);
    v_t_boxed_7901_ = (lean_unbox(v_t_7896_) as u8);
    v_res_7902_ = l_Lean_Compiler_LCNF_normParam___redArg___lam__1(
        v_pu_boxed_7900_,
        v_t_boxed_7901_,
        v_type_7897_,
        v_toPure_7898_,
        v_____do__lift_7899_,
    );
    lean_dec_ref(v_____do__lift_7899_);
    return v_res_7902_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg(
    mut v_pu_7903_: u8,
    mut v_t_7904_: u8,
    mut v_inst_7905_: *mut LeanObject,
    mut v_inst_7906_: *mut LeanObject,
    mut v_inst_7907_: *mut LeanObject,
    mut v_p_7908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7909_ = lean_ctor_get(v_inst_7906_, 0);
    lean_inc_ref(v_toApplicative_7909_);
    v_toBind_7910_ = lean_ctor_get(v_inst_7906_, 1);
    lean_inc_n(v_toBind_7910_, 2);
    lean_dec_ref(v_inst_7906_);
    v_type_7911_ = lean_ctor_get(v_p_7908_, 2);
    lean_inc_ref(v_type_7911_);
    v_toPure_7912_ = lean_ctor_get(v_toApplicative_7909_, 1);
    lean_inc(v_toPure_7912_);
    lean_dec_ref(v_toApplicative_7909_);
    v___x_7913_ = lean_box((v_pu_7903_) as usize);
    v___f_7914_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7914_, 0, v___x_7913_);
    lean_closure_set(v___f_7914_, 1, v_p_7908_);
    lean_closure_set(v___f_7914_, 2, v_inst_7905_);
    v___x_7915_ = lean_box((v_pu_7903_) as usize);
    v___x_7916_ = lean_box((v_t_7904_) as usize);
    v___f_7917_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7917_, 0, v___x_7915_);
    lean_closure_set(v___f_7917_, 1, v___x_7916_);
    lean_closure_set(v___f_7917_, 2, v_type_7911_);
    lean_closure_set(v___f_7917_, 3, v_toPure_7912_);
    v___x_7918_ = lean_apply_4(
        v_toBind_7910_,
        lean_box(0),
        lean_box(0),
        v_inst_7907_,
        v___f_7917_,
    );
    v___x_7919_ = lean_apply_4(
        v_toBind_7910_,
        lean_box(0),
        lean_box(0),
        v___x_7918_,
        v___f_7914_,
    );
    return v___x_7919_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___redArg___boxed(
    mut v_pu_7920_: *mut LeanObject,
    mut v_t_7921_: *mut LeanObject,
    mut v_inst_7922_: *mut LeanObject,
    mut v_inst_7923_: *mut LeanObject,
    mut v_inst_7924_: *mut LeanObject,
    mut v_p_7925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7926_: u8 = 0;
    let mut v_t_boxed_7927_: u8 = 0;
    let mut v_res_7928_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7926_ = (lean_unbox(v_pu_7920_) as u8);
    v_t_boxed_7927_ = (lean_unbox(v_t_7921_) as u8);
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
    mut v_m_7929_: *mut LeanObject,
    mut v_pu_7930_: u8,
    mut v_t_7931_: u8,
    mut v_inst_7932_: *mut LeanObject,
    mut v_inst_7933_: *mut LeanObject,
    mut v_inst_7934_: *mut LeanObject,
    mut v_p_7935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7936_ = lean_ctor_get(v_inst_7933_, 0);
    lean_inc_ref(v_toApplicative_7936_);
    v_toBind_7937_ = lean_ctor_get(v_inst_7933_, 1);
    lean_inc_n(v_toBind_7937_, 2);
    lean_dec_ref(v_inst_7933_);
    v_type_7938_ = lean_ctor_get(v_p_7935_, 2);
    lean_inc_ref(v_type_7938_);
    v_toPure_7939_ = lean_ctor_get(v_toApplicative_7936_, 1);
    lean_inc(v_toPure_7939_);
    lean_dec_ref(v_toApplicative_7936_);
    v___x_7940_ = lean_box((v_pu_7930_) as usize);
    v___f_7941_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_7941_, 0, v___x_7940_);
    lean_closure_set(v___f_7941_, 1, v_p_7935_);
    lean_closure_set(v___f_7941_, 2, v_inst_7932_);
    v___x_7942_ = lean_box((v_pu_7930_) as usize);
    v___x_7943_ = lean_box((v_t_7931_) as usize);
    v___f_7944_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_7944_, 0, v___x_7942_);
    lean_closure_set(v___f_7944_, 1, v___x_7943_);
    lean_closure_set(v___f_7944_, 2, v_type_7938_);
    lean_closure_set(v___f_7944_, 3, v_toPure_7939_);
    v___x_7945_ = lean_apply_4(
        v_toBind_7937_,
        lean_box(0),
        lean_box(0),
        v_inst_7934_,
        v___f_7944_,
    );
    v___x_7946_ = lean_apply_4(
        v_toBind_7937_,
        lean_box(0),
        lean_box(0),
        v___x_7945_,
        v___f_7941_,
    );
    return v___x_7946_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParam___boxed(
    mut v_m_7947_: *mut LeanObject,
    mut v_pu_7948_: *mut LeanObject,
    mut v_t_7949_: *mut LeanObject,
    mut v_inst_7950_: *mut LeanObject,
    mut v_inst_7951_: *mut LeanObject,
    mut v_inst_7952_: *mut LeanObject,
    mut v_p_7953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7954_: u8 = 0;
    let mut v_t_boxed_7955_: u8 = 0;
    let mut v_res_7956_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7954_ = (lean_unbox(v_pu_7948_) as u8);
    v_t_boxed_7955_ = (lean_unbox(v_t_7949_) as u8);
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
    mut v_inst_7959_: *mut LeanObject,
    mut v_inst_7960_: *mut LeanObject,
    mut v_inst_7961_: *mut LeanObject,
    mut v_ps_7962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7967_: *mut LeanObject = core::ptr::null_mut();
    v___x_7963_ = lean_box((v_pu_7957_) as usize);
    v___x_7964_ = lean_box((v_t_7958_) as usize);
    lean_inc_ref(v_inst_7960_);
    v___x_7965_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___x_7965_, 0, lean_box(0));
    lean_closure_set(v___x_7965_, 1, v___x_7963_);
    lean_closure_set(v___x_7965_, 2, v___x_7964_);
    lean_closure_set(v___x_7965_, 3, v_inst_7959_);
    lean_closure_set(v___x_7965_, 4, v_inst_7960_);
    lean_closure_set(v___x_7965_, 5, v_inst_7961_);
    v___x_7966_ = lean_unsigned_to_nat(0);
    v___x_7967_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(
        lean_box(0),
        lean_box(0),
        v_inst_7960_,
        v___x_7965_,
        v___x_7966_,
        v_ps_7962_,
    );
    return v___x_7967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___redArg___boxed(
    mut v_pu_7968_: *mut LeanObject,
    mut v_t_7969_: *mut LeanObject,
    mut v_inst_7970_: *mut LeanObject,
    mut v_inst_7971_: *mut LeanObject,
    mut v_inst_7972_: *mut LeanObject,
    mut v_ps_7973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7974_: u8 = 0;
    let mut v_t_boxed_7975_: u8 = 0;
    let mut v_res_7976_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7974_ = (lean_unbox(v_pu_7968_) as u8);
    v_t_boxed_7975_ = (lean_unbox(v_t_7969_) as u8);
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
    mut v_m_7977_: *mut LeanObject,
    mut v_pu_7978_: u8,
    mut v_t_7979_: u8,
    mut v_inst_7980_: *mut LeanObject,
    mut v_inst_7981_: *mut LeanObject,
    mut v_inst_7982_: *mut LeanObject,
    mut v_ps_7983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7984_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_7985_: *mut LeanObject,
    mut v_pu_7986_: *mut LeanObject,
    mut v_t_7987_: *mut LeanObject,
    mut v_inst_7988_: *mut LeanObject,
    mut v_inst_7989_: *mut LeanObject,
    mut v_inst_7990_: *mut LeanObject,
    mut v_ps_7991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7992_: u8 = 0;
    let mut v_t_boxed_7993_: u8 = 0;
    let mut v_res_7994_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7992_ = (lean_unbox(v_pu_7986_) as u8);
    v_t_boxed_7993_ = (lean_unbox(v_t_7987_) as u8);
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
    mut v_decl_7996_: *mut LeanObject,
    mut v_____do__lift_7997_: *mut LeanObject,
    mut v_inst_7998_: *mut LeanObject,
    mut v_____do__lift_7999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut LeanObject = core::ptr::null_mut();
    v___x_8000_ = lean_box((v_pu_7995_) as usize);
    v___x_8001_ = lean_alloc_closure(
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_8001_, 0, v___x_8000_);
    lean_closure_set(v___x_8001_, 1, v_decl_7996_);
    lean_closure_set(v___x_8001_, 2, v_____do__lift_7997_);
    lean_closure_set(v___x_8001_, 3, v_____do__lift_7999_);
    v___x_8002_ = lean_apply_2(v_inst_7998_, lean_box(0), v___x_8001_);
    return v___x_8002_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed(
    mut v_pu_8003_: *mut LeanObject,
    mut v_decl_8004_: *mut LeanObject,
    mut v_____do__lift_8005_: *mut LeanObject,
    mut v_inst_8006_: *mut LeanObject,
    mut v_____do__lift_8007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8008_: u8 = 0;
    let mut v_res_8009_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8008_ = (lean_unbox(v_pu_8003_) as u8);
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
    mut v_value_8011_: *mut LeanObject,
    mut v_t_8012_: u8,
    mut v_toPure_8013_: *mut LeanObject,
    mut v_____do__lift_8014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    v___x_8015_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_8010_,
        v_____do__lift_8014_,
        v_value_8011_,
        v_t_8012_,
    );
    v___x_8016_ = lean_apply_2(v_toPure_8013_, lean_box(0), v___x_8015_);
    return v___x_8016_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed(
    mut v_pu_8017_: *mut LeanObject,
    mut v_value_8018_: *mut LeanObject,
    mut v_t_8019_: *mut LeanObject,
    mut v_toPure_8020_: *mut LeanObject,
    mut v_____do__lift_8021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8022_: u8 = 0;
    let mut v_t_boxed_8023_: u8 = 0;
    let mut v_res_8024_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8022_ = (lean_unbox(v_pu_8017_) as u8);
    v_t_boxed_8023_ = (lean_unbox(v_t_8019_) as u8);
    v_res_8024_ = l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1(
        v_pu_boxed_8022_,
        v_value_8018_,
        v_t_boxed_8023_,
        v_toPure_8020_,
        v_____do__lift_8021_,
    );
    lean_dec_ref(v_____do__lift_8021_);
    return v_res_8024_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2(
    mut v_pu_8025_: u8,
    mut v_decl_8026_: *mut LeanObject,
    mut v_inst_8027_: *mut LeanObject,
    mut v_value_8028_: *mut LeanObject,
    mut v_t_8029_: u8,
    mut v_toPure_8030_: *mut LeanObject,
    mut v_toBind_8031_: *mut LeanObject,
    mut v_inst_8032_: *mut LeanObject,
    mut v_____do__lift_8033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    v___x_8034_ = lean_box((v_pu_8025_) as usize);
    v___f_8035_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_8035_, 0, v___x_8034_);
    lean_closure_set(v___f_8035_, 1, v_decl_8026_);
    lean_closure_set(v___f_8035_, 2, v_____do__lift_8033_);
    lean_closure_set(v___f_8035_, 3, v_inst_8027_);
    v___x_8036_ = lean_box((v_pu_8025_) as usize);
    v___x_8037_ = lean_box((v_t_8029_) as usize);
    v___f_8038_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_8038_, 0, v___x_8036_);
    lean_closure_set(v___f_8038_, 1, v_value_8028_);
    lean_closure_set(v___f_8038_, 2, v___x_8037_);
    lean_closure_set(v___f_8038_, 3, v_toPure_8030_);
    lean_inc(v_toBind_8031_);
    v___x_8039_ = lean_apply_4(
        v_toBind_8031_,
        lean_box(0),
        lean_box(0),
        v_inst_8032_,
        v___f_8038_,
    );
    v___x_8040_ = lean_apply_4(
        v_toBind_8031_,
        lean_box(0),
        lean_box(0),
        v___x_8039_,
        v___f_8035_,
    );
    return v___x_8040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed(
    mut v_pu_8041_: *mut LeanObject,
    mut v_decl_8042_: *mut LeanObject,
    mut v_inst_8043_: *mut LeanObject,
    mut v_value_8044_: *mut LeanObject,
    mut v_t_8045_: *mut LeanObject,
    mut v_toPure_8046_: *mut LeanObject,
    mut v_toBind_8047_: *mut LeanObject,
    mut v_inst_8048_: *mut LeanObject,
    mut v_____do__lift_8049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8050_: u8 = 0;
    let mut v_t_boxed_8051_: u8 = 0;
    let mut v_res_8052_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8050_ = (lean_unbox(v_pu_8041_) as u8);
    v_t_boxed_8051_ = (lean_unbox(v_t_8045_) as u8);
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
    mut v_inst_8055_: *mut LeanObject,
    mut v_inst_8056_: *mut LeanObject,
    mut v_inst_8057_: *mut LeanObject,
    mut v_decl_8058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8059_ = lean_ctor_get(v_inst_8056_, 0);
    lean_inc_ref(v_toApplicative_8059_);
    v_toBind_8060_ = lean_ctor_get(v_inst_8056_, 1);
    lean_inc_n(v_toBind_8060_, 3);
    lean_dec_ref(v_inst_8056_);
    v_type_8061_ = lean_ctor_get(v_decl_8058_, 2);
    lean_inc_ref(v_type_8061_);
    v_value_8062_ = lean_ctor_get(v_decl_8058_, 3);
    lean_inc(v_value_8062_);
    v_toPure_8063_ = lean_ctor_get(v_toApplicative_8059_, 1);
    lean_inc_n(v_toPure_8063_, 2);
    lean_dec_ref(v_toApplicative_8059_);
    v___x_8064_ = lean_box((v_pu_8053_) as usize);
    v___x_8065_ = lean_box((v_t_8054_) as usize);
    lean_inc(v_inst_8057_);
    v___f_8066_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normLetDecl___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_8066_, 0, v___x_8064_);
    lean_closure_set(v___f_8066_, 1, v_decl_8058_);
    lean_closure_set(v___f_8066_, 2, v_inst_8055_);
    lean_closure_set(v___f_8066_, 3, v_value_8062_);
    lean_closure_set(v___f_8066_, 4, v___x_8065_);
    lean_closure_set(v___f_8066_, 5, v_toPure_8063_);
    lean_closure_set(v___f_8066_, 6, v_toBind_8060_);
    lean_closure_set(v___f_8066_, 7, v_inst_8057_);
    v___x_8067_ = lean_box((v_pu_8053_) as usize);
    v___x_8068_ = lean_box((v_t_8054_) as usize);
    v___f_8069_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normParam___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_8069_, 0, v___x_8067_);
    lean_closure_set(v___f_8069_, 1, v___x_8068_);
    lean_closure_set(v___f_8069_, 2, v_type_8061_);
    lean_closure_set(v___f_8069_, 3, v_toPure_8063_);
    v___x_8070_ = lean_apply_4(
        v_toBind_8060_,
        lean_box(0),
        lean_box(0),
        v_inst_8057_,
        v___f_8069_,
    );
    v___x_8071_ = lean_apply_4(
        v_toBind_8060_,
        lean_box(0),
        lean_box(0),
        v___x_8070_,
        v___f_8066_,
    );
    return v___x_8071_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___redArg___boxed(
    mut v_pu_8072_: *mut LeanObject,
    mut v_t_8073_: *mut LeanObject,
    mut v_inst_8074_: *mut LeanObject,
    mut v_inst_8075_: *mut LeanObject,
    mut v_inst_8076_: *mut LeanObject,
    mut v_decl_8077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8078_: u8 = 0;
    let mut v_t_boxed_8079_: u8 = 0;
    let mut v_res_8080_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8078_ = (lean_unbox(v_pu_8072_) as u8);
    v_t_boxed_8079_ = (lean_unbox(v_t_8073_) as u8);
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
    mut v_m_8081_: *mut LeanObject,
    mut v_pu_8082_: u8,
    mut v_t_8083_: u8,
    mut v_inst_8084_: *mut LeanObject,
    mut v_inst_8085_: *mut LeanObject,
    mut v_inst_8086_: *mut LeanObject,
    mut v_decl_8087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8088_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_8089_: *mut LeanObject,
    mut v_pu_8090_: *mut LeanObject,
    mut v_t_8091_: *mut LeanObject,
    mut v_inst_8092_: *mut LeanObject,
    mut v_inst_8093_: *mut LeanObject,
    mut v_inst_8094_: *mut LeanObject,
    mut v_decl_8095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8096_: u8 = 0;
    let mut v_t_boxed_8097_: u8 = 0;
    let mut v_res_8098_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8096_ = (lean_unbox(v_pu_8090_) as u8);
    v_t_boxed_8097_ = (lean_unbox(v_t_8091_) as u8);
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
) -> *mut LeanObject {
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v_toFunctor_8122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8128_: u8 = 0;
    let mut v___f_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8144_: u8 = 0;
    let mut v_unused_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8146_: u8 = 0;
    let mut v_unused_8147_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8101_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instMonadCompilerM___closed__1,
                );
                v_toApplicative_8102_ = lean_ctor_get(v___x_8101_, 0);
                v_toFunctor_8103_ = lean_ctor_get(v_toApplicative_8102_, 0);
                v_toSeq_8104_ = lean_ctor_get(v_toApplicative_8102_, 2);
                v_toSeqLeft_8105_ = lean_ctor_get(v_toApplicative_8102_, 3);
                v_toSeqRight_8106_ = lean_ctor_get(v_toApplicative_8102_, 4);
                v___f_8107_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__2;
                v___f_8108_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__3;
                lean_inc_ref_n(v_toFunctor_8103_, 2);
                v___f_8109_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8109_, 0, v_toFunctor_8103_);
                v___f_8110_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8110_, 0, v_toFunctor_8103_);
                v___x_8111_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8111_, 0, v___f_8109_);
                lean_ctor_set(v___x_8111_, 1, v___f_8110_);
                lean_inc(v_toSeqRight_8106_);
                v___f_8112_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8112_, 0, v_toSeqRight_8106_);
                lean_inc(v_toSeqLeft_8105_);
                v___f_8113_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8113_, 0, v_toSeqLeft_8105_);
                lean_inc(v_toSeq_8104_);
                v___f_8114_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8114_, 0, v_toSeq_8104_);
                v___x_8115_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_8115_, 0, v___x_8111_);
                lean_ctor_set(v___x_8115_, 1, v___f_8107_);
                lean_ctor_set(v___x_8115_, 2, v___f_8114_);
                lean_ctor_set(v___x_8115_, 3, v___f_8113_);
                lean_ctor_set(v___x_8115_, 4, v___f_8112_);
                v___x_8116_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8116_, 0, v___x_8115_);
                lean_ctor_set(v___x_8116_, 1, v___f_8108_);
                v___x_8117_ = l_StateRefT_x27_instMonad___redArg(v___x_8116_);
                v_toApplicative_8118_ = lean_ctor_get(v___x_8117_, 0);
                v_isSharedCheck_8146_ = (!lean_is_exclusive(v___x_8117_)) as u8;
                if v_isSharedCheck_8146_ == 0 {
                    v_unused_8147_ = lean_ctor_get(v___x_8117_, 1);
                    lean_dec(v_unused_8147_);
                    v___x_8120_ = v___x_8117_;
                    v_isShared_8121_ = v_isSharedCheck_8146_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_8118_);
                    lean_dec(v___x_8117_);
                    v___x_8120_ = lean_box(0);
                    v_isShared_8121_ = v_isSharedCheck_8146_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_8122_ = lean_ctor_get(v_toApplicative_8118_, 0);
                v_toSeq_8123_ = lean_ctor_get(v_toApplicative_8118_, 2);
                v_toSeqLeft_8124_ = lean_ctor_get(v_toApplicative_8118_, 3);
                v_toSeqRight_8125_ = lean_ctor_get(v_toApplicative_8118_, 4);
                v_isSharedCheck_8144_ = (!lean_is_exclusive(v_toApplicative_8118_)) as u8;
                if v_isSharedCheck_8144_ == 0 {
                    v_unused_8145_ = lean_ctor_get(v_toApplicative_8118_, 1);
                    lean_dec(v_unused_8145_);
                    v___x_8127_ = v_toApplicative_8118_;
                    v_isShared_8128_ = v_isSharedCheck_8144_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_8125_);
                    lean_inc(v_toSeqLeft_8124_);
                    lean_inc(v_toSeq_8123_);
                    lean_inc(v_toFunctor_8122_);
                    lean_dec(v_toApplicative_8118_);
                    v___x_8127_ = lean_box(0);
                    v_isShared_8128_ = v_isSharedCheck_8144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_8129_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__4;
                v___f_8130_ = l_Lean_Compiler_LCNF_instMonadCompilerM___closed__5;
                lean_inc_ref(v_toFunctor_8122_);
                v___f_8131_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8131_, 0, v_toFunctor_8122_);
                v___f_8132_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8132_, 0, v_toFunctor_8122_);
                v___x_8133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8133_, 0, v___f_8131_);
                lean_ctor_set(v___x_8133_, 1, v___f_8132_);
                v___f_8134_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8134_, 0, v_toSeqRight_8125_);
                v___f_8135_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8135_, 0, v_toSeqLeft_8124_);
                v___f_8136_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8136_, 0, v_toSeq_8123_);
                if v_isShared_8128_ == 0 {
                    lean_ctor_set(v___x_8127_, 4, v___f_8134_);
                    lean_ctor_set(v___x_8127_, 3, v___f_8135_);
                    lean_ctor_set(v___x_8127_, 2, v___f_8136_);
                    lean_ctor_set(v___x_8127_, 1, v___f_8129_);
                    lean_ctor_set(v___x_8127_, 0, v___x_8133_);
                    v___x_8138_ = v___x_8127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8143_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 0, v___x_8133_);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 1, v___f_8129_);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 2, v___f_8136_);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 3, v___f_8135_);
                    lean_ctor_set(v_reuseFailAlloc_8143_, 4, v___f_8134_);
                    v___x_8138_ = v_reuseFailAlloc_8143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8121_ == 0 {
                    lean_ctor_set(v___x_8120_, 1, v___f_8130_);
                    lean_ctor_set(v___x_8120_, 0, v___x_8138_);
                    v___x_8140_ = v___x_8120_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8142_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8142_, 0, v___x_8138_);
                    lean_ctor_set(v_reuseFailAlloc_8142_, 1, v___f_8130_);
                    v___x_8140_ = v_reuseFailAlloc_8142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8141_ =
                    lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_8141_, 0, lean_box(0));
                lean_closure_set(v___x_8141_, 1, lean_box(0));
                lean_closure_set(v___x_8141_, 2, v___x_8140_);
                return v___x_8141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM___boxed(
    mut v_pu_8148_: *mut LeanObject,
    mut v_t_8149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8150_: u8 = 0;
    let mut v_t_boxed_8151_: u8 = 0;
    let mut v_res_8152_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8150_ = (lean_unbox(v_pu_8148_) as u8);
    v_t_boxed_8151_ = (lean_unbox(v_t_8149_) as u8);
    v_res_8152_ =
        l_Lean_Compiler_LCNF_instMonadFVarSubstNormalizerM(v_pu_boxed_8150_, v_t_boxed_8151_);
    return v_res_8152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___redArg(
    mut v_pu_8153_: u8,
    mut v_inst_8154_: *mut LeanObject,
    mut v_result_8155_: *mut LeanObject,
    mut v_x_8156_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_result_8155_) == 0 {
        let mut v_fvarId_8157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_8154_);
        v_fvarId_8157_ = lean_ctor_get(v_result_8155_, 0);
        lean_inc(v_fvarId_8157_);
        lean_dec_ref_known(v_result_8155_, 1);
        v___x_8158_ = lean_apply_1(v_x_8156_, v_fvarId_8157_);
        return v___x_8158_;
    } else {
        let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_8156_);
        v___x_8159_ = lean_box((v_pu_8153_) as usize);
        v___x_8160_ = lean_alloc_closure(
            l_Lean_Compiler_LCNF_mkReturnErased___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        lean_closure_set(v___x_8160_, 0, v___x_8159_);
        v___x_8161_ = lean_apply_2(v_inst_8154_, lean_box(0), v___x_8160_);
        return v___x_8161_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___redArg___boxed(
    mut v_pu_8162_: *mut LeanObject,
    mut v_inst_8163_: *mut LeanObject,
    mut v_result_8164_: *mut LeanObject,
    mut v_x_8165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8166_: u8 = 0;
    let mut v_res_8167_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8166_ = (lean_unbox(v_pu_8162_) as u8);
    v_res_8167_ = l_Lean_Compiler_LCNF_withNormFVarResult___redArg(
        v_pu_boxed_8166_,
        v_inst_8163_,
        v_result_8164_,
        v_x_8165_,
    );
    return v_res_8167_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult(
    mut v_m_8168_: *mut LeanObject,
    mut v_pu_8169_: u8,
    mut v_inst_8170_: *mut LeanObject,
    mut v_inst_8171_: *mut LeanObject,
    mut v_result_8172_: *mut LeanObject,
    mut v_x_8173_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_result_8172_) == 0 {
        let mut v_fvarId_8174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_8170_);
        v_fvarId_8174_ = lean_ctor_get(v_result_8172_, 0);
        lean_inc(v_fvarId_8174_);
        lean_dec_ref_known(v_result_8172_, 1);
        v___x_8175_ = lean_apply_1(v_x_8173_, v_fvarId_8174_);
        return v___x_8175_;
    } else {
        let mut v___x_8176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8178_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_8173_);
        v___x_8176_ = lean_box((v_pu_8169_) as usize);
        v___x_8177_ = lean_alloc_closure(
            l_Lean_Compiler_LCNF_mkReturnErased___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        lean_closure_set(v___x_8177_, 0, v___x_8176_);
        v___x_8178_ = lean_apply_2(v_inst_8170_, lean_box(0), v___x_8177_);
        return v___x_8178_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withNormFVarResult___boxed(
    mut v_m_8179_: *mut LeanObject,
    mut v_pu_8180_: *mut LeanObject,
    mut v_inst_8181_: *mut LeanObject,
    mut v_inst_8182_: *mut LeanObject,
    mut v_result_8183_: *mut LeanObject,
    mut v_x_8184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8185_: u8 = 0;
    let mut v_res_8186_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8185_ = (lean_unbox(v_pu_8180_) as u8);
    v_res_8186_ = l_Lean_Compiler_LCNF_withNormFVarResult(
        v_m_8179_,
        v_pu_boxed_8185_,
        v_inst_8181_,
        v_inst_8182_,
        v_result_8183_,
        v_x_8184_,
    );
    lean_dec_ref(v_inst_8182_);
    return v_res_8186_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(
    mut v_pu_8187_: u8,
    mut v_t_8188_: u8,
    mut v_args_8189_: *mut LeanObject,
    mut v___y_8190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut LeanObject = core::ptr::null_mut();
    v___x_8192_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_8187_,
        v___y_8190_,
        v_args_8189_,
        v_t_8188_,
    );
    v___x_8193_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8193_, 0, v___x_8192_);
    return v___x_8193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg___boxed(
    mut v_pu_8194_: *mut LeanObject,
    mut v_t_8195_: *mut LeanObject,
    mut v_args_8196_: *mut LeanObject,
    mut v___y_8197_: *mut LeanObject,
    mut v___y_8198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8199_: u8 = 0;
    let mut v_t_boxed_8200_: u8 = 0;
    let mut v_res_8201_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8199_ = (lean_unbox(v_pu_8194_) as u8);
    v_t_boxed_8200_ = (lean_unbox(v_t_8195_) as u8);
    v_res_8201_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(
            v_pu_boxed_8199_,
            v_t_boxed_8200_,
            v_args_8196_,
            v___y_8197_,
        );
    lean_dec_ref(v___y_8197_);
    return v_res_8201_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(
    mut v_pu_8202_: u8,
    mut v_t_8203_: u8,
    mut v_i_8204_: *mut LeanObject,
    mut v_as_8205_: *mut LeanObject,
    mut v___y_8206_: *mut LeanObject,
    mut v___y_8207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: u8 = 0;
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: usize = 0;
    let mut v___x_8218_: usize = 0;
    let mut v___x_8219_: u8 = 0;
    let mut v___x_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8230_: u8 = 0;
    let mut v___x_8232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8209_ = lean_array_get_size(v_as_8205_);
                v___x_8210_ = lean_nat_dec_lt(v_i_8204_, v___x_8209_);
                if v___x_8210_ == 0 {
                    lean_dec(v_i_8204_);
                    v___x_8211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8211_, 0, v_as_8205_);
                    return v___x_8211_;
                } else {
                    v_a_8212_ = lean_array_fget_borrowed(v_as_8205_, v_i_8204_);
                    v_type_8213_ = lean_ctor_get(v_a_8212_, 2);
                    lean_inc_ref(v_type_8213_);
                    v___x_8214_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8202_, v___y_8206_, v_t_8203_, v_type_8213_);
                    lean_inc(v_a_8212_);
                    v___x_8215_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_8202_, v_a_8212_, v___x_8214_, v___y_8207_);
                    if lean_obj_tag(v___x_8215_) == 0 {
                        v_a_8216_ = lean_ctor_get(v___x_8215_, 0);
                        lean_inc(v_a_8216_);
                        lean_dec_ref_known(v___x_8215_, 1);
                        v___x_8217_ = lean_ptr_addr(v_a_8212_);
                        v___x_8218_ = lean_ptr_addr(v_a_8216_);
                        v___x_8219_ = lean_usize_dec_eq(v___x_8217_, v___x_8218_);
                        if v___x_8219_ == 0 {
                            v___x_8220_ = lean_unsigned_to_nat(1);
                            v___x_8221_ = lean_nat_add(v_i_8204_, v___x_8220_);
                            v___x_8222_ = lean_array_fset(v_as_8205_, v_i_8204_, v_a_8216_);
                            lean_dec(v_i_8204_);
                            v_i_8204_ = v___x_8221_;
                            v_as_8205_ = v___x_8222_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_8216_);
                            v___x_8224_ = lean_unsigned_to_nat(1);
                            v___x_8225_ = lean_nat_add(v_i_8204_, v___x_8224_);
                            lean_dec(v_i_8204_);
                            v_i_8204_ = v___x_8225_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_8205_);
                        lean_dec(v_i_8204_);
                        v_a_8227_ = lean_ctor_get(v___x_8215_, 0);
                        v_isSharedCheck_8234_ = (!lean_is_exclusive(v___x_8215_)) as u8;
                        if v_isSharedCheck_8234_ == 0 {
                            v___x_8229_ = v___x_8215_;
                            v_isShared_8230_ = v_isSharedCheck_8234_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8227_);
                            lean_dec(v___x_8215_);
                            v___x_8229_ = lean_box(0);
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
                    v_reuseFailAlloc_8233_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8233_, 0, v_a_8227_);
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
    mut v_pu_8235_: *mut LeanObject,
    mut v_t_8236_: *mut LeanObject,
    mut v_i_8237_: *mut LeanObject,
    mut v_as_8238_: *mut LeanObject,
    mut v___y_8239_: *mut LeanObject,
    mut v___y_8240_: *mut LeanObject,
    mut v___y_8241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8242_: u8 = 0;
    let mut v_t_boxed_8243_: u8 = 0;
    let mut v_res_8244_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8242_ = (lean_unbox(v_pu_8235_) as u8);
    v_t_boxed_8243_ = (lean_unbox(v_t_8236_) as u8);
    v_res_8244_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_boxed_8242_, v_t_boxed_8243_, v_i_8237_, v_as_8238_, v___y_8239_, v___y_8240_);
    lean_dec(v___y_8240_);
    lean_dec_ref(v___y_8239_);
    return v_res_8244_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(
    mut v_pu_8245_: u8,
    mut v_t_8246_: u8,
    mut v_ps_8247_: *mut LeanObject,
    mut v___y_8248_: *mut LeanObject,
    mut v___y_8249_: *mut LeanObject,
    mut v___y_8250_: *mut LeanObject,
    mut v___y_8251_: *mut LeanObject,
    mut v___y_8252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8255_: *mut LeanObject = core::ptr::null_mut();
    v___x_8254_ = lean_unsigned_to_nat(0);
    v___x_8255_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_8245_, v_t_8246_, v___x_8254_, v_ps_8247_, v___y_8248_, v___y_8250_);
    return v___x_8255_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg___boxed(
    mut v_pu_8256_: *mut LeanObject,
    mut v_t_8257_: *mut LeanObject,
    mut v_ps_8258_: *mut LeanObject,
    mut v___y_8259_: *mut LeanObject,
    mut v___y_8260_: *mut LeanObject,
    mut v___y_8261_: *mut LeanObject,
    mut v___y_8262_: *mut LeanObject,
    mut v___y_8263_: *mut LeanObject,
    mut v___y_8264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8265_: u8 = 0;
    let mut v_t_boxed_8266_: u8 = 0;
    let mut v_res_8267_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8265_ = (lean_unbox(v_pu_8256_) as u8);
    v_t_boxed_8266_ = (lean_unbox(v_t_8257_) as u8);
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
    lean_dec(v___y_8263_);
    lean_dec_ref(v___y_8262_);
    lean_dec(v___y_8261_);
    lean_dec_ref(v___y_8260_);
    lean_dec_ref(v___y_8259_);
    return v_res_8267_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(
    mut v_pu_8268_: u8,
    mut v_t_8269_: u8,
    mut v_decl_8270_: *mut LeanObject,
    mut v___y_8271_: *mut LeanObject,
    mut v___y_8272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut LeanObject = core::ptr::null_mut();
    v_type_8274_ = lean_ctor_get(v_decl_8270_, 2);
    v_value_8275_ = lean_ctor_get(v_decl_8270_, 3);
    lean_inc_ref(v_type_8274_);
    v___x_8276_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_8268_,
        v___y_8271_,
        v_t_8269_,
        v_type_8274_,
    );
    lean_inc(v_value_8275_);
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
    mut v_pu_8279_: *mut LeanObject,
    mut v_t_8280_: *mut LeanObject,
    mut v_decl_8281_: *mut LeanObject,
    mut v___y_8282_: *mut LeanObject,
    mut v___y_8283_: *mut LeanObject,
    mut v___y_8284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_8285_: u8 = 0;
    let mut v_t_boxed_8286_: u8 = 0;
    let mut v_res_8287_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_8285_ = (lean_unbox(v_pu_8279_) as u8);
    v_t_boxed_8286_ = (lean_unbox(v_t_8280_) as u8);
    v_res_8287_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(
            v_pu_boxed_8285_,
            v_t_boxed_8286_,
            v_decl_8281_,
            v___y_8282_,
            v___y_8283_,
        );
    lean_dec(v___y_8283_);
    lean_dec_ref(v___y_8282_);
    return v_res_8287_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(
    mut v_pu_8288_: u8,
    mut v_t_8289_: u8,
    mut v_i_8290_: *mut LeanObject,
    mut v_as_8291_: *mut LeanObject,
    mut v___y_8292_: *mut LeanObject,
    mut v___y_8293_: *mut LeanObject,
    mut v___y_8294_: *mut LeanObject,
    mut v___y_8295_: *mut LeanObject,
    mut v___y_8296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: u8 = 0;
    let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: usize = 0;
    let mut v___x_8305_: usize = 0;
    let mut v___x_8306_: u8 = 0;
    let mut v___x_8307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_8314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8324_: u8 = 0;
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8328_: u8 = 0;
    let mut v_a_8329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8332_: u8 = 0;
    let mut v___x_8334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8336_: u8 = 0;
    let mut v_code_8337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8344_: u8 = 0;
    let mut v___x_8346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8348_: u8 = 0;
    let mut v_code_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8356_: u8 = 0;
    let mut v___x_8358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8298_ = lean_array_get_size(v_as_8291_);
                v___x_8299_ = lean_nat_dec_lt(v_i_8290_, v___x_8298_);
                if v___x_8299_ == 0 {
                    lean_dec(v_i_8290_);
                    v___x_8300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8300_, 0, v_as_8291_);
                    return v___x_8300_;
                } else {
                    v_a_8301_ = lean_array_fget_borrowed(v_as_8291_, v_i_8290_);
                    match lean_obj_tag(v_a_8301_) {
                        0 => {
                            v_params_8314_ = lean_ctor_get(v_a_8301_, 1);
                            v_code_8315_ = lean_ctor_get(v_a_8301_, 2);
                            lean_inc_ref(v_params_8314_);
                            v___x_8316_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_8288_, v_t_8289_, v_params_8314_, v___y_8292_, v___y_8293_, v___y_8294_, v___y_8295_, v___y_8296_);
                            if lean_obj_tag(v___x_8316_) == 0 {
                                v_a_8317_ = lean_ctor_get(v___x_8316_, 0);
                                lean_inc(v_a_8317_);
                                lean_dec_ref_known(v___x_8316_, 1);
                                lean_inc_ref(v_code_8315_);
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
                                if lean_obj_tag(v___x_8318_) == 0 {
                                    v_a_8319_ = lean_ctor_get(v___x_8318_, 0);
                                    lean_inc(v_a_8319_);
                                    lean_dec_ref_known(v___x_8318_, 1);
                                    lean_inc_ref(v_a_8301_);
                                    v___x_8320_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v_pu_8288_, v_a_8301_, v_a_8317_, v_a_8319_);
                                    v_a_8303_ = v___x_8320_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_8317_);
                                    lean_dec_ref(v_as_8291_);
                                    lean_dec(v_i_8290_);
                                    v_a_8321_ = lean_ctor_get(v___x_8318_, 0);
                                    v_isSharedCheck_8328_ = (!lean_is_exclusive(v___x_8318_)) as u8;
                                    if v_isSharedCheck_8328_ == 0 {
                                        v___x_8323_ = v___x_8318_;
                                        v_isShared_8324_ = v_isSharedCheck_8328_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8321_);
                                        lean_dec(v___x_8318_);
                                        v___x_8323_ = lean_box(0);
                                        v_isShared_8324_ = v_isSharedCheck_8328_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_as_8291_);
                                lean_dec(v_i_8290_);
                                v_a_8329_ = lean_ctor_get(v___x_8316_, 0);
                                v_isSharedCheck_8336_ = (!lean_is_exclusive(v___x_8316_)) as u8;
                                if v_isSharedCheck_8336_ == 0 {
                                    v___x_8331_ = v___x_8316_;
                                    v_isShared_8332_ = v_isSharedCheck_8336_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_8329_);
                                    lean_dec(v___x_8316_);
                                    v___x_8331_ = lean_box(0);
                                    v_isShared_8332_ = v_isSharedCheck_8336_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_code_8337_ = lean_ctor_get(v_a_8301_, 1);
                            lean_inc_ref(v_code_8337_);
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
                            if lean_obj_tag(v___x_8338_) == 0 {
                                v_a_8339_ = lean_ctor_get(v___x_8338_, 0);
                                lean_inc(v_a_8339_);
                                lean_dec_ref_known(v___x_8338_, 1);
                                lean_inc_ref(v_a_8301_);
                                v___x_8340_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_8301_, v_a_8339_);
                                v_a_8303_ = v___x_8340_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_as_8291_);
                                lean_dec(v_i_8290_);
                                v_a_8341_ = lean_ctor_get(v___x_8338_, 0);
                                v_isSharedCheck_8348_ = (!lean_is_exclusive(v___x_8338_)) as u8;
                                if v_isSharedCheck_8348_ == 0 {
                                    v___x_8343_ = v___x_8338_;
                                    v_isShared_8344_ = v_isSharedCheck_8348_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_8341_);
                                    lean_dec(v___x_8338_);
                                    v___x_8343_ = lean_box(0);
                                    v_isShared_8344_ = v_isSharedCheck_8348_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_code_8349_ = lean_ctor_get(v_a_8301_, 0);
                            lean_inc_ref(v_code_8349_);
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
                            if lean_obj_tag(v___x_8350_) == 0 {
                                v_a_8351_ = lean_ctor_get(v___x_8350_, 0);
                                lean_inc(v_a_8351_);
                                lean_dec_ref_known(v___x_8350_, 1);
                                lean_inc_ref(v_a_8301_);
                                v___x_8352_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_8301_, v_a_8351_);
                                v_a_8303_ = v___x_8352_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_as_8291_);
                                lean_dec(v_i_8290_);
                                v_a_8353_ = lean_ctor_get(v___x_8350_, 0);
                                v_isSharedCheck_8360_ = (!lean_is_exclusive(v___x_8350_)) as u8;
                                if v_isSharedCheck_8360_ == 0 {
                                    v___x_8355_ = v___x_8350_;
                                    v_isShared_8356_ = v_isSharedCheck_8360_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_8353_);
                                    lean_dec(v___x_8350_);
                                    v___x_8355_ = lean_box(0);
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
                    v___x_8307_ = lean_unsigned_to_nat(1);
                    v___x_8308_ = lean_nat_add(v_i_8290_, v___x_8307_);
                    v___x_8309_ = lean_array_fset(v_as_8291_, v_i_8290_, v_a_8303_);
                    lean_dec(v_i_8290_);
                    v_i_8290_ = v___x_8308_;
                    v_as_8291_ = v___x_8309_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_8303_);
                    v___x_8311_ = lean_unsigned_to_nat(1);
                    v___x_8312_ = lean_nat_add(v_i_8290_, v___x_8311_);
                    lean_dec(v_i_8290_);
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
                    v_reuseFailAlloc_8327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8327_, 0, v_a_8321_);
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
                    v_reuseFailAlloc_8335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8335_, 0, v_a_8329_);
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
                    v_reuseFailAlloc_8347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8347_, 0, v_a_8341_);
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
                    v_reuseFailAlloc_8359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8359_, 0, v_a_8353_);
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
    mut v_code_8363_: *mut LeanObject,
    mut v_a_8364_: *mut LeanObject,
    mut v_a_8365_: *mut LeanObject,
    mut v_a_8366_: *mut LeanObject,
    mut v_a_8367_: *mut LeanObject,
    mut v_a_8368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_8370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8378_: u8 = 0;
    let mut v___y_8380_: u8 = 0;
    let mut v___x_8382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8383_: u8 = 0;
    let mut v___x_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8390_: u8 = 0;
    let mut v_unused_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: usize = 0;
    let mut v___x_8397_: usize = 0;
    let mut v___x_8398_: u8 = 0;
    let mut v___x_8399_: usize = 0;
    let mut v___x_8400_: usize = 0;
    let mut v___x_8401_: u8 = 0;
    let mut v_isSharedCheck_8402_: u8 = 0;
    let mut v_a_8403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8406_: u8 = 0;
    let mut v___x_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8410_: u8 = 0;
    let mut v_decl_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8419_: u8 = 0;
    let mut v___y_8421_: u8 = 0;
    let mut v___x_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8424_: u8 = 0;
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8431_: u8 = 0;
    let mut v_unused_8432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8437_: usize = 0;
    let mut v___x_8438_: usize = 0;
    let mut v___x_8439_: u8 = 0;
    let mut v___x_8440_: usize = 0;
    let mut v___x_8441_: usize = 0;
    let mut v___x_8442_: u8 = 0;
    let mut v_isSharedCheck_8443_: u8 = 0;
    let mut v_a_8444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8447_: u8 = 0;
    let mut v___x_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8451_: u8 = 0;
    let mut v_decl_8452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8460_: u8 = 0;
    let mut v___y_8462_: u8 = 0;
    let mut v___x_8464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8465_: u8 = 0;
    let mut v___x_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8472_: u8 = 0;
    let mut v_unused_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8478_: usize = 0;
    let mut v___x_8479_: usize = 0;
    let mut v___x_8480_: u8 = 0;
    let mut v___x_8481_: usize = 0;
    let mut v___x_8482_: usize = 0;
    let mut v___x_8483_: u8 = 0;
    let mut v_isSharedCheck_8484_: u8 = 0;
    let mut v_a_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8488_: u8 = 0;
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8492_: u8 = 0;
    let mut v_fvarId_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8501_: u8 = 0;
    let mut v___y_8503_: u8 = 0;
    let mut v___x_8505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8506_: u8 = 0;
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8513_: u8 = 0;
    let mut v_unused_8514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8519_: u8 = 0;
    let mut v___x_8520_: usize = 0;
    let mut v___x_8521_: usize = 0;
    let mut v___x_8522_: u8 = 0;
    let mut v_isSharedCheck_8523_: u8 = 0;
    let mut v_a_8524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8527_: u8 = 0;
    let mut v___x_8529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8531_: u8 = 0;
    let mut v___x_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_8533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_8534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_8535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8540_: u8 = 0;
    let mut v___x_8541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8546_: u8 = 0;
    let mut v___x_8547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8552_: u8 = 0;
    let mut v___x_8555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8564_: u8 = 0;
    let mut v___x_8565_: u8 = 0;
    let mut v___x_8566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: usize = 0;
    let mut v___x_8568_: usize = 0;
    let mut v___x_8569_: u8 = 0;
    let mut v___x_8570_: usize = 0;
    let mut v___x_8571_: usize = 0;
    let mut v___x_8572_: u8 = 0;
    let mut v_isSharedCheck_8573_: u8 = 0;
    let mut v_a_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8577_: u8 = 0;
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8581_: u8 = 0;
    let mut v_isSharedCheck_8582_: u8 = 0;
    let mut v___x_8583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8584_: u8 = 0;
    let mut v_fvarId_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8590_: u8 = 0;
    let mut v___x_8591_: u8 = 0;
    let mut v___x_8593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8594_: u8 = 0;
    let mut v___x_8596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8601_: u8 = 0;
    let mut v_unused_8602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8606_: u8 = 0;
    let mut v___x_8607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_8608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8610_: usize = 0;
    let mut v___x_8611_: usize = 0;
    let mut v___x_8612_: u8 = 0;
    let mut v___x_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8615_: u8 = 0;
    let mut v___x_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8620_: u8 = 0;
    let mut v_unused_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_8625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8634_: u8 = 0;
    let mut v___y_8636_: u8 = 0;
    let mut v___x_8638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8639_: u8 = 0;
    let mut v___x_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8646_: u8 = 0;
    let mut v_unused_8647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: usize = 0;
    let mut v___x_8652_: usize = 0;
    let mut v___x_8653_: u8 = 0;
    let mut v___x_8655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8656_: u8 = 0;
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8663_: u8 = 0;
    let mut v_unused_8664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8668_: usize = 0;
    let mut v___x_8669_: usize = 0;
    let mut v___x_8670_: u8 = 0;
    let mut v___x_8672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8673_: u8 = 0;
    let mut v___x_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8680_: u8 = 0;
    let mut v_unused_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8688_: usize = 0;
    let mut v___x_8689_: usize = 0;
    let mut v___x_8690_: u8 = 0;
    let mut v___x_8691_: u8 = 0;
    let mut v_isSharedCheck_8692_: u8 = 0;
    let mut v___x_8693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_8695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_8696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8706_: u8 = 0;
    let mut v___y_8708_: u8 = 0;
    let mut v___x_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8711_: u8 = 0;
    let mut v___x_8713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8718_: u8 = 0;
    let mut v_unused_8719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8723_: usize = 0;
    let mut v___x_8724_: usize = 0;
    let mut v___x_8725_: u8 = 0;
    let mut v___x_8727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8728_: u8 = 0;
    let mut v___x_8730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8735_: u8 = 0;
    let mut v_unused_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8740_: usize = 0;
    let mut v___x_8741_: usize = 0;
    let mut v___x_8742_: u8 = 0;
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8745_: u8 = 0;
    let mut v___x_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8752_: u8 = 0;
    let mut v_unused_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: usize = 0;
    let mut v___x_8761_: usize = 0;
    let mut v___x_8762_: u8 = 0;
    let mut v___x_8763_: u8 = 0;
    let mut v_isSharedCheck_8764_: u8 = 0;
    let mut v___x_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8782_: u8 = 0;
    let mut v___y_8784_: u8 = 0;
    let mut v___x_8786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8787_: u8 = 0;
    let mut v___x_8789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8794_: u8 = 0;
    let mut v_unused_8795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8801_: u8 = 0;
    let mut v___x_8803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8804_: u8 = 0;
    let mut v___x_8806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8811_: u8 = 0;
    let mut v_unused_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8818_: usize = 0;
    let mut v___x_8819_: usize = 0;
    let mut v___x_8820_: u8 = 0;
    let mut v___x_8822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8823_: u8 = 0;
    let mut v___x_8825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8830_: u8 = 0;
    let mut v_unused_8831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: usize = 0;
    let mut v___x_8838_: usize = 0;
    let mut v___x_8839_: u8 = 0;
    let mut v___x_8841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8842_: u8 = 0;
    let mut v___x_8844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8849_: u8 = 0;
    let mut v_unused_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8856_: usize = 0;
    let mut v___x_8857_: usize = 0;
    let mut v___x_8858_: u8 = 0;
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8861_: u8 = 0;
    let mut v___x_8863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8868_: u8 = 0;
    let mut v_unused_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: usize = 0;
    let mut v___x_8879_: usize = 0;
    let mut v___x_8880_: u8 = 0;
    let mut v___x_8881_: u8 = 0;
    let mut v_isSharedCheck_8882_: u8 = 0;
    let mut v___x_8883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8894_: u8 = 0;
    let mut v___y_8896_: u8 = 0;
    let mut v___x_8898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8899_: u8 = 0;
    let mut v___x_8901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8906_: u8 = 0;
    let mut v_unused_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8910_: usize = 0;
    let mut v___x_8911_: usize = 0;
    let mut v___x_8912_: u8 = 0;
    let mut v___x_8914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8915_: u8 = 0;
    let mut v___x_8917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8922_: u8 = 0;
    let mut v_unused_8923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8929_: usize = 0;
    let mut v___x_8930_: usize = 0;
    let mut v___x_8931_: u8 = 0;
    let mut v___x_8932_: u8 = 0;
    let mut v_isSharedCheck_8933_: u8 = 0;
    let mut v___x_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_8936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_8937_: u8 = 0;
    let mut v_persistent_8938_: u8 = 0;
    let mut v_k_8939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8946_: u8 = 0;
    let mut v___y_8948_: u8 = 0;
    let mut v___x_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8951_: u8 = 0;
    let mut v___x_8953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8958_: u8 = 0;
    let mut v_unused_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8962_: usize = 0;
    let mut v___x_8963_: usize = 0;
    let mut v___x_8964_: u8 = 0;
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8967_: u8 = 0;
    let mut v___x_8969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8974_: u8 = 0;
    let mut v_unused_8975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_8977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8981_: usize = 0;
    let mut v___x_8982_: usize = 0;
    let mut v___x_8983_: u8 = 0;
    let mut v___x_8984_: u8 = 0;
    let mut v_isSharedCheck_8985_: u8 = 0;
    let mut v___x_8986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_8988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_8989_: u8 = 0;
    let mut v_persistent_8990_: u8 = 0;
    let mut v_objs_x3f_8991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_8992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8999_: u8 = 0;
    let mut v___y_9001_: u8 = 0;
    let mut v___x_9003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9004_: u8 = 0;
    let mut v___x_9006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9011_: u8 = 0;
    let mut v_unused_9012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9016_: usize = 0;
    let mut v___x_9017_: u8 = 0;
    let mut v___x_9019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9020_: u8 = 0;
    let mut v___x_9022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9027_: u8 = 0;
    let mut v_unused_9028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9032_: usize = 0;
    let mut v___x_9033_: usize = 0;
    let mut v___x_9034_: u8 = 0;
    let mut v___x_9036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9037_: u8 = 0;
    let mut v___x_9039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9044_: u8 = 0;
    let mut v_unused_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9052_: usize = 0;
    let mut v___x_9053_: usize = 0;
    let mut v___x_9054_: u8 = 0;
    let mut v___x_9055_: u8 = 0;
    let mut v_isSharedCheck_9056_: u8 = 0;
    let mut v___x_9057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9066_: u8 = 0;
    let mut v___y_9068_: u8 = 0;
    let mut v___x_9070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9071_: u8 = 0;
    let mut v___x_9073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9078_: u8 = 0;
    let mut v_unused_9079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_9080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9084_: usize = 0;
    let mut v___x_9085_: usize = 0;
    let mut v___x_9086_: u8 = 0;
    let mut v___x_9087_: usize = 0;
    let mut v___x_9088_: usize = 0;
    let mut v___x_9089_: u8 = 0;
    let mut v_isSharedCheck_9090_: u8 = 0;
    let mut v___x_9091_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_8363_) {
                0 => {
                    v_decl_8370_ = lean_ctor_get(v_code_8363_, 0);
                    v_k_8371_ = lean_ctor_get(v_code_8363_, 1);
                    lean_inc_ref(v_decl_8370_);
                    v___x_8372_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2___redArg(v_pu_8361_, v_t_8362_, v_decl_8370_, v_a_8364_, v_a_8366_);
                    if lean_obj_tag(v___x_8372_) == 0 {
                        v_a_8373_ = lean_ctor_get(v___x_8372_, 0);
                        lean_inc(v_a_8373_);
                        lean_dec_ref_known(v___x_8372_, 1);
                        lean_inc_ref(v_k_8371_);
                        v___x_8374_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8371_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8374_) == 0 {
                            v_a_8375_ = lean_ctor_get(v___x_8374_, 0);
                            v_isSharedCheck_8402_ = (!lean_is_exclusive(v___x_8374_)) as u8;
                            if v_isSharedCheck_8402_ == 0 {
                                v___x_8377_ = v___x_8374_;
                                v_isShared_8378_ = v_isSharedCheck_8402_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_8375_);
                                lean_dec(v___x_8374_);
                                v___x_8377_ = lean_box(0);
                                v_isShared_8378_ = v_isSharedCheck_8402_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8373_);
                            lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8374_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8403_ = lean_ctor_get(v___x_8372_, 0);
                        v_isSharedCheck_8410_ = (!lean_is_exclusive(v___x_8372_)) as u8;
                        if v_isSharedCheck_8410_ == 0 {
                            v___x_8405_ = v___x_8372_;
                            v_isShared_8406_ = v_isSharedCheck_8410_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_8403_);
                            lean_dec(v___x_8372_);
                            v___x_8405_ = lean_box(0);
                            v_isShared_8406_ = v_isSharedCheck_8410_;
                            state = 7;
                            continue;
                        }
                    }
                }
                1 => {
                    v_decl_8411_ = lean_ctor_get(v_code_8363_, 0);
                    v_k_8412_ = lean_ctor_get(v_code_8363_, 1);
                    lean_inc_ref(v_decl_8411_);
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
                    if lean_obj_tag(v___x_8413_) == 0 {
                        v_a_8414_ = lean_ctor_get(v___x_8413_, 0);
                        lean_inc(v_a_8414_);
                        lean_dec_ref_known(v___x_8413_, 1);
                        lean_inc_ref(v_k_8412_);
                        v___x_8415_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8412_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8415_) == 0 {
                            v_a_8416_ = lean_ctor_get(v___x_8415_, 0);
                            v_isSharedCheck_8443_ = (!lean_is_exclusive(v___x_8415_)) as u8;
                            if v_isSharedCheck_8443_ == 0 {
                                v___x_8418_ = v___x_8415_;
                                v_isShared_8419_ = v_isSharedCheck_8443_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_8416_);
                                lean_dec(v___x_8415_);
                                v___x_8418_ = lean_box(0);
                                v_isShared_8419_ = v_isSharedCheck_8443_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8414_);
                            lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8415_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8444_ = lean_ctor_get(v___x_8413_, 0);
                        v_isSharedCheck_8451_ = (!lean_is_exclusive(v___x_8413_)) as u8;
                        if v_isSharedCheck_8451_ == 0 {
                            v___x_8446_ = v___x_8413_;
                            v_isShared_8447_ = v_isSharedCheck_8451_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_8444_);
                            lean_dec(v___x_8413_);
                            v___x_8446_ = lean_box(0);
                            v_isShared_8447_ = v_isSharedCheck_8451_;
                            state = 15;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_8452_ = lean_ctor_get(v_code_8363_, 0);
                    v_k_8453_ = lean_ctor_get(v_code_8363_, 1);
                    lean_inc_ref(v_decl_8452_);
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
                    if lean_obj_tag(v___x_8454_) == 0 {
                        v_a_8455_ = lean_ctor_get(v___x_8454_, 0);
                        lean_inc(v_a_8455_);
                        lean_dec_ref_known(v___x_8454_, 1);
                        lean_inc_ref(v_k_8453_);
                        v___x_8456_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8453_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8456_) == 0 {
                            v_a_8457_ = lean_ctor_get(v___x_8456_, 0);
                            v_isSharedCheck_8484_ = (!lean_is_exclusive(v___x_8456_)) as u8;
                            if v_isSharedCheck_8484_ == 0 {
                                v___x_8459_ = v___x_8456_;
                                v_isShared_8460_ = v_isSharedCheck_8484_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_8457_);
                                lean_dec(v___x_8456_);
                                v___x_8459_ = lean_box(0);
                                v_isShared_8460_ = v_isSharedCheck_8484_;
                                state = 17;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8455_);
                            lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_8456_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 2);
                        v_a_8485_ = lean_ctor_get(v___x_8454_, 0);
                        v_isSharedCheck_8492_ = (!lean_is_exclusive(v___x_8454_)) as u8;
                        if v_isSharedCheck_8492_ == 0 {
                            v___x_8487_ = v___x_8454_;
                            v_isShared_8488_ = v_isSharedCheck_8492_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_8485_);
                            lean_dec(v___x_8454_);
                            v___x_8487_ = lean_box(0);
                            v_isShared_8488_ = v_isSharedCheck_8492_;
                            state = 23;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_8493_ = lean_ctor_get(v_code_8363_, 0);
                    v_args_8494_ = lean_ctor_get(v_code_8363_, 1);
                    lean_inc(v_fvarId_8493_);
                    v___x_8495_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8493_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8495_) == 0 {
                        v_fvarId_8496_ = lean_ctor_get(v___x_8495_, 0);
                        lean_inc(v_fvarId_8496_);
                        lean_dec_ref_known(v___x_8495_, 1);
                        lean_inc_ref(v_args_8494_);
                        v___x_8497_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3___redArg(v_pu_8361_, v_t_8362_, v_args_8494_, v_a_8364_);
                        if lean_obj_tag(v___x_8497_) == 0 {
                            v_a_8498_ = lean_ctor_get(v___x_8497_, 0);
                            v_isSharedCheck_8523_ = (!lean_is_exclusive(v___x_8497_)) as u8;
                            if v_isSharedCheck_8523_ == 0 {
                                v___x_8500_ = v___x_8497_;
                                v_isShared_8501_ = v_isSharedCheck_8523_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_8498_);
                                lean_dec(v___x_8497_);
                                v___x_8500_ = lean_box(0);
                                v_isShared_8501_ = v_isSharedCheck_8523_;
                                state = 25;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_8496_);
                            lean_dec_ref_known(v_code_8363_, 2);
                            v_a_8524_ = lean_ctor_get(v___x_8497_, 0);
                            v_isSharedCheck_8531_ = (!lean_is_exclusive(v___x_8497_)) as u8;
                            if v_isSharedCheck_8531_ == 0 {
                                v___x_8526_ = v___x_8497_;
                                v_isShared_8527_ = v_isSharedCheck_8531_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_a_8524_);
                                lean_dec(v___x_8497_);
                                v___x_8526_ = lean_box(0);
                                v_isShared_8527_ = v_isSharedCheck_8531_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 2);
                        v___x_8532_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8532_;
                    }
                }
                4 => {
                    v_cases_8533_ = lean_ctor_get(v_code_8363_, 0);
                    lean_inc_ref(v_cases_8533_);
                    v_typeName_8534_ = lean_ctor_get(v_cases_8533_, 0);
                    v_resultType_8535_ = lean_ctor_get(v_cases_8533_, 1);
                    v_discr_8536_ = lean_ctor_get(v_cases_8533_, 2);
                    v_alts_8537_ = lean_ctor_get(v_cases_8533_, 3);
                    v_isSharedCheck_8584_ = (!lean_is_exclusive(v_cases_8533_)) as u8;
                    if v_isSharedCheck_8584_ == 0 {
                        v___x_8539_ = v_cases_8533_;
                        v_isShared_8540_ = v_isSharedCheck_8584_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_alts_8537_);
                        lean_inc(v_discr_8536_);
                        lean_inc(v_resultType_8535_);
                        lean_inc(v_typeName_8534_);
                        lean_dec(v_cases_8533_);
                        v___x_8539_ = lean_box(0);
                        v_isShared_8540_ = v_isSharedCheck_8584_;
                        state = 33;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_8585_ = lean_ctor_get(v_code_8363_, 0);
                    lean_inc(v_fvarId_8585_);
                    v___x_8586_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8585_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8586_) == 0 {
                        v_fvarId_8587_ = lean_ctor_get(v___x_8586_, 0);
                        v_isSharedCheck_8606_ = (!lean_is_exclusive(v___x_8586_)) as u8;
                        if v_isSharedCheck_8606_ == 0 {
                            v___x_8589_ = v___x_8586_;
                            v_isShared_8590_ = v_isSharedCheck_8606_;
                            state = 43;
                            continue;
                        } else {
                            lean_inc(v_fvarId_8587_);
                            lean_dec(v___x_8586_);
                            v___x_8589_ = lean_box(0);
                            v_isShared_8590_ = v_isSharedCheck_8606_;
                            state = 43;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 1);
                        v___x_8607_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8607_;
                    }
                }
                6 => {
                    v_type_8608_ = lean_ctor_get(v_code_8363_, 0);
                    lean_inc_ref(v_type_8608_);
                    v___x_8609_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8361_, v_a_8364_, v_t_8362_, v_type_8608_);
                    v___x_8610_ = lean_ptr_addr(v_type_8608_);
                    v___x_8611_ = lean_ptr_addr(v___x_8609_);
                    v___x_8612_ = lean_usize_dec_eq(v___x_8610_, v___x_8611_);
                    if v___x_8612_ == 0 {
                        v_isSharedCheck_8620_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8620_ == 0 {
                            v_unused_8621_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8621_);
                            v___x_8614_ = v_code_8363_;
                            v_isShared_8615_ = v_isSharedCheck_8620_;
                            state = 48;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8614_ = lean_box(0);
                            v_isShared_8615_ = v_isSharedCheck_8620_;
                            state = 48;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_8609_);
                        v___x_8622_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_8622_, 0, v_code_8363_);
                        return v___x_8622_;
                    }
                }
                7 => {
                    v_fvarId_8623_ = lean_ctor_get(v_code_8363_, 0);
                    v_i_8624_ = lean_ctor_get(v_code_8363_, 1);
                    v_y_8625_ = lean_ctor_get(v_code_8363_, 2);
                    v_k_8626_ = lean_ctor_get(v_code_8363_, 3);
                    lean_inc(v_fvarId_8623_);
                    v___x_8627_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8623_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8627_) == 0 {
                        v_fvarId_8628_ = lean_ctor_get(v___x_8627_, 0);
                        lean_inc(v_fvarId_8628_);
                        lean_dec_ref_known(v___x_8627_, 1);
                        lean_inc(v_y_8625_);
                        v___x_8629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v_pu_8361_, v_a_8364_, v_y_8625_, v_t_8362_);
                        lean_inc_ref(v_k_8626_);
                        v___x_8630_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8626_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8630_) == 0 {
                            v_a_8631_ = lean_ctor_get(v___x_8630_, 0);
                            v_isSharedCheck_8692_ = (!lean_is_exclusive(v___x_8630_)) as u8;
                            if v_isSharedCheck_8692_ == 0 {
                                v___x_8633_ = v___x_8630_;
                                v_isShared_8634_ = v_isSharedCheck_8692_;
                                state = 50;
                                continue;
                            } else {
                                lean_inc(v_a_8631_);
                                lean_dec(v___x_8630_);
                                v___x_8633_ = lean_box(0);
                                v_isShared_8634_ = v_isSharedCheck_8692_;
                                state = 50;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_8629_);
                            lean_dec(v_fvarId_8628_);
                            lean_dec_ref_known(v_code_8363_, 4);
                            return v___x_8630_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 4);
                        v___x_8693_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8693_;
                    }
                }
                8 => {
                    v_fvarId_8694_ = lean_ctor_get(v_code_8363_, 0);
                    v_i_8695_ = lean_ctor_get(v_code_8363_, 1);
                    v_y_8696_ = lean_ctor_get(v_code_8363_, 2);
                    v_k_8697_ = lean_ctor_get(v_code_8363_, 3);
                    lean_inc(v_fvarId_8694_);
                    v___x_8698_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8694_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8698_) == 0 {
                        v_fvarId_8699_ = lean_ctor_get(v___x_8698_, 0);
                        lean_inc(v_fvarId_8699_);
                        lean_dec_ref_known(v___x_8698_, 1);
                        lean_inc(v_y_8696_);
                        v___x_8700_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_a_8364_, v_y_8696_, v_t_8362_,
                        );
                        if lean_obj_tag(v___x_8700_) == 0 {
                            v_fvarId_8701_ = lean_ctor_get(v___x_8700_, 0);
                            lean_inc(v_fvarId_8701_);
                            lean_dec_ref_known(v___x_8700_, 1);
                            lean_inc_ref(v_k_8697_);
                            v___x_8702_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8361_, v_t_8362_, v_k_8697_, v_a_8364_, v_a_8365_, v_a_8366_,
                                v_a_8367_, v_a_8368_,
                            );
                            if lean_obj_tag(v___x_8702_) == 0 {
                                v_a_8703_ = lean_ctor_get(v___x_8702_, 0);
                                v_isSharedCheck_8764_ = (!lean_is_exclusive(v___x_8702_)) as u8;
                                if v_isSharedCheck_8764_ == 0 {
                                    v___x_8705_ = v___x_8702_;
                                    v_isShared_8706_ = v_isSharedCheck_8764_;
                                    state = 62;
                                    continue;
                                } else {
                                    lean_inc(v_a_8703_);
                                    lean_dec(v___x_8702_);
                                    v___x_8705_ = lean_box(0);
                                    v_isShared_8706_ = v_isSharedCheck_8764_;
                                    state = 62;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fvarId_8701_);
                                lean_dec(v_fvarId_8699_);
                                lean_dec_ref_known(v_code_8363_, 4);
                                return v___x_8702_;
                            }
                        } else {
                            lean_dec(v_fvarId_8699_);
                            lean_dec_ref_known(v_code_8363_, 4);
                            v___x_8765_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                            );
                            return v___x_8765_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 4);
                        v___x_8766_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8766_;
                    }
                }
                9 => {
                    v_fvarId_8767_ = lean_ctor_get(v_code_8363_, 0);
                    v_i_8768_ = lean_ctor_get(v_code_8363_, 1);
                    v_offset_8769_ = lean_ctor_get(v_code_8363_, 2);
                    v_y_8770_ = lean_ctor_get(v_code_8363_, 3);
                    v_ty_8771_ = lean_ctor_get(v_code_8363_, 4);
                    v_k_8772_ = lean_ctor_get(v_code_8363_, 5);
                    lean_inc(v_fvarId_8767_);
                    v___x_8773_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8767_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8773_) == 0 {
                        v_fvarId_8774_ = lean_ctor_get(v___x_8773_, 0);
                        lean_inc(v_fvarId_8774_);
                        lean_dec_ref_known(v___x_8773_, 1);
                        lean_inc(v_y_8770_);
                        v___x_8775_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                            v_a_8364_, v_y_8770_, v_t_8362_,
                        );
                        if lean_obj_tag(v___x_8775_) == 0 {
                            v_fvarId_8776_ = lean_ctor_get(v___x_8775_, 0);
                            lean_inc(v_fvarId_8776_);
                            lean_dec_ref_known(v___x_8775_, 1);
                            lean_inc_ref(v_ty_8771_);
                            v___x_8777_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_8361_, v_a_8364_, v_t_8362_, v_ty_8771_);
                            lean_inc_ref(v_k_8772_);
                            v___x_8778_ = l_Lean_Compiler_LCNF_normCodeImp(
                                v_pu_8361_, v_t_8362_, v_k_8772_, v_a_8364_, v_a_8365_, v_a_8366_,
                                v_a_8367_, v_a_8368_,
                            );
                            if lean_obj_tag(v___x_8778_) == 0 {
                                v_a_8779_ = lean_ctor_get(v___x_8778_, 0);
                                v_isSharedCheck_8882_ = (!lean_is_exclusive(v___x_8778_)) as u8;
                                if v_isSharedCheck_8882_ == 0 {
                                    v___x_8781_ = v___x_8778_;
                                    v_isShared_8782_ = v_isSharedCheck_8882_;
                                    state = 74;
                                    continue;
                                } else {
                                    lean_inc(v_a_8779_);
                                    lean_dec(v___x_8778_);
                                    v___x_8781_ = lean_box(0);
                                    v_isShared_8782_ = v_isSharedCheck_8882_;
                                    state = 74;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_8777_);
                                lean_dec(v_fvarId_8776_);
                                lean_dec(v_fvarId_8774_);
                                lean_dec_ref_known(v_code_8363_, 6);
                                return v___x_8778_;
                            }
                        } else {
                            lean_dec(v_fvarId_8774_);
                            lean_dec_ref_known(v_code_8363_, 6);
                            v___x_8883_ = l_Lean_Compiler_LCNF_mkReturnErased(
                                v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                            );
                            return v___x_8883_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 6);
                        v___x_8884_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8884_;
                    }
                }
                10 => {
                    v_fvarId_8885_ = lean_ctor_get(v_code_8363_, 0);
                    v_cidx_8886_ = lean_ctor_get(v_code_8363_, 1);
                    v_k_8887_ = lean_ctor_get(v_code_8363_, 2);
                    lean_inc(v_fvarId_8885_);
                    v___x_8888_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8885_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8888_) == 0 {
                        v_fvarId_8889_ = lean_ctor_get(v___x_8888_, 0);
                        lean_inc(v_fvarId_8889_);
                        lean_dec_ref_known(v___x_8888_, 1);
                        lean_inc_ref(v_k_8887_);
                        v___x_8890_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8887_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8890_) == 0 {
                            v_a_8891_ = lean_ctor_get(v___x_8890_, 0);
                            v_isSharedCheck_8933_ = (!lean_is_exclusive(v___x_8890_)) as u8;
                            if v_isSharedCheck_8933_ == 0 {
                                v___x_8893_ = v___x_8890_;
                                v_isShared_8894_ = v_isSharedCheck_8933_;
                                state = 92;
                                continue;
                            } else {
                                lean_inc(v_a_8891_);
                                lean_dec(v___x_8890_);
                                v___x_8893_ = lean_box(0);
                                v_isShared_8894_ = v_isSharedCheck_8933_;
                                state = 92;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_8889_);
                            lean_dec_ref_known(v_code_8363_, 3);
                            return v___x_8890_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 3);
                        v___x_8934_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8934_;
                    }
                }
                11 => {
                    v_fvarId_8935_ = lean_ctor_get(v_code_8363_, 0);
                    v_n_8936_ = lean_ctor_get(v_code_8363_, 1);
                    v_check_8937_ = lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_8938_ = lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_8939_ = lean_ctor_get(v_code_8363_, 2);
                    lean_inc(v_fvarId_8935_);
                    v___x_8940_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8935_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8940_) == 0 {
                        v_fvarId_8941_ = lean_ctor_get(v___x_8940_, 0);
                        lean_inc(v_fvarId_8941_);
                        lean_dec_ref_known(v___x_8940_, 1);
                        lean_inc_ref(v_k_8939_);
                        v___x_8942_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8939_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8942_) == 0 {
                            v_a_8943_ = lean_ctor_get(v___x_8942_, 0);
                            v_isSharedCheck_8985_ = (!lean_is_exclusive(v___x_8942_)) as u8;
                            if v_isSharedCheck_8985_ == 0 {
                                v___x_8945_ = v___x_8942_;
                                v_isShared_8946_ = v_isSharedCheck_8985_;
                                state = 101;
                                continue;
                            } else {
                                lean_inc(v_a_8943_);
                                lean_dec(v___x_8942_);
                                v___x_8945_ = lean_box(0);
                                v_isShared_8946_ = v_isSharedCheck_8985_;
                                state = 101;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_8941_);
                            lean_dec_ref_known(v_code_8363_, 3);
                            return v___x_8942_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 3);
                        v___x_8986_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_8986_;
                    }
                }
                12 => {
                    v_fvarId_8987_ = lean_ctor_get(v_code_8363_, 0);
                    v_n_8988_ = lean_ctor_get(v_code_8363_, 1);
                    v_check_8989_ = lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    v_persistent_8990_ = lean_ctor_get_uint8(
                        v_code_8363_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_8991_ = lean_ctor_get(v_code_8363_, 2);
                    v_k_8992_ = lean_ctor_get(v_code_8363_, 3);
                    lean_inc(v_fvarId_8987_);
                    v___x_8993_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_8987_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_8993_) == 0 {
                        v_fvarId_8994_ = lean_ctor_get(v___x_8993_, 0);
                        lean_inc(v_fvarId_8994_);
                        lean_dec_ref_known(v___x_8993_, 1);
                        lean_inc_ref(v_k_8992_);
                        v___x_8995_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_8992_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_8995_) == 0 {
                            v_a_8996_ = lean_ctor_get(v___x_8995_, 0);
                            v_isSharedCheck_9056_ = (!lean_is_exclusive(v___x_8995_)) as u8;
                            if v_isSharedCheck_9056_ == 0 {
                                v___x_8998_ = v___x_8995_;
                                v_isShared_8999_ = v_isSharedCheck_9056_;
                                state = 110;
                                continue;
                            } else {
                                lean_inc(v_a_8996_);
                                lean_dec(v___x_8995_);
                                v___x_8998_ = lean_box(0);
                                v_isShared_8999_ = v_isSharedCheck_9056_;
                                state = 110;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_8994_);
                            lean_dec_ref_known(v_code_8363_, 4);
                            return v___x_8995_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 4);
                        v___x_9057_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                        );
                        return v___x_9057_;
                    }
                }
                _ => {
                    v_fvarId_9058_ = lean_ctor_get(v_code_8363_, 0);
                    v_k_9059_ = lean_ctor_get(v_code_8363_, 1);
                    lean_inc(v_fvarId_9058_);
                    v___x_9060_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_a_8364_,
                        v_fvarId_9058_,
                        v_t_8362_,
                    );
                    if lean_obj_tag(v___x_9060_) == 0 {
                        v_fvarId_9061_ = lean_ctor_get(v___x_9060_, 0);
                        lean_inc(v_fvarId_9061_);
                        lean_dec_ref_known(v___x_9060_, 1);
                        lean_inc_ref(v_k_9059_);
                        v___x_9062_ = l_Lean_Compiler_LCNF_normCodeImp(
                            v_pu_8361_, v_t_8362_, v_k_9059_, v_a_8364_, v_a_8365_, v_a_8366_,
                            v_a_8367_, v_a_8368_,
                        );
                        if lean_obj_tag(v___x_9062_) == 0 {
                            v_a_9063_ = lean_ctor_get(v___x_9062_, 0);
                            v_isSharedCheck_9090_ = (!lean_is_exclusive(v___x_9062_)) as u8;
                            if v_isSharedCheck_9090_ == 0 {
                                v___x_9065_ = v___x_9062_;
                                v_isShared_9066_ = v_isSharedCheck_9090_;
                                state = 122;
                                continue;
                            } else {
                                lean_inc(v_a_9063_);
                                lean_dec(v___x_9062_);
                                v___x_9065_ = lean_box(0);
                                v_isShared_9066_ = v_isSharedCheck_9090_;
                                state = 122;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_9061_);
                            lean_dec_ref_known(v_code_8363_, 2);
                            return v___x_9062_;
                        }
                    } else {
                        lean_dec_ref_known(v_code_8363_, 2);
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
                    v_isSharedCheck_8390_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8390_ == 0 {
                        v_unused_8391_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8391_);
                        v_unused_8392_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8392_);
                        v___x_8382_ = v_code_8363_;
                        v_isShared_8383_ = v_isSharedCheck_8390_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8382_ = lean_box(0);
                        v_isShared_8383_ = v_isSharedCheck_8390_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_8375_);
                    lean_dec(v_a_8373_);
                    if v_isShared_8378_ == 0 {
                        lean_ctor_set(v___x_8377_, 0, v_code_8363_);
                        v___x_8394_ = v___x_8377_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_8395_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8395_, 0, v_code_8363_);
                        v___x_8394_ = v_reuseFailAlloc_8395_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_8383_ == 0 {
                    lean_ctor_set(v___x_8382_, 1, v_a_8375_);
                    lean_ctor_set(v___x_8382_, 0, v_a_8373_);
                    v___x_8385_ = v___x_8382_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8389_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8389_, 0, v_a_8373_);
                    lean_ctor_set(v_reuseFailAlloc_8389_, 1, v_a_8375_);
                    v___x_8385_ = v_reuseFailAlloc_8389_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8378_ == 0 {
                    lean_ctor_set(v___x_8377_, 0, v___x_8385_);
                    v___x_8387_ = v___x_8377_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8388_, 0, v___x_8385_);
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
                    v_reuseFailAlloc_8409_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8409_, 0, v_a_8403_);
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
                    v_isSharedCheck_8431_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8431_ == 0 {
                        v_unused_8432_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8432_);
                        v_unused_8433_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8433_);
                        v___x_8423_ = v_code_8363_;
                        v_isShared_8424_ = v_isSharedCheck_8431_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8423_ = lean_box(0);
                        v_isShared_8424_ = v_isSharedCheck_8431_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_a_8416_);
                    lean_dec(v_a_8414_);
                    if v_isShared_8419_ == 0 {
                        lean_ctor_set(v___x_8418_, 0, v_code_8363_);
                        v___x_8435_ = v___x_8418_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_8436_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8436_, 0, v_code_8363_);
                        v___x_8435_ = v_reuseFailAlloc_8436_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_8424_ == 0 {
                    lean_ctor_set(v___x_8423_, 1, v_a_8416_);
                    lean_ctor_set(v___x_8423_, 0, v_a_8414_);
                    v___x_8426_ = v___x_8423_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8430_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8430_, 0, v_a_8414_);
                    lean_ctor_set(v_reuseFailAlloc_8430_, 1, v_a_8416_);
                    v___x_8426_ = v_reuseFailAlloc_8430_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_8419_ == 0 {
                    lean_ctor_set(v___x_8418_, 0, v___x_8426_);
                    v___x_8428_ = v___x_8418_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8429_, 0, v___x_8426_);
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
                    v_reuseFailAlloc_8450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8450_, 0, v_a_8444_);
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
                    v_isSharedCheck_8472_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8472_ == 0 {
                        v_unused_8473_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8473_);
                        v_unused_8474_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8474_);
                        v___x_8464_ = v_code_8363_;
                        v_isShared_8465_ = v_isSharedCheck_8472_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8464_ = lean_box(0);
                        v_isShared_8465_ = v_isSharedCheck_8472_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v_a_8457_);
                    lean_dec(v_a_8455_);
                    if v_isShared_8460_ == 0 {
                        lean_ctor_set(v___x_8459_, 0, v_code_8363_);
                        v___x_8476_ = v___x_8459_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_8477_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8477_, 0, v_code_8363_);
                        v___x_8476_ = v_reuseFailAlloc_8477_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_8465_ == 0 {
                    lean_ctor_set(v___x_8464_, 1, v_a_8457_);
                    lean_ctor_set(v___x_8464_, 0, v_a_8455_);
                    v___x_8467_ = v___x_8464_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8471_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8471_, 0, v_a_8455_);
                    lean_ctor_set(v_reuseFailAlloc_8471_, 1, v_a_8457_);
                    v___x_8467_ = v_reuseFailAlloc_8471_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_8460_ == 0 {
                    lean_ctor_set(v___x_8459_, 0, v___x_8467_);
                    v___x_8469_ = v___x_8459_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8470_, 0, v___x_8467_);
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
                    v_reuseFailAlloc_8491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8491_, 0, v_a_8485_);
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
                    v_isSharedCheck_8513_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8513_ == 0 {
                        v_unused_8514_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8514_);
                        v_unused_8515_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8515_);
                        v___x_8505_ = v_code_8363_;
                        v_isShared_8506_ = v_isSharedCheck_8513_;
                        state = 27;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8505_ = lean_box(0);
                        v_isShared_8506_ = v_isSharedCheck_8513_;
                        state = 27;
                        continue;
                    }
                } else {
                    lean_dec(v_a_8498_);
                    lean_dec(v_fvarId_8496_);
                    if v_isShared_8501_ == 0 {
                        lean_ctor_set(v___x_8500_, 0, v_code_8363_);
                        v___x_8517_ = v___x_8500_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_8518_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8518_, 0, v_code_8363_);
                        v___x_8517_ = v_reuseFailAlloc_8518_;
                        state = 30;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_8506_ == 0 {
                    lean_ctor_set(v___x_8505_, 1, v_a_8498_);
                    lean_ctor_set(v___x_8505_, 0, v_fvarId_8496_);
                    v___x_8508_ = v___x_8505_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_8512_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8512_, 0, v_fvarId_8496_);
                    lean_ctor_set(v_reuseFailAlloc_8512_, 1, v_a_8498_);
                    v___x_8508_ = v_reuseFailAlloc_8512_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_8501_ == 0 {
                    lean_ctor_set(v___x_8500_, 0, v___x_8508_);
                    v___x_8510_ = v___x_8500_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_8511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8511_, 0, v___x_8508_);
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
                    v_reuseFailAlloc_8530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8530_, 0, v_a_8524_);
                    v___x_8529_ = v_reuseFailAlloc_8530_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_8529_;
            }
            33 => {
                lean_inc_ref(v_resultType_8535_);
                v___x_8541_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v_pu_8361_,
                        v_a_8364_,
                        v_t_8362_,
                        v_resultType_8535_,
                    );
                lean_inc(v_discr_8536_);
                v___x_8542_ =
                    l_Lean_Compiler_LCNF_normFVarImp___redArg(v_a_8364_, v_discr_8536_, v_t_8362_);
                if lean_obj_tag(v___x_8542_) == 0 {
                    v_fvarId_8543_ = lean_ctor_get(v___x_8542_, 0);
                    v_isSharedCheck_8582_ = (!lean_is_exclusive(v___x_8542_)) as u8;
                    if v_isSharedCheck_8582_ == 0 {
                        v___x_8545_ = v___x_8542_;
                        v_isShared_8546_ = v_isSharedCheck_8582_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_fvarId_8543_);
                        lean_dec(v___x_8542_);
                        v___x_8545_ = lean_box(0);
                        v_isShared_8546_ = v_isSharedCheck_8582_;
                        state = 34;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_8541_);
                    lean_del_object(v___x_8539_);
                    lean_dec_ref(v_alts_8537_);
                    lean_dec(v_discr_8536_);
                    lean_dec_ref(v_resultType_8535_);
                    lean_dec(v_typeName_8534_);
                    lean_dec_ref_known(v_code_8363_, 1);
                    v___x_8583_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v_pu_8361_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_,
                    );
                    return v___x_8583_;
                }
            }
            34 => {
                v___x_8547_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_8537_);
                v___x_8548_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_8361_, v_t_8362_, v___x_8547_, v_alts_8537_, v_a_8364_, v_a_8365_, v_a_8366_, v_a_8367_, v_a_8368_);
                if lean_obj_tag(v___x_8548_) == 0 {
                    v_a_8549_ = lean_ctor_get(v___x_8548_, 0);
                    v_isSharedCheck_8573_ = (!lean_is_exclusive(v___x_8548_)) as u8;
                    if v_isSharedCheck_8573_ == 0 {
                        v___x_8551_ = v___x_8548_;
                        v_isShared_8552_ = v_isSharedCheck_8573_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_8549_);
                        lean_dec(v___x_8548_);
                        v___x_8551_ = lean_box(0);
                        v_isShared_8552_ = v_isSharedCheck_8573_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8545_);
                    lean_dec(v_fvarId_8543_);
                    lean_dec_ref(v___x_8541_);
                    lean_del_object(v___x_8539_);
                    lean_dec_ref(v_alts_8537_);
                    lean_dec(v_discr_8536_);
                    lean_dec_ref(v_resultType_8535_);
                    lean_dec(v_typeName_8534_);
                    lean_dec_ref_known(v_code_8363_, 1);
                    v_a_8574_ = lean_ctor_get(v___x_8548_, 0);
                    v_isSharedCheck_8581_ = (!lean_is_exclusive(v___x_8548_)) as u8;
                    if v_isSharedCheck_8581_ == 0 {
                        v___x_8576_ = v___x_8548_;
                        v_isShared_8577_ = v_isSharedCheck_8581_;
                        state = 41;
                        continue;
                    } else {
                        lean_inc(v_a_8574_);
                        lean_dec(v___x_8548_);
                        v___x_8576_ = lean_box(0);
                        v_isShared_8577_ = v_isSharedCheck_8581_;
                        state = 41;
                        continue;
                    }
                }
            }
            35 => {
                v___x_8567_ = lean_ptr_addr(v_alts_8537_);
                lean_dec_ref(v_alts_8537_);
                v___x_8568_ = lean_ptr_addr(v_a_8549_);
                v___x_8569_ = lean_usize_dec_eq(v___x_8567_, v___x_8568_);
                if v___x_8569_ == 0 {
                    lean_dec_ref(v_resultType_8535_);
                    v___y_8564_ = v___x_8569_;
                    state = 40;
                    continue;
                } else {
                    v___x_8570_ = lean_ptr_addr(v_resultType_8535_);
                    lean_dec_ref(v_resultType_8535_);
                    v___x_8571_ = lean_ptr_addr(v___x_8541_);
                    v___x_8572_ = lean_usize_dec_eq(v___x_8570_, v___x_8571_);
                    v___y_8564_ = v___x_8572_;
                    state = 40;
                    continue;
                }
            }
            36 => {
                if v_isShared_8540_ == 0 {
                    lean_ctor_set(v___x_8539_, 3, v_a_8549_);
                    lean_ctor_set(v___x_8539_, 2, v_fvarId_8543_);
                    lean_ctor_set(v___x_8539_, 1, v___x_8541_);
                    v___x_8555_ = v___x_8539_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8562_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8562_, 0, v_typeName_8534_);
                    lean_ctor_set(v_reuseFailAlloc_8562_, 1, v___x_8541_);
                    lean_ctor_set(v_reuseFailAlloc_8562_, 2, v_fvarId_8543_);
                    lean_ctor_set(v_reuseFailAlloc_8562_, 3, v_a_8549_);
                    v___x_8555_ = v_reuseFailAlloc_8562_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_8546_ == 0 {
                    lean_ctor_set_tag(v___x_8545_, 4);
                    lean_ctor_set(v___x_8545_, 0, v___x_8555_);
                    v___x_8557_ = v___x_8545_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_8561_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8561_, 0, v___x_8555_);
                    v___x_8557_ = v_reuseFailAlloc_8561_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                if v_isShared_8552_ == 0 {
                    lean_ctor_set(v___x_8551_, 0, v___x_8557_);
                    v___x_8559_ = v___x_8551_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_8560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8560_, 0, v___x_8557_);
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
                    lean_dec(v_discr_8536_);
                    lean_dec_ref_known(v_code_8363_, 1);
                    state = 36;
                    continue;
                } else {
                    v___x_8565_ = l_Lean_instBEqFVarId_beq(v_discr_8536_, v_fvarId_8543_);
                    lean_dec(v_discr_8536_);
                    if v___x_8565_ == 0 {
                        lean_dec_ref_known(v_code_8363_, 1);
                        state = 36;
                        continue;
                    } else {
                        lean_del_object(v___x_8551_);
                        lean_dec(v_a_8549_);
                        lean_del_object(v___x_8545_);
                        lean_dec(v_fvarId_8543_);
                        lean_dec_ref(v___x_8541_);
                        lean_del_object(v___x_8539_);
                        lean_dec(v_typeName_8534_);
                        v___x_8566_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_8566_, 0, v_code_8363_);
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
                    v_reuseFailAlloc_8580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8580_, 0, v_a_8574_);
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
                    v_isSharedCheck_8601_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8601_ == 0 {
                        v_unused_8602_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8602_);
                        v___x_8593_ = v_code_8363_;
                        v_isShared_8594_ = v_isSharedCheck_8601_;
                        state = 44;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8593_ = lean_box(0);
                        v_isShared_8594_ = v_isSharedCheck_8601_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_8587_);
                    if v_isShared_8590_ == 0 {
                        lean_ctor_set(v___x_8589_, 0, v_code_8363_);
                        v___x_8604_ = v___x_8589_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_8605_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_8605_, 0, v_code_8363_);
                        v___x_8604_ = v_reuseFailAlloc_8605_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_8594_ == 0 {
                    lean_ctor_set(v___x_8593_, 0, v_fvarId_8587_);
                    v___x_8596_ = v___x_8593_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_8600_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8600_, 0, v_fvarId_8587_);
                    v___x_8596_ = v_reuseFailAlloc_8600_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_8590_ == 0 {
                    lean_ctor_set(v___x_8589_, 0, v___x_8596_);
                    v___x_8598_ = v___x_8589_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_8599_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8599_, 0, v___x_8596_);
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
                    lean_ctor_set(v___x_8614_, 0, v___x_8609_);
                    v___x_8617_ = v___x_8614_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_8619_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8619_, 0, v___x_8609_);
                    v___x_8617_ = v_reuseFailAlloc_8619_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                v___x_8618_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8618_, 0, v___x_8617_);
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
                    lean_inc(v_i_8624_);
                    v_isSharedCheck_8646_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8646_ == 0 {
                        v_unused_8647_ = lean_ctor_get(v_code_8363_, 3);
                        lean_dec(v_unused_8647_);
                        v_unused_8648_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_8648_);
                        v_unused_8649_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8649_);
                        v_unused_8650_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8650_);
                        v___x_8638_ = v_code_8363_;
                        v_isShared_8639_ = v_isSharedCheck_8646_;
                        state = 52;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8638_ = lean_box(0);
                        v_isShared_8639_ = v_isSharedCheck_8646_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_8651_ = lean_ptr_addr(v_y_8625_);
                    v___x_8652_ = lean_ptr_addr(v___x_8629_);
                    v___x_8653_ = lean_usize_dec_eq(v___x_8651_, v___x_8652_);
                    if v___x_8653_ == 0 {
                        lean_inc(v_i_8624_);
                        v_isSharedCheck_8663_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8663_ == 0 {
                            v_unused_8664_ = lean_ctor_get(v_code_8363_, 3);
                            lean_dec(v_unused_8664_);
                            v_unused_8665_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_8665_);
                            v_unused_8666_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_8666_);
                            v_unused_8667_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8667_);
                            v___x_8655_ = v_code_8363_;
                            v_isShared_8656_ = v_isSharedCheck_8663_;
                            state = 55;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8655_ = lean_box(0);
                            v_isShared_8656_ = v_isSharedCheck_8663_;
                            state = 55;
                            continue;
                        }
                    } else {
                        v___x_8668_ = lean_ptr_addr(v_k_8626_);
                        v___x_8669_ = lean_ptr_addr(v_a_8631_);
                        v___x_8670_ = lean_usize_dec_eq(v___x_8668_, v___x_8669_);
                        if v___x_8670_ == 0 {
                            lean_inc(v_i_8624_);
                            v_isSharedCheck_8680_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8680_ == 0 {
                                v_unused_8681_ = lean_ctor_get(v_code_8363_, 3);
                                lean_dec(v_unused_8681_);
                                v_unused_8682_ = lean_ctor_get(v_code_8363_, 2);
                                lean_dec(v_unused_8682_);
                                v_unused_8683_ = lean_ctor_get(v_code_8363_, 1);
                                lean_dec(v_unused_8683_);
                                v_unused_8684_ = lean_ctor_get(v_code_8363_, 0);
                                lean_dec(v_unused_8684_);
                                v___x_8672_ = v_code_8363_;
                                v_isShared_8673_ = v_isSharedCheck_8680_;
                                state = 58;
                                continue;
                            } else {
                                lean_dec(v_code_8363_);
                                v___x_8672_ = lean_box(0);
                                v_isShared_8673_ = v_isSharedCheck_8680_;
                                state = 58;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8631_);
                            lean_dec(v___x_8629_);
                            lean_dec(v_fvarId_8628_);
                            if v_isShared_8634_ == 0 {
                                lean_ctor_set(v___x_8633_, 0, v_code_8363_);
                                v___x_8686_ = v___x_8633_;
                                state = 61;
                                continue;
                            } else {
                                v_reuseFailAlloc_8687_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_8687_, 0, v_code_8363_);
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
                    lean_ctor_set(v___x_8638_, 3, v_a_8631_);
                    lean_ctor_set(v___x_8638_, 2, v___x_8629_);
                    lean_ctor_set(v___x_8638_, 0, v_fvarId_8628_);
                    v___x_8641_ = v___x_8638_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_8645_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8645_, 0, v_fvarId_8628_);
                    lean_ctor_set(v_reuseFailAlloc_8645_, 1, v_i_8624_);
                    lean_ctor_set(v_reuseFailAlloc_8645_, 2, v___x_8629_);
                    lean_ctor_set(v_reuseFailAlloc_8645_, 3, v_a_8631_);
                    v___x_8641_ = v_reuseFailAlloc_8645_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_8634_ == 0 {
                    lean_ctor_set(v___x_8633_, 0, v___x_8641_);
                    v___x_8643_ = v___x_8633_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_8644_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8644_, 0, v___x_8641_);
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
                    lean_ctor_set(v___x_8655_, 3, v_a_8631_);
                    lean_ctor_set(v___x_8655_, 2, v___x_8629_);
                    lean_ctor_set(v___x_8655_, 0, v_fvarId_8628_);
                    v___x_8658_ = v___x_8655_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_8662_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8662_, 0, v_fvarId_8628_);
                    lean_ctor_set(v_reuseFailAlloc_8662_, 1, v_i_8624_);
                    lean_ctor_set(v_reuseFailAlloc_8662_, 2, v___x_8629_);
                    lean_ctor_set(v_reuseFailAlloc_8662_, 3, v_a_8631_);
                    v___x_8658_ = v_reuseFailAlloc_8662_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                if v_isShared_8634_ == 0 {
                    lean_ctor_set(v___x_8633_, 0, v___x_8658_);
                    v___x_8660_ = v___x_8633_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_8661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8661_, 0, v___x_8658_);
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
                    lean_ctor_set(v___x_8672_, 3, v_a_8631_);
                    lean_ctor_set(v___x_8672_, 2, v___x_8629_);
                    lean_ctor_set(v___x_8672_, 0, v_fvarId_8628_);
                    v___x_8675_ = v___x_8672_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_8679_ = lean_alloc_ctor(7, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8679_, 0, v_fvarId_8628_);
                    lean_ctor_set(v_reuseFailAlloc_8679_, 1, v_i_8624_);
                    lean_ctor_set(v_reuseFailAlloc_8679_, 2, v___x_8629_);
                    lean_ctor_set(v_reuseFailAlloc_8679_, 3, v_a_8631_);
                    v___x_8675_ = v_reuseFailAlloc_8679_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                if v_isShared_8634_ == 0 {
                    lean_ctor_set(v___x_8633_, 0, v___x_8675_);
                    v___x_8677_ = v___x_8633_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_8678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8678_, 0, v___x_8675_);
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
                    lean_inc(v_i_8695_);
                    v_isSharedCheck_8718_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8718_ == 0 {
                        v_unused_8719_ = lean_ctor_get(v_code_8363_, 3);
                        lean_dec(v_unused_8719_);
                        v_unused_8720_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_8720_);
                        v_unused_8721_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8721_);
                        v_unused_8722_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8722_);
                        v___x_8710_ = v_code_8363_;
                        v_isShared_8711_ = v_isSharedCheck_8718_;
                        state = 64;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8710_ = lean_box(0);
                        v_isShared_8711_ = v_isSharedCheck_8718_;
                        state = 64;
                        continue;
                    }
                } else {
                    v___x_8723_ = lean_ptr_addr(v_y_8696_);
                    v___x_8724_ = lean_ptr_addr(v_fvarId_8701_);
                    v___x_8725_ = lean_usize_dec_eq(v___x_8723_, v___x_8724_);
                    if v___x_8725_ == 0 {
                        lean_inc(v_i_8695_);
                        v_isSharedCheck_8735_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8735_ == 0 {
                            v_unused_8736_ = lean_ctor_get(v_code_8363_, 3);
                            lean_dec(v_unused_8736_);
                            v_unused_8737_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_8737_);
                            v_unused_8738_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_8738_);
                            v_unused_8739_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8739_);
                            v___x_8727_ = v_code_8363_;
                            v_isShared_8728_ = v_isSharedCheck_8735_;
                            state = 67;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8727_ = lean_box(0);
                            v_isShared_8728_ = v_isSharedCheck_8735_;
                            state = 67;
                            continue;
                        }
                    } else {
                        v___x_8740_ = lean_ptr_addr(v_k_8697_);
                        v___x_8741_ = lean_ptr_addr(v_a_8703_);
                        v___x_8742_ = lean_usize_dec_eq(v___x_8740_, v___x_8741_);
                        if v___x_8742_ == 0 {
                            lean_inc(v_i_8695_);
                            v_isSharedCheck_8752_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8752_ == 0 {
                                v_unused_8753_ = lean_ctor_get(v_code_8363_, 3);
                                lean_dec(v_unused_8753_);
                                v_unused_8754_ = lean_ctor_get(v_code_8363_, 2);
                                lean_dec(v_unused_8754_);
                                v_unused_8755_ = lean_ctor_get(v_code_8363_, 1);
                                lean_dec(v_unused_8755_);
                                v_unused_8756_ = lean_ctor_get(v_code_8363_, 0);
                                lean_dec(v_unused_8756_);
                                v___x_8744_ = v_code_8363_;
                                v_isShared_8745_ = v_isSharedCheck_8752_;
                                state = 70;
                                continue;
                            } else {
                                lean_dec(v_code_8363_);
                                v___x_8744_ = lean_box(0);
                                v_isShared_8745_ = v_isSharedCheck_8752_;
                                state = 70;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8703_);
                            lean_dec(v_fvarId_8701_);
                            lean_dec(v_fvarId_8699_);
                            if v_isShared_8706_ == 0 {
                                lean_ctor_set(v___x_8705_, 0, v_code_8363_);
                                v___x_8758_ = v___x_8705_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_8759_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_8759_, 0, v_code_8363_);
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
                    lean_ctor_set(v___x_8710_, 3, v_a_8703_);
                    lean_ctor_set(v___x_8710_, 2, v_fvarId_8701_);
                    lean_ctor_set(v___x_8710_, 0, v_fvarId_8699_);
                    v___x_8713_ = v___x_8710_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_8717_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8717_, 0, v_fvarId_8699_);
                    lean_ctor_set(v_reuseFailAlloc_8717_, 1, v_i_8695_);
                    lean_ctor_set(v_reuseFailAlloc_8717_, 2, v_fvarId_8701_);
                    lean_ctor_set(v_reuseFailAlloc_8717_, 3, v_a_8703_);
                    v___x_8713_ = v_reuseFailAlloc_8717_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                if v_isShared_8706_ == 0 {
                    lean_ctor_set(v___x_8705_, 0, v___x_8713_);
                    v___x_8715_ = v___x_8705_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_8716_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8716_, 0, v___x_8713_);
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
                    lean_ctor_set(v___x_8727_, 3, v_a_8703_);
                    lean_ctor_set(v___x_8727_, 2, v_fvarId_8701_);
                    lean_ctor_set(v___x_8727_, 0, v_fvarId_8699_);
                    v___x_8730_ = v___x_8727_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_8734_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8734_, 0, v_fvarId_8699_);
                    lean_ctor_set(v_reuseFailAlloc_8734_, 1, v_i_8695_);
                    lean_ctor_set(v_reuseFailAlloc_8734_, 2, v_fvarId_8701_);
                    lean_ctor_set(v_reuseFailAlloc_8734_, 3, v_a_8703_);
                    v___x_8730_ = v_reuseFailAlloc_8734_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_8706_ == 0 {
                    lean_ctor_set(v___x_8705_, 0, v___x_8730_);
                    v___x_8732_ = v___x_8705_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_8733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8733_, 0, v___x_8730_);
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
                    lean_ctor_set(v___x_8744_, 3, v_a_8703_);
                    lean_ctor_set(v___x_8744_, 2, v_fvarId_8701_);
                    lean_ctor_set(v___x_8744_, 0, v_fvarId_8699_);
                    v___x_8747_ = v___x_8744_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_8751_ = lean_alloc_ctor(8, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8751_, 0, v_fvarId_8699_);
                    lean_ctor_set(v_reuseFailAlloc_8751_, 1, v_i_8695_);
                    lean_ctor_set(v_reuseFailAlloc_8751_, 2, v_fvarId_8701_);
                    lean_ctor_set(v_reuseFailAlloc_8751_, 3, v_a_8703_);
                    v___x_8747_ = v_reuseFailAlloc_8751_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_8706_ == 0 {
                    lean_ctor_set(v___x_8705_, 0, v___x_8747_);
                    v___x_8749_ = v___x_8705_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_8750_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8750_, 0, v___x_8747_);
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
                    lean_inc(v_offset_8769_);
                    lean_inc(v_i_8768_);
                    v_isSharedCheck_8794_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8794_ == 0 {
                        v_unused_8795_ = lean_ctor_get(v_code_8363_, 5);
                        lean_dec(v_unused_8795_);
                        v_unused_8796_ = lean_ctor_get(v_code_8363_, 4);
                        lean_dec(v_unused_8796_);
                        v_unused_8797_ = lean_ctor_get(v_code_8363_, 3);
                        lean_dec(v_unused_8797_);
                        v_unused_8798_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_8798_);
                        v_unused_8799_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8799_);
                        v_unused_8800_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8800_);
                        v___x_8786_ = v_code_8363_;
                        v_isShared_8787_ = v_isSharedCheck_8794_;
                        state = 76;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8786_ = lean_box(0);
                        v_isShared_8787_ = v_isSharedCheck_8794_;
                        state = 76;
                        continue;
                    }
                } else {
                    v___x_8801_ = lean_nat_dec_eq(v_offset_8769_, v_offset_8769_);
                    if v___x_8801_ == 0 {
                        lean_inc(v_offset_8769_);
                        lean_inc(v_i_8768_);
                        v_isSharedCheck_8811_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8811_ == 0 {
                            v_unused_8812_ = lean_ctor_get(v_code_8363_, 5);
                            lean_dec(v_unused_8812_);
                            v_unused_8813_ = lean_ctor_get(v_code_8363_, 4);
                            lean_dec(v_unused_8813_);
                            v_unused_8814_ = lean_ctor_get(v_code_8363_, 3);
                            lean_dec(v_unused_8814_);
                            v_unused_8815_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_8815_);
                            v_unused_8816_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_8816_);
                            v_unused_8817_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8817_);
                            v___x_8803_ = v_code_8363_;
                            v_isShared_8804_ = v_isSharedCheck_8811_;
                            state = 79;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8803_ = lean_box(0);
                            v_isShared_8804_ = v_isSharedCheck_8811_;
                            state = 79;
                            continue;
                        }
                    } else {
                        v___x_8818_ = lean_ptr_addr(v_y_8770_);
                        v___x_8819_ = lean_ptr_addr(v_fvarId_8776_);
                        v___x_8820_ = lean_usize_dec_eq(v___x_8818_, v___x_8819_);
                        if v___x_8820_ == 0 {
                            lean_inc(v_offset_8769_);
                            lean_inc(v_i_8768_);
                            v_isSharedCheck_8830_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_8830_ == 0 {
                                v_unused_8831_ = lean_ctor_get(v_code_8363_, 5);
                                lean_dec(v_unused_8831_);
                                v_unused_8832_ = lean_ctor_get(v_code_8363_, 4);
                                lean_dec(v_unused_8832_);
                                v_unused_8833_ = lean_ctor_get(v_code_8363_, 3);
                                lean_dec(v_unused_8833_);
                                v_unused_8834_ = lean_ctor_get(v_code_8363_, 2);
                                lean_dec(v_unused_8834_);
                                v_unused_8835_ = lean_ctor_get(v_code_8363_, 1);
                                lean_dec(v_unused_8835_);
                                v_unused_8836_ = lean_ctor_get(v_code_8363_, 0);
                                lean_dec(v_unused_8836_);
                                v___x_8822_ = v_code_8363_;
                                v_isShared_8823_ = v_isSharedCheck_8830_;
                                state = 82;
                                continue;
                            } else {
                                lean_dec(v_code_8363_);
                                v___x_8822_ = lean_box(0);
                                v_isShared_8823_ = v_isSharedCheck_8830_;
                                state = 82;
                                continue;
                            }
                        } else {
                            v___x_8837_ = lean_ptr_addr(v_ty_8771_);
                            v___x_8838_ = lean_ptr_addr(v___x_8777_);
                            v___x_8839_ = lean_usize_dec_eq(v___x_8837_, v___x_8838_);
                            if v___x_8839_ == 0 {
                                lean_inc(v_offset_8769_);
                                lean_inc(v_i_8768_);
                                v_isSharedCheck_8849_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                                if v_isSharedCheck_8849_ == 0 {
                                    v_unused_8850_ = lean_ctor_get(v_code_8363_, 5);
                                    lean_dec(v_unused_8850_);
                                    v_unused_8851_ = lean_ctor_get(v_code_8363_, 4);
                                    lean_dec(v_unused_8851_);
                                    v_unused_8852_ = lean_ctor_get(v_code_8363_, 3);
                                    lean_dec(v_unused_8852_);
                                    v_unused_8853_ = lean_ctor_get(v_code_8363_, 2);
                                    lean_dec(v_unused_8853_);
                                    v_unused_8854_ = lean_ctor_get(v_code_8363_, 1);
                                    lean_dec(v_unused_8854_);
                                    v_unused_8855_ = lean_ctor_get(v_code_8363_, 0);
                                    lean_dec(v_unused_8855_);
                                    v___x_8841_ = v_code_8363_;
                                    v_isShared_8842_ = v_isSharedCheck_8849_;
                                    state = 85;
                                    continue;
                                } else {
                                    lean_dec(v_code_8363_);
                                    v___x_8841_ = lean_box(0);
                                    v_isShared_8842_ = v_isSharedCheck_8849_;
                                    state = 85;
                                    continue;
                                }
                            } else {
                                v___x_8856_ = lean_ptr_addr(v_k_8772_);
                                v___x_8857_ = lean_ptr_addr(v_a_8779_);
                                v___x_8858_ = lean_usize_dec_eq(v___x_8856_, v___x_8857_);
                                if v___x_8858_ == 0 {
                                    lean_inc(v_offset_8769_);
                                    lean_inc(v_i_8768_);
                                    v_isSharedCheck_8868_ =
                                        (!lean_is_exclusive(v_code_8363_)) as u8;
                                    if v_isSharedCheck_8868_ == 0 {
                                        v_unused_8869_ = lean_ctor_get(v_code_8363_, 5);
                                        lean_dec(v_unused_8869_);
                                        v_unused_8870_ = lean_ctor_get(v_code_8363_, 4);
                                        lean_dec(v_unused_8870_);
                                        v_unused_8871_ = lean_ctor_get(v_code_8363_, 3);
                                        lean_dec(v_unused_8871_);
                                        v_unused_8872_ = lean_ctor_get(v_code_8363_, 2);
                                        lean_dec(v_unused_8872_);
                                        v_unused_8873_ = lean_ctor_get(v_code_8363_, 1);
                                        lean_dec(v_unused_8873_);
                                        v_unused_8874_ = lean_ctor_get(v_code_8363_, 0);
                                        lean_dec(v_unused_8874_);
                                        v___x_8860_ = v_code_8363_;
                                        v_isShared_8861_ = v_isSharedCheck_8868_;
                                        state = 88;
                                        continue;
                                    } else {
                                        lean_dec(v_code_8363_);
                                        v___x_8860_ = lean_box(0);
                                        v_isShared_8861_ = v_isSharedCheck_8868_;
                                        state = 88;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_8779_);
                                    lean_dec_ref(v___x_8777_);
                                    lean_dec(v_fvarId_8776_);
                                    lean_dec(v_fvarId_8774_);
                                    if v_isShared_8782_ == 0 {
                                        lean_ctor_set(v___x_8781_, 0, v_code_8363_);
                                        v___x_8876_ = v___x_8781_;
                                        state = 91;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_8877_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_8877_, 0, v_code_8363_);
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
                    lean_ctor_set(v___x_8786_, 5, v_a_8779_);
                    lean_ctor_set(v___x_8786_, 4, v___x_8777_);
                    lean_ctor_set(v___x_8786_, 3, v_fvarId_8776_);
                    lean_ctor_set(v___x_8786_, 0, v_fvarId_8774_);
                    v___x_8789_ = v___x_8786_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_8793_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 0, v_fvarId_8774_);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 1, v_i_8768_);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 2, v_offset_8769_);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 3, v_fvarId_8776_);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 4, v___x_8777_);
                    lean_ctor_set(v_reuseFailAlloc_8793_, 5, v_a_8779_);
                    v___x_8789_ = v_reuseFailAlloc_8793_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                if v_isShared_8782_ == 0 {
                    lean_ctor_set(v___x_8781_, 0, v___x_8789_);
                    v___x_8791_ = v___x_8781_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_8792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8792_, 0, v___x_8789_);
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
                    lean_ctor_set(v___x_8803_, 5, v_a_8779_);
                    lean_ctor_set(v___x_8803_, 4, v___x_8777_);
                    lean_ctor_set(v___x_8803_, 3, v_fvarId_8776_);
                    lean_ctor_set(v___x_8803_, 0, v_fvarId_8774_);
                    v___x_8806_ = v___x_8803_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_8810_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 0, v_fvarId_8774_);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 1, v_i_8768_);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 2, v_offset_8769_);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 3, v_fvarId_8776_);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 4, v___x_8777_);
                    lean_ctor_set(v_reuseFailAlloc_8810_, 5, v_a_8779_);
                    v___x_8806_ = v_reuseFailAlloc_8810_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_8782_ == 0 {
                    lean_ctor_set(v___x_8781_, 0, v___x_8806_);
                    v___x_8808_ = v___x_8781_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_8809_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8809_, 0, v___x_8806_);
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
                    lean_ctor_set(v___x_8822_, 5, v_a_8779_);
                    lean_ctor_set(v___x_8822_, 4, v___x_8777_);
                    lean_ctor_set(v___x_8822_, 3, v_fvarId_8776_);
                    lean_ctor_set(v___x_8822_, 0, v_fvarId_8774_);
                    v___x_8825_ = v___x_8822_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_8829_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 0, v_fvarId_8774_);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 1, v_i_8768_);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 2, v_offset_8769_);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 3, v_fvarId_8776_);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 4, v___x_8777_);
                    lean_ctor_set(v_reuseFailAlloc_8829_, 5, v_a_8779_);
                    v___x_8825_ = v_reuseFailAlloc_8829_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_8782_ == 0 {
                    lean_ctor_set(v___x_8781_, 0, v___x_8825_);
                    v___x_8827_ = v___x_8781_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_8828_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8828_, 0, v___x_8825_);
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
                    lean_ctor_set(v___x_8841_, 5, v_a_8779_);
                    lean_ctor_set(v___x_8841_, 4, v___x_8777_);
                    lean_ctor_set(v___x_8841_, 3, v_fvarId_8776_);
                    lean_ctor_set(v___x_8841_, 0, v_fvarId_8774_);
                    v___x_8844_ = v___x_8841_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_8848_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 0, v_fvarId_8774_);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 1, v_i_8768_);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 2, v_offset_8769_);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 3, v_fvarId_8776_);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 4, v___x_8777_);
                    lean_ctor_set(v_reuseFailAlloc_8848_, 5, v_a_8779_);
                    v___x_8844_ = v_reuseFailAlloc_8848_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                if v_isShared_8782_ == 0 {
                    lean_ctor_set(v___x_8781_, 0, v___x_8844_);
                    v___x_8846_ = v___x_8781_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_8847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8847_, 0, v___x_8844_);
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
                    lean_ctor_set(v___x_8860_, 5, v_a_8779_);
                    lean_ctor_set(v___x_8860_, 4, v___x_8777_);
                    lean_ctor_set(v___x_8860_, 3, v_fvarId_8776_);
                    lean_ctor_set(v___x_8860_, 0, v_fvarId_8774_);
                    v___x_8863_ = v___x_8860_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_8867_ = lean_alloc_ctor(9, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 0, v_fvarId_8774_);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 1, v_i_8768_);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 2, v_offset_8769_);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 3, v_fvarId_8776_);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 4, v___x_8777_);
                    lean_ctor_set(v_reuseFailAlloc_8867_, 5, v_a_8779_);
                    v___x_8863_ = v_reuseFailAlloc_8867_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_8782_ == 0 {
                    lean_ctor_set(v___x_8781_, 0, v___x_8863_);
                    v___x_8865_ = v___x_8781_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_8866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8866_, 0, v___x_8863_);
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
                    lean_inc(v_cidx_8886_);
                    v_isSharedCheck_8906_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8906_ == 0 {
                        v_unused_8907_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_8907_);
                        v_unused_8908_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8908_);
                        v_unused_8909_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8909_);
                        v___x_8898_ = v_code_8363_;
                        v_isShared_8899_ = v_isSharedCheck_8906_;
                        state = 94;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8898_ = lean_box(0);
                        v_isShared_8899_ = v_isSharedCheck_8906_;
                        state = 94;
                        continue;
                    }
                } else {
                    v___x_8910_ = lean_ptr_addr(v_k_8887_);
                    v___x_8911_ = lean_ptr_addr(v_a_8891_);
                    v___x_8912_ = lean_usize_dec_eq(v___x_8910_, v___x_8911_);
                    if v___x_8912_ == 0 {
                        lean_inc(v_cidx_8886_);
                        v_isSharedCheck_8922_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8922_ == 0 {
                            v_unused_8923_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_8923_);
                            v_unused_8924_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_8924_);
                            v_unused_8925_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8925_);
                            v___x_8914_ = v_code_8363_;
                            v_isShared_8915_ = v_isSharedCheck_8922_;
                            state = 97;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8914_ = lean_box(0);
                            v_isShared_8915_ = v_isSharedCheck_8922_;
                            state = 97;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8891_);
                        lean_dec(v_fvarId_8889_);
                        if v_isShared_8894_ == 0 {
                            lean_ctor_set(v___x_8893_, 0, v_code_8363_);
                            v___x_8927_ = v___x_8893_;
                            state = 100;
                            continue;
                        } else {
                            v_reuseFailAlloc_8928_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_8928_, 0, v_code_8363_);
                            v___x_8927_ = v_reuseFailAlloc_8928_;
                            state = 100;
                            continue;
                        }
                    }
                }
            }
            94 => {
                if v_isShared_8899_ == 0 {
                    lean_ctor_set(v___x_8898_, 2, v_a_8891_);
                    lean_ctor_set(v___x_8898_, 0, v_fvarId_8889_);
                    v___x_8901_ = v___x_8898_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_8905_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8905_, 0, v_fvarId_8889_);
                    lean_ctor_set(v_reuseFailAlloc_8905_, 1, v_cidx_8886_);
                    lean_ctor_set(v_reuseFailAlloc_8905_, 2, v_a_8891_);
                    v___x_8901_ = v_reuseFailAlloc_8905_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_8894_ == 0 {
                    lean_ctor_set(v___x_8893_, 0, v___x_8901_);
                    v___x_8903_ = v___x_8893_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_8904_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8904_, 0, v___x_8901_);
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
                    lean_ctor_set(v___x_8914_, 2, v_a_8891_);
                    lean_ctor_set(v___x_8914_, 0, v_fvarId_8889_);
                    v___x_8917_ = v___x_8914_;
                    state = 98;
                    continue;
                } else {
                    v_reuseFailAlloc_8921_ = lean_alloc_ctor(10, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8921_, 0, v_fvarId_8889_);
                    lean_ctor_set(v_reuseFailAlloc_8921_, 1, v_cidx_8886_);
                    lean_ctor_set(v_reuseFailAlloc_8921_, 2, v_a_8891_);
                    v___x_8917_ = v_reuseFailAlloc_8921_;
                    state = 98;
                    continue;
                }
            }
            98 => {
                if v_isShared_8894_ == 0 {
                    lean_ctor_set(v___x_8893_, 0, v___x_8917_);
                    v___x_8919_ = v___x_8893_;
                    state = 99;
                    continue;
                } else {
                    v_reuseFailAlloc_8920_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8920_, 0, v___x_8917_);
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
                    lean_inc(v_n_8936_);
                    v_isSharedCheck_8958_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_8958_ == 0 {
                        v_unused_8959_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_8959_);
                        v_unused_8960_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_8960_);
                        v_unused_8961_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_8961_);
                        v___x_8950_ = v_code_8363_;
                        v_isShared_8951_ = v_isSharedCheck_8958_;
                        state = 103;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_8950_ = lean_box(0);
                        v_isShared_8951_ = v_isSharedCheck_8958_;
                        state = 103;
                        continue;
                    }
                } else {
                    v___x_8962_ = lean_ptr_addr(v_k_8939_);
                    v___x_8963_ = lean_ptr_addr(v_a_8943_);
                    v___x_8964_ = lean_usize_dec_eq(v___x_8962_, v___x_8963_);
                    if v___x_8964_ == 0 {
                        lean_inc(v_n_8936_);
                        v_isSharedCheck_8974_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_8974_ == 0 {
                            v_unused_8975_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_8975_);
                            v_unused_8976_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_8976_);
                            v_unused_8977_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_8977_);
                            v___x_8966_ = v_code_8363_;
                            v_isShared_8967_ = v_isSharedCheck_8974_;
                            state = 106;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_8966_ = lean_box(0);
                            v_isShared_8967_ = v_isSharedCheck_8974_;
                            state = 106;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8943_);
                        lean_dec(v_fvarId_8941_);
                        if v_isShared_8946_ == 0 {
                            lean_ctor_set(v___x_8945_, 0, v_code_8363_);
                            v___x_8979_ = v___x_8945_;
                            state = 109;
                            continue;
                        } else {
                            v_reuseFailAlloc_8980_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_8980_, 0, v_code_8363_);
                            v___x_8979_ = v_reuseFailAlloc_8980_;
                            state = 109;
                            continue;
                        }
                    }
                }
            }
            103 => {
                if v_isShared_8951_ == 0 {
                    lean_ctor_set(v___x_8950_, 2, v_a_8943_);
                    lean_ctor_set(v___x_8950_, 0, v_fvarId_8941_);
                    v___x_8953_ = v___x_8950_;
                    state = 104;
                    continue;
                } else {
                    v_reuseFailAlloc_8957_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8957_, 0, v_fvarId_8941_);
                    lean_ctor_set(v_reuseFailAlloc_8957_, 1, v_n_8936_);
                    lean_ctor_set(v_reuseFailAlloc_8957_, 2, v_a_8943_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8957_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_8937_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8957_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_8938_,
                    );
                    v___x_8953_ = v_reuseFailAlloc_8957_;
                    state = 104;
                    continue;
                }
            }
            104 => {
                if v_isShared_8946_ == 0 {
                    lean_ctor_set(v___x_8945_, 0, v___x_8953_);
                    v___x_8955_ = v___x_8945_;
                    state = 105;
                    continue;
                } else {
                    v_reuseFailAlloc_8956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8956_, 0, v___x_8953_);
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
                    lean_ctor_set(v___x_8966_, 2, v_a_8943_);
                    lean_ctor_set(v___x_8966_, 0, v_fvarId_8941_);
                    v___x_8969_ = v___x_8966_;
                    state = 107;
                    continue;
                } else {
                    v_reuseFailAlloc_8973_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8973_, 0, v_fvarId_8941_);
                    lean_ctor_set(v_reuseFailAlloc_8973_, 1, v_n_8936_);
                    lean_ctor_set(v_reuseFailAlloc_8973_, 2, v_a_8943_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8973_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_8937_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8973_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_8938_,
                    );
                    v___x_8969_ = v_reuseFailAlloc_8973_;
                    state = 107;
                    continue;
                }
            }
            107 => {
                if v_isShared_8946_ == 0 {
                    lean_ctor_set(v___x_8945_, 0, v___x_8969_);
                    v___x_8971_ = v___x_8945_;
                    state = 108;
                    continue;
                } else {
                    v_reuseFailAlloc_8972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8972_, 0, v___x_8969_);
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
                    lean_inc(v_objs_x3f_8991_);
                    lean_inc(v_n_8988_);
                    v_isSharedCheck_9011_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_9011_ == 0 {
                        v_unused_9012_ = lean_ctor_get(v_code_8363_, 3);
                        lean_dec(v_unused_9012_);
                        v_unused_9013_ = lean_ctor_get(v_code_8363_, 2);
                        lean_dec(v_unused_9013_);
                        v_unused_9014_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_9014_);
                        v_unused_9015_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_9015_);
                        v___x_9003_ = v_code_8363_;
                        v_isShared_9004_ = v_isSharedCheck_9011_;
                        state = 112;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_9003_ = lean_box(0);
                        v_isShared_9004_ = v_isSharedCheck_9011_;
                        state = 112;
                        continue;
                    }
                } else {
                    v___x_9016_ = lean_ptr_addr(v_objs_x3f_8991_);
                    v___x_9017_ = lean_usize_dec_eq(v___x_9016_, v___x_9016_);
                    if v___x_9017_ == 0 {
                        lean_inc(v_objs_x3f_8991_);
                        lean_inc(v_n_8988_);
                        v_isSharedCheck_9027_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                        if v_isSharedCheck_9027_ == 0 {
                            v_unused_9028_ = lean_ctor_get(v_code_8363_, 3);
                            lean_dec(v_unused_9028_);
                            v_unused_9029_ = lean_ctor_get(v_code_8363_, 2);
                            lean_dec(v_unused_9029_);
                            v_unused_9030_ = lean_ctor_get(v_code_8363_, 1);
                            lean_dec(v_unused_9030_);
                            v_unused_9031_ = lean_ctor_get(v_code_8363_, 0);
                            lean_dec(v_unused_9031_);
                            v___x_9019_ = v_code_8363_;
                            v_isShared_9020_ = v_isSharedCheck_9027_;
                            state = 115;
                            continue;
                        } else {
                            lean_dec(v_code_8363_);
                            v___x_9019_ = lean_box(0);
                            v_isShared_9020_ = v_isSharedCheck_9027_;
                            state = 115;
                            continue;
                        }
                    } else {
                        v___x_9032_ = lean_ptr_addr(v_k_8992_);
                        v___x_9033_ = lean_ptr_addr(v_a_8996_);
                        v___x_9034_ = lean_usize_dec_eq(v___x_9032_, v___x_9033_);
                        if v___x_9034_ == 0 {
                            lean_inc(v_objs_x3f_8991_);
                            lean_inc(v_n_8988_);
                            v_isSharedCheck_9044_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                            if v_isSharedCheck_9044_ == 0 {
                                v_unused_9045_ = lean_ctor_get(v_code_8363_, 3);
                                lean_dec(v_unused_9045_);
                                v_unused_9046_ = lean_ctor_get(v_code_8363_, 2);
                                lean_dec(v_unused_9046_);
                                v_unused_9047_ = lean_ctor_get(v_code_8363_, 1);
                                lean_dec(v_unused_9047_);
                                v_unused_9048_ = lean_ctor_get(v_code_8363_, 0);
                                lean_dec(v_unused_9048_);
                                v___x_9036_ = v_code_8363_;
                                v_isShared_9037_ = v_isSharedCheck_9044_;
                                state = 118;
                                continue;
                            } else {
                                lean_dec(v_code_8363_);
                                v___x_9036_ = lean_box(0);
                                v_isShared_9037_ = v_isSharedCheck_9044_;
                                state = 118;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_8996_);
                            lean_dec(v_fvarId_8994_);
                            if v_isShared_8999_ == 0 {
                                lean_ctor_set(v___x_8998_, 0, v_code_8363_);
                                v___x_9050_ = v___x_8998_;
                                state = 121;
                                continue;
                            } else {
                                v_reuseFailAlloc_9051_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_9051_, 0, v_code_8363_);
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
                    lean_ctor_set(v___x_9003_, 3, v_a_8996_);
                    lean_ctor_set(v___x_9003_, 0, v_fvarId_8994_);
                    v___x_9006_ = v___x_9003_;
                    state = 113;
                    continue;
                } else {
                    v_reuseFailAlloc_9010_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9010_, 0, v_fvarId_8994_);
                    lean_ctor_set(v_reuseFailAlloc_9010_, 1, v_n_8988_);
                    lean_ctor_set(v_reuseFailAlloc_9010_, 2, v_objs_x3f_8991_);
                    lean_ctor_set(v_reuseFailAlloc_9010_, 3, v_a_8996_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9010_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9010_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9006_ = v_reuseFailAlloc_9010_;
                    state = 113;
                    continue;
                }
            }
            113 => {
                if v_isShared_8999_ == 0 {
                    lean_ctor_set(v___x_8998_, 0, v___x_9006_);
                    v___x_9008_ = v___x_8998_;
                    state = 114;
                    continue;
                } else {
                    v_reuseFailAlloc_9009_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9009_, 0, v___x_9006_);
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
                    lean_ctor_set(v___x_9019_, 3, v_a_8996_);
                    lean_ctor_set(v___x_9019_, 0, v_fvarId_8994_);
                    v___x_9022_ = v___x_9019_;
                    state = 116;
                    continue;
                } else {
                    v_reuseFailAlloc_9026_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9026_, 0, v_fvarId_8994_);
                    lean_ctor_set(v_reuseFailAlloc_9026_, 1, v_n_8988_);
                    lean_ctor_set(v_reuseFailAlloc_9026_, 2, v_objs_x3f_8991_);
                    lean_ctor_set(v_reuseFailAlloc_9026_, 3, v_a_8996_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9026_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9026_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9022_ = v_reuseFailAlloc_9026_;
                    state = 116;
                    continue;
                }
            }
            116 => {
                if v_isShared_8999_ == 0 {
                    lean_ctor_set(v___x_8998_, 0, v___x_9022_);
                    v___x_9024_ = v___x_8998_;
                    state = 117;
                    continue;
                } else {
                    v_reuseFailAlloc_9025_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9025_, 0, v___x_9022_);
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
                    lean_ctor_set(v___x_9036_, 3, v_a_8996_);
                    lean_ctor_set(v___x_9036_, 0, v_fvarId_8994_);
                    v___x_9039_ = v___x_9036_;
                    state = 119;
                    continue;
                } else {
                    v_reuseFailAlloc_9043_ = lean_alloc_ctor(12, 4, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9043_, 0, v_fvarId_8994_);
                    lean_ctor_set(v_reuseFailAlloc_9043_, 1, v_n_8988_);
                    lean_ctor_set(v_reuseFailAlloc_9043_, 2, v_objs_x3f_8991_);
                    lean_ctor_set(v_reuseFailAlloc_9043_, 3, v_a_8996_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9043_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v_check_8989_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9043_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v_persistent_8990_,
                    );
                    v___x_9039_ = v_reuseFailAlloc_9043_;
                    state = 119;
                    continue;
                }
            }
            119 => {
                if v_isShared_8999_ == 0 {
                    lean_ctor_set(v___x_8998_, 0, v___x_9039_);
                    v___x_9041_ = v___x_8998_;
                    state = 120;
                    continue;
                } else {
                    v_reuseFailAlloc_9042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9042_, 0, v___x_9039_);
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
                    v_isSharedCheck_9078_ = (!lean_is_exclusive(v_code_8363_)) as u8;
                    if v_isSharedCheck_9078_ == 0 {
                        v_unused_9079_ = lean_ctor_get(v_code_8363_, 1);
                        lean_dec(v_unused_9079_);
                        v_unused_9080_ = lean_ctor_get(v_code_8363_, 0);
                        lean_dec(v_unused_9080_);
                        v___x_9070_ = v_code_8363_;
                        v_isShared_9071_ = v_isSharedCheck_9078_;
                        state = 124;
                        continue;
                    } else {
                        lean_dec(v_code_8363_);
                        v___x_9070_ = lean_box(0);
                        v_isShared_9071_ = v_isSharedCheck_9078_;
                        state = 124;
                        continue;
                    }
                } else {
                    lean_dec(v_a_9063_);
                    lean_dec(v_fvarId_9061_);
                    if v_isShared_9066_ == 0 {
                        lean_ctor_set(v___x_9065_, 0, v_code_8363_);
                        v___x_9082_ = v___x_9065_;
                        state = 127;
                        continue;
                    } else {
                        v_reuseFailAlloc_9083_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9083_, 0, v_code_8363_);
                        v___x_9082_ = v_reuseFailAlloc_9083_;
                        state = 127;
                        continue;
                    }
                }
            }
            124 => {
                if v_isShared_9071_ == 0 {
                    lean_ctor_set(v___x_9070_, 1, v_a_9063_);
                    lean_ctor_set(v___x_9070_, 0, v_fvarId_9061_);
                    v___x_9073_ = v___x_9070_;
                    state = 125;
                    continue;
                } else {
                    v_reuseFailAlloc_9077_ = lean_alloc_ctor(13, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9077_, 0, v_fvarId_9061_);
                    lean_ctor_set(v_reuseFailAlloc_9077_, 1, v_a_9063_);
                    v___x_9073_ = v_reuseFailAlloc_9077_;
                    state = 125;
                    continue;
                }
            }
            125 => {
                if v_isShared_9066_ == 0 {
                    lean_ctor_set(v___x_9065_, 0, v___x_9073_);
                    v___x_9075_ = v___x_9065_;
                    state = 126;
                    continue;
                } else {
                    v_reuseFailAlloc_9076_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9076_, 0, v___x_9073_);
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
    mut v_decl_9094_: *mut LeanObject,
    mut v_a_9095_: *mut LeanObject,
    mut v_a_9096_: *mut LeanObject,
    mut v_a_9097_: *mut LeanObject,
    mut v_a_9098_: *mut LeanObject,
    mut v_a_9099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_9101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_9102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_9103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9113_: u8 = 0;
    let mut v___x_9115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9117_: u8 = 0;
    let mut v_a_9118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9121_: u8 = 0;
    let mut v___x_9123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_9101_ = lean_ctor_get(v_decl_9094_, 2);
                v_type_9102_ = lean_ctor_get(v_decl_9094_, 3);
                v_value_9103_ = lean_ctor_get(v_decl_9094_, 4);
                lean_inc_ref(v_type_9102_);
                v___x_9104_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v_pu_9092_,
                        v_a_9095_,
                        v_t_9093_,
                        v_type_9102_,
                    );
                lean_inc_ref(v_params_9101_);
                v___x_9105_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0___redArg(v_pu_9092_, v_t_9093_, v_params_9101_, v_a_9095_, v_a_9096_, v_a_9097_, v_a_9098_, v_a_9099_);
                if lean_obj_tag(v___x_9105_) == 0 {
                    v_a_9106_ = lean_ctor_get(v___x_9105_, 0);
                    lean_inc(v_a_9106_);
                    lean_dec_ref_known(v___x_9105_, 1);
                    lean_inc_ref(v_value_9103_);
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
                    if lean_obj_tag(v___x_9107_) == 0 {
                        v_a_9108_ = lean_ctor_get(v___x_9107_, 0);
                        lean_inc(v_a_9108_);
                        lean_dec_ref_known(v___x_9107_, 1);
                        v___x_9109_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_9092_, v_decl_9094_, v___x_9104_, v_a_9106_, v_a_9108_, v_a_9097_);
                        return v___x_9109_;
                    } else {
                        lean_dec(v_a_9106_);
                        lean_dec_ref(v___x_9104_);
                        lean_dec_ref(v_decl_9094_);
                        v_a_9110_ = lean_ctor_get(v___x_9107_, 0);
                        v_isSharedCheck_9117_ = (!lean_is_exclusive(v___x_9107_)) as u8;
                        if v_isSharedCheck_9117_ == 0 {
                            v___x_9112_ = v___x_9107_;
                            v_isShared_9113_ = v_isSharedCheck_9117_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9110_);
                            lean_dec(v___x_9107_);
                            v___x_9112_ = lean_box(0);
                            v_isShared_9113_ = v_isSharedCheck_9117_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_9104_);
                    lean_dec_ref(v_decl_9094_);
                    v_a_9118_ = lean_ctor_get(v___x_9105_, 0);
                    v_isSharedCheck_9125_ = (!lean_is_exclusive(v___x_9105_)) as u8;
                    if v_isSharedCheck_9125_ == 0 {
                        v___x_9120_ = v___x_9105_;
                        v_isShared_9121_ = v_isSharedCheck_9125_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9118_);
                        lean_dec(v___x_9105_);
                        v___x_9120_ = lean_box(0);
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
                    v_reuseFailAlloc_9116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9116_, 0, v_a_9110_);
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
                    v_reuseFailAlloc_9124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9124_, 0, v_a_9118_);
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
    mut v_pu_9126_: *mut LeanObject,
    mut v_t_9127_: *mut LeanObject,
    mut v_decl_9128_: *mut LeanObject,
    mut v_a_9129_: *mut LeanObject,
    mut v_a_9130_: *mut LeanObject,
    mut v_a_9131_: *mut LeanObject,
    mut v_a_9132_: *mut LeanObject,
    mut v_a_9133_: *mut LeanObject,
    mut v_a_9134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9135_: u8 = 0;
    let mut v_t_boxed_9136_: u8 = 0;
    let mut v_res_9137_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9135_ = (lean_unbox(v_pu_9126_) as u8);
    v_t_boxed_9136_ = (lean_unbox(v_t_9127_) as u8);
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
    lean_dec(v_a_9133_);
    lean_dec_ref(v_a_9132_);
    lean_dec(v_a_9131_);
    lean_dec_ref(v_a_9130_);
    lean_dec_ref(v_a_9129_);
    return v_res_9137_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4___boxed(
    mut v_pu_9138_: *mut LeanObject,
    mut v_t_9139_: *mut LeanObject,
    mut v_i_9140_: *mut LeanObject,
    mut v_as_9141_: *mut LeanObject,
    mut v___y_9142_: *mut LeanObject,
    mut v___y_9143_: *mut LeanObject,
    mut v___y_9144_: *mut LeanObject,
    mut v___y_9145_: *mut LeanObject,
    mut v___y_9146_: *mut LeanObject,
    mut v___y_9147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9148_: u8 = 0;
    let mut v_t_boxed_9149_: u8 = 0;
    let mut v_res_9150_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9148_ = (lean_unbox(v_pu_9138_) as u8);
    v_t_boxed_9149_ = (lean_unbox(v_t_9139_) as u8);
    v_res_9150_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normCodeImp_spec__4(v_pu_boxed_9148_, v_t_boxed_9149_, v_i_9140_, v_as_9141_, v___y_9142_, v___y_9143_, v___y_9144_, v___y_9145_, v___y_9146_);
    lean_dec(v___y_9146_);
    lean_dec_ref(v___y_9145_);
    lean_dec(v___y_9144_);
    lean_dec_ref(v___y_9143_);
    lean_dec_ref(v___y_9142_);
    return v_res_9150_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCodeImp___boxed(
    mut v_pu_9151_: *mut LeanObject,
    mut v_t_9152_: *mut LeanObject,
    mut v_code_9153_: *mut LeanObject,
    mut v_a_9154_: *mut LeanObject,
    mut v_a_9155_: *mut LeanObject,
    mut v_a_9156_: *mut LeanObject,
    mut v_a_9157_: *mut LeanObject,
    mut v_a_9158_: *mut LeanObject,
    mut v_a_9159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9160_: u8 = 0;
    let mut v_t_boxed_9161_: u8 = 0;
    let mut v_res_9162_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9160_ = (lean_unbox(v_pu_9151_) as u8);
    v_t_boxed_9161_ = (lean_unbox(v_t_9152_) as u8);
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
    lean_dec(v_a_9158_);
    lean_dec_ref(v_a_9157_);
    lean_dec(v_a_9156_);
    lean_dec_ref(v_a_9155_);
    lean_dec_ref(v_a_9154_);
    return v_res_9162_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_normCodeImp_spec__2(
    mut v_pu_9163_: u8,
    mut v_t_9164_: u8,
    mut v_pu_9165_: u8,
    mut v_t_9166_: u8,
    mut v_decl_9167_: *mut LeanObject,
    mut v___y_9168_: *mut LeanObject,
    mut v___y_9169_: *mut LeanObject,
    mut v___y_9170_: *mut LeanObject,
    mut v___y_9171_: *mut LeanObject,
    mut v___y_9172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9174_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_9175_: *mut LeanObject,
    mut v_t_9176_: *mut LeanObject,
    mut v_pu_9177_: *mut LeanObject,
    mut v_t_9178_: *mut LeanObject,
    mut v_decl_9179_: *mut LeanObject,
    mut v___y_9180_: *mut LeanObject,
    mut v___y_9181_: *mut LeanObject,
    mut v___y_9182_: *mut LeanObject,
    mut v___y_9183_: *mut LeanObject,
    mut v___y_9184_: *mut LeanObject,
    mut v___y_9185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9186_: u8 = 0;
    let mut v_t_boxed_9187_: u8 = 0;
    let mut v_pu_boxed_9188_: u8 = 0;
    let mut v_t_boxed_9189_: u8 = 0;
    let mut v_res_9190_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9186_ = (lean_unbox(v_pu_9175_) as u8);
    v_t_boxed_9187_ = (lean_unbox(v_t_9176_) as u8);
    v_pu_boxed_9188_ = (lean_unbox(v_pu_9177_) as u8);
    v_t_boxed_9189_ = (lean_unbox(v_t_9178_) as u8);
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
    lean_dec(v___y_9184_);
    lean_dec_ref(v___y_9183_);
    lean_dec(v___y_9182_);
    lean_dec_ref(v___y_9181_);
    lean_dec_ref(v___y_9180_);
    return v_res_9190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_normCodeImp_spec__3(
    mut v_pu_9191_: u8,
    mut v_t_9192_: u8,
    mut v_pu_9193_: u8,
    mut v_t_9194_: u8,
    mut v_args_9195_: *mut LeanObject,
    mut v___y_9196_: *mut LeanObject,
    mut v___y_9197_: *mut LeanObject,
    mut v___y_9198_: *mut LeanObject,
    mut v___y_9199_: *mut LeanObject,
    mut v___y_9200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9202_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_9203_: *mut LeanObject,
    mut v_t_9204_: *mut LeanObject,
    mut v_pu_9205_: *mut LeanObject,
    mut v_t_9206_: *mut LeanObject,
    mut v_args_9207_: *mut LeanObject,
    mut v___y_9208_: *mut LeanObject,
    mut v___y_9209_: *mut LeanObject,
    mut v___y_9210_: *mut LeanObject,
    mut v___y_9211_: *mut LeanObject,
    mut v___y_9212_: *mut LeanObject,
    mut v___y_9213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9214_: u8 = 0;
    let mut v_t_boxed_9215_: u8 = 0;
    let mut v_pu_boxed_9216_: u8 = 0;
    let mut v_t_boxed_9217_: u8 = 0;
    let mut v_res_9218_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9214_ = (lean_unbox(v_pu_9203_) as u8);
    v_t_boxed_9215_ = (lean_unbox(v_t_9204_) as u8);
    v_pu_boxed_9216_ = (lean_unbox(v_pu_9205_) as u8);
    v_t_boxed_9217_ = (lean_unbox(v_t_9206_) as u8);
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
    lean_dec(v___y_9212_);
    lean_dec_ref(v___y_9211_);
    lean_dec(v___y_9210_);
    lean_dec_ref(v___y_9209_);
    lean_dec_ref(v___y_9208_);
    return v_res_9218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0(
    mut v_pu_9219_: u8,
    mut v_t_9220_: u8,
    mut v_pu_9221_: u8,
    mut v_t_9222_: u8,
    mut v_ps_9223_: *mut LeanObject,
    mut v___y_9224_: *mut LeanObject,
    mut v___y_9225_: *mut LeanObject,
    mut v___y_9226_: *mut LeanObject,
    mut v___y_9227_: *mut LeanObject,
    mut v___y_9228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9230_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_9231_: *mut LeanObject,
    mut v_t_9232_: *mut LeanObject,
    mut v_pu_9233_: *mut LeanObject,
    mut v_t_9234_: *mut LeanObject,
    mut v_ps_9235_: *mut LeanObject,
    mut v___y_9236_: *mut LeanObject,
    mut v___y_9237_: *mut LeanObject,
    mut v___y_9238_: *mut LeanObject,
    mut v___y_9239_: *mut LeanObject,
    mut v___y_9240_: *mut LeanObject,
    mut v___y_9241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9242_: u8 = 0;
    let mut v_t_boxed_9243_: u8 = 0;
    let mut v_pu_boxed_9244_: u8 = 0;
    let mut v_t_boxed_9245_: u8 = 0;
    let mut v_res_9246_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9242_ = (lean_unbox(v_pu_9231_) as u8);
    v_t_boxed_9243_ = (lean_unbox(v_t_9232_) as u8);
    v_pu_boxed_9244_ = (lean_unbox(v_pu_9233_) as u8);
    v_t_boxed_9245_ = (lean_unbox(v_t_9234_) as u8);
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
    lean_dec(v___y_9240_);
    lean_dec_ref(v___y_9239_);
    lean_dec(v___y_9238_);
    lean_dec_ref(v___y_9237_);
    lean_dec_ref(v___y_9236_);
    return v_res_9246_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(
    mut v_pu_9247_: u8,
    mut v_t_9248_: u8,
    mut v_i_9249_: *mut LeanObject,
    mut v_as_9250_: *mut LeanObject,
    mut v___y_9251_: *mut LeanObject,
    mut v___y_9252_: *mut LeanObject,
    mut v___y_9253_: *mut LeanObject,
    mut v___y_9254_: *mut LeanObject,
    mut v___y_9255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9257_: *mut LeanObject = core::ptr::null_mut();
    v___x_9257_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___redArg(v_pu_9247_, v_t_9248_, v_i_9249_, v_as_9250_, v___y_9251_, v___y_9253_);
    return v___x_9257_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0___boxed(
    mut v_pu_9258_: *mut LeanObject,
    mut v_t_9259_: *mut LeanObject,
    mut v_i_9260_: *mut LeanObject,
    mut v_as_9261_: *mut LeanObject,
    mut v___y_9262_: *mut LeanObject,
    mut v___y_9263_: *mut LeanObject,
    mut v___y_9264_: *mut LeanObject,
    mut v___y_9265_: *mut LeanObject,
    mut v___y_9266_: *mut LeanObject,
    mut v___y_9267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9268_: u8 = 0;
    let mut v_t_boxed_9269_: u8 = 0;
    let mut v_res_9270_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9268_ = (lean_unbox(v_pu_9258_) as u8);
    v_t_boxed_9269_ = (lean_unbox(v_t_9259_) as u8);
    v_res_9270_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_normFunDeclImp_spec__0_spec__0(v_pu_boxed_9268_, v_t_boxed_9269_, v_i_9260_, v_as_9261_, v___y_9262_, v___y_9263_, v___y_9264_, v___y_9265_, v___y_9266_);
    lean_dec(v___y_9266_);
    lean_dec_ref(v___y_9265_);
    lean_dec(v___y_9264_);
    lean_dec_ref(v___y_9263_);
    lean_dec_ref(v___y_9262_);
    return v_res_9270_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0(
    mut v_pu_9271_: u8,
    mut v_t_9272_: u8,
    mut v_decl_9273_: *mut LeanObject,
    mut v_inst_9274_: *mut LeanObject,
    mut v_____do__lift_9275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9279_: *mut LeanObject = core::ptr::null_mut();
    v___x_9276_ = lean_box((v_pu_9271_) as usize);
    v___x_9277_ = lean_box((v_t_9272_) as usize);
    v___x_9278_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDeclImp___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_9278_, 0, v___x_9276_);
    lean_closure_set(v___x_9278_, 1, v___x_9277_);
    lean_closure_set(v___x_9278_, 2, v_decl_9273_);
    lean_closure_set(v___x_9278_, 3, v_____do__lift_9275_);
    v___x_9279_ = lean_apply_2(v_inst_9274_, lean_box(0), v___x_9278_);
    return v___x_9279_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed(
    mut v_pu_9280_: *mut LeanObject,
    mut v_t_9281_: *mut LeanObject,
    mut v_decl_9282_: *mut LeanObject,
    mut v_inst_9283_: *mut LeanObject,
    mut v_____do__lift_9284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9285_: u8 = 0;
    let mut v_t_boxed_9286_: u8 = 0;
    let mut v_res_9287_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9285_ = (lean_unbox(v_pu_9280_) as u8);
    v_t_boxed_9286_ = (lean_unbox(v_t_9281_) as u8);
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
    mut v_inst_9290_: *mut LeanObject,
    mut v_inst_9291_: *mut LeanObject,
    mut v_inst_9292_: *mut LeanObject,
    mut v_decl_9293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9298_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9294_ = lean_ctor_get(v_inst_9291_, 1);
    lean_inc(v_toBind_9294_);
    lean_dec_ref(v_inst_9291_);
    v___x_9295_ = lean_box((v_pu_9288_) as usize);
    v___x_9296_ = lean_box((v_t_9289_) as usize);
    v___f_9297_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_9297_, 0, v___x_9295_);
    lean_closure_set(v___f_9297_, 1, v___x_9296_);
    lean_closure_set(v___f_9297_, 2, v_decl_9293_);
    lean_closure_set(v___f_9297_, 3, v_inst_9290_);
    v___x_9298_ = lean_apply_4(
        v_toBind_9294_,
        lean_box(0),
        lean_box(0),
        v_inst_9292_,
        v___f_9297_,
    );
    return v___x_9298_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___redArg___boxed(
    mut v_pu_9299_: *mut LeanObject,
    mut v_t_9300_: *mut LeanObject,
    mut v_inst_9301_: *mut LeanObject,
    mut v_inst_9302_: *mut LeanObject,
    mut v_inst_9303_: *mut LeanObject,
    mut v_decl_9304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9305_: u8 = 0;
    let mut v_t_boxed_9306_: u8 = 0;
    let mut v_res_9307_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9305_ = (lean_unbox(v_pu_9299_) as u8);
    v_t_boxed_9306_ = (lean_unbox(v_t_9300_) as u8);
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
    mut v_m_9308_: *mut LeanObject,
    mut v_pu_9309_: u8,
    mut v_t_9310_: u8,
    mut v_inst_9311_: *mut LeanObject,
    mut v_inst_9312_: *mut LeanObject,
    mut v_inst_9313_: *mut LeanObject,
    mut v_decl_9314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9319_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9315_ = lean_ctor_get(v_inst_9312_, 1);
    lean_inc(v_toBind_9315_);
    lean_dec_ref(v_inst_9312_);
    v___x_9316_ = lean_box((v_pu_9309_) as usize);
    v___x_9317_ = lean_box((v_t_9310_) as usize);
    v___f_9318_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normFunDecl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_9318_, 0, v___x_9316_);
    lean_closure_set(v___f_9318_, 1, v___x_9317_);
    lean_closure_set(v___f_9318_, 2, v_decl_9314_);
    lean_closure_set(v___f_9318_, 3, v_inst_9311_);
    v___x_9319_ = lean_apply_4(
        v_toBind_9315_,
        lean_box(0),
        lean_box(0),
        v_inst_9313_,
        v___f_9318_,
    );
    return v___x_9319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normFunDecl___boxed(
    mut v_m_9320_: *mut LeanObject,
    mut v_pu_9321_: *mut LeanObject,
    mut v_t_9322_: *mut LeanObject,
    mut v_inst_9323_: *mut LeanObject,
    mut v_inst_9324_: *mut LeanObject,
    mut v_inst_9325_: *mut LeanObject,
    mut v_decl_9326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9327_: u8 = 0;
    let mut v_t_boxed_9328_: u8 = 0;
    let mut v_res_9329_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9327_ = (lean_unbox(v_pu_9321_) as u8);
    v_t_boxed_9328_ = (lean_unbox(v_t_9322_) as u8);
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
    mut v_code_9332_: *mut LeanObject,
    mut v_inst_9333_: *mut LeanObject,
    mut v_____do__lift_9334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9338_: *mut LeanObject = core::ptr::null_mut();
    v___x_9335_ = lean_box((v_pu_9330_) as usize);
    v___x_9336_ = lean_box((v_t_9331_) as usize);
    v___x_9337_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCodeImp___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_9337_, 0, v___x_9335_);
    lean_closure_set(v___x_9337_, 1, v___x_9336_);
    lean_closure_set(v___x_9337_, 2, v_code_9332_);
    lean_closure_set(v___x_9337_, 3, v_____do__lift_9334_);
    v___x_9338_ = lean_apply_2(v_inst_9333_, lean_box(0), v___x_9337_);
    return v___x_9338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed(
    mut v_pu_9339_: *mut LeanObject,
    mut v_t_9340_: *mut LeanObject,
    mut v_code_9341_: *mut LeanObject,
    mut v_inst_9342_: *mut LeanObject,
    mut v_____do__lift_9343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9344_: u8 = 0;
    let mut v_t_boxed_9345_: u8 = 0;
    let mut v_res_9346_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9344_ = (lean_unbox(v_pu_9339_) as u8);
    v_t_boxed_9345_ = (lean_unbox(v_t_9340_) as u8);
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
    mut v_inst_9349_: *mut LeanObject,
    mut v_inst_9350_: *mut LeanObject,
    mut v_inst_9351_: *mut LeanObject,
    mut v_code_9352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9357_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9353_ = lean_ctor_get(v_inst_9350_, 1);
    lean_inc(v_toBind_9353_);
    lean_dec_ref(v_inst_9350_);
    v___x_9354_ = lean_box((v_pu_9347_) as usize);
    v___x_9355_ = lean_box((v_t_9348_) as usize);
    v___f_9356_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_9356_, 0, v___x_9354_);
    lean_closure_set(v___f_9356_, 1, v___x_9355_);
    lean_closure_set(v___f_9356_, 2, v_code_9352_);
    lean_closure_set(v___f_9356_, 3, v_inst_9349_);
    v___x_9357_ = lean_apply_4(
        v_toBind_9353_,
        lean_box(0),
        lean_box(0),
        v_inst_9351_,
        v___f_9356_,
    );
    return v___x_9357_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___redArg___boxed(
    mut v_pu_9358_: *mut LeanObject,
    mut v_t_9359_: *mut LeanObject,
    mut v_inst_9360_: *mut LeanObject,
    mut v_inst_9361_: *mut LeanObject,
    mut v_inst_9362_: *mut LeanObject,
    mut v_code_9363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9364_: u8 = 0;
    let mut v_t_boxed_9365_: u8 = 0;
    let mut v_res_9366_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9364_ = (lean_unbox(v_pu_9358_) as u8);
    v_t_boxed_9365_ = (lean_unbox(v_t_9359_) as u8);
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
    mut v_m_9367_: *mut LeanObject,
    mut v_pu_9368_: u8,
    mut v_t_9369_: u8,
    mut v_inst_9370_: *mut LeanObject,
    mut v_inst_9371_: *mut LeanObject,
    mut v_inst_9372_: *mut LeanObject,
    mut v_code_9373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9378_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9374_ = lean_ctor_get(v_inst_9371_, 1);
    lean_inc(v_toBind_9374_);
    lean_dec_ref(v_inst_9371_);
    v___x_9375_ = lean_box((v_pu_9368_) as usize);
    v___x_9376_ = lean_box((v_t_9369_) as usize);
    v___f_9377_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_normCode___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_9377_, 0, v___x_9375_);
    lean_closure_set(v___f_9377_, 1, v___x_9376_);
    lean_closure_set(v___f_9377_, 2, v_code_9373_);
    lean_closure_set(v___f_9377_, 3, v_inst_9370_);
    v___x_9378_ = lean_apply_4(
        v_toBind_9374_,
        lean_box(0),
        lean_box(0),
        v_inst_9372_,
        v___f_9377_,
    );
    return v___x_9378_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normCode___boxed(
    mut v_m_9379_: *mut LeanObject,
    mut v_pu_9380_: *mut LeanObject,
    mut v_t_9381_: *mut LeanObject,
    mut v_inst_9382_: *mut LeanObject,
    mut v_inst_9383_: *mut LeanObject,
    mut v_inst_9384_: *mut LeanObject,
    mut v_code_9385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9386_: u8 = 0;
    let mut v_t_boxed_9387_: u8 = 0;
    let mut v_res_9388_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9386_ = (lean_unbox(v_pu_9380_) as u8);
    v_t_boxed_9387_ = (lean_unbox(v_t_9381_) as u8);
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
    mut v_e_9390_: *mut LeanObject,
    mut v_s_9391_: *mut LeanObject,
    mut v_translator_9392_: u8,
) -> *mut LeanObject {
    let mut v___x_9394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9395_: *mut LeanObject = core::ptr::null_mut();
    v___x_9394_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_9389_,
        v_s_9391_,
        v_translator_9392_,
        v_e_9390_,
    );
    v___x_9395_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9395_, 0, v___x_9394_);
    return v___x_9395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars___redArg___boxed(
    mut v_pu_9396_: *mut LeanObject,
    mut v_e_9397_: *mut LeanObject,
    mut v_s_9398_: *mut LeanObject,
    mut v_translator_9399_: *mut LeanObject,
    mut v_a_9400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9401_: u8 = 0;
    let mut v_translator_boxed_9402_: u8 = 0;
    let mut v_res_9403_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9401_ = (lean_unbox(v_pu_9396_) as u8);
    v_translator_boxed_9402_ = (lean_unbox(v_translator_9399_) as u8);
    v_res_9403_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
        v_pu_boxed_9401_,
        v_e_9397_,
        v_s_9398_,
        v_translator_boxed_9402_,
    );
    lean_dec_ref(v_s_9398_);
    return v_res_9403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars(
    mut v_pu_9404_: u8,
    mut v_e_9405_: *mut LeanObject,
    mut v_s_9406_: *mut LeanObject,
    mut v_translator_9407_: u8,
    mut v_a_9408_: *mut LeanObject,
    mut v_a_9409_: *mut LeanObject,
    mut v_a_9410_: *mut LeanObject,
    mut v_a_9411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9413_: *mut LeanObject = core::ptr::null_mut();
    v___x_9413_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
        v_pu_9404_,
        v_e_9405_,
        v_s_9406_,
        v_translator_9407_,
    );
    return v___x_9413_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceExprFVars___boxed(
    mut v_pu_9414_: *mut LeanObject,
    mut v_e_9415_: *mut LeanObject,
    mut v_s_9416_: *mut LeanObject,
    mut v_translator_9417_: *mut LeanObject,
    mut v_a_9418_: *mut LeanObject,
    mut v_a_9419_: *mut LeanObject,
    mut v_a_9420_: *mut LeanObject,
    mut v_a_9421_: *mut LeanObject,
    mut v_a_9422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9423_: u8 = 0;
    let mut v_translator_boxed_9424_: u8 = 0;
    let mut v_res_9425_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9423_ = (lean_unbox(v_pu_9414_) as u8);
    v_translator_boxed_9424_ = (lean_unbox(v_translator_9417_) as u8);
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
    lean_dec(v_a_9421_);
    lean_dec_ref(v_a_9420_);
    lean_dec(v_a_9419_);
    lean_dec_ref(v_a_9418_);
    lean_dec_ref(v_s_9416_);
    return v_res_9425_;
}
pub unsafe fn l_Lean_Compiler_LCNF_replaceFVars(
    mut v_pu_9426_: u8,
    mut v_code_9427_: *mut LeanObject,
    mut v_s_9428_: *mut LeanObject,
    mut v_translator_9429_: u8,
    mut v_a_9430_: *mut LeanObject,
    mut v_a_9431_: *mut LeanObject,
    mut v_a_9432_: *mut LeanObject,
    mut v_a_9433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9435_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_9436_: *mut LeanObject,
    mut v_code_9437_: *mut LeanObject,
    mut v_s_9438_: *mut LeanObject,
    mut v_translator_9439_: *mut LeanObject,
    mut v_a_9440_: *mut LeanObject,
    mut v_a_9441_: *mut LeanObject,
    mut v_a_9442_: *mut LeanObject,
    mut v_a_9443_: *mut LeanObject,
    mut v_a_9444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9445_: u8 = 0;
    let mut v_translator_boxed_9446_: u8 = 0;
    let mut v_res_9447_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9445_ = (lean_unbox(v_pu_9436_) as u8);
    v_translator_boxed_9446_ = (lean_unbox(v_translator_9439_) as u8);
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
    lean_dec(v_a_9443_);
    lean_dec_ref(v_a_9442_);
    lean_dec(v_a_9441_);
    lean_dec_ref(v_a_9440_);
    lean_dec_ref(v_s_9438_);
    return v_res_9447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___redArg(
    mut v_a_9451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9454_: *mut LeanObject = core::ptr::null_mut();
    v___x_9453_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg___closed__1;
    v___x_9454_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_9453_, v_a_9451_);
    return v___x_9454_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___redArg___boxed(
    mut v_a_9455_: *mut LeanObject,
    mut v_a_9456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9457_: *mut LeanObject = core::ptr::null_mut();
    v_res_9457_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_9455_);
    lean_dec(v_a_9455_);
    return v_res_9457_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName(
    mut v_a_9458_: *mut LeanObject,
    mut v_a_9459_: *mut LeanObject,
    mut v_a_9460_: *mut LeanObject,
    mut v_a_9461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9463_: *mut LeanObject = core::ptr::null_mut();
    v___x_9463_ = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(v_a_9459_);
    return v___x_9463_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFreshJpName___boxed(
    mut v_a_9464_: *mut LeanObject,
    mut v_a_9465_: *mut LeanObject,
    mut v_a_9466_: *mut LeanObject,
    mut v_a_9467_: *mut LeanObject,
    mut v_a_9468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9469_: *mut LeanObject = core::ptr::null_mut();
    v_res_9469_ = l_Lean_Compiler_LCNF_mkFreshJpName(v_a_9464_, v_a_9465_, v_a_9466_, v_a_9467_);
    lean_dec(v_a_9467_);
    lean_dec_ref(v_a_9466_);
    lean_dec(v_a_9465_);
    lean_dec_ref(v_a_9464_);
    return v_res_9469_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxParam(
    mut v_pu_9470_: u8,
    mut v_type_9471_: *mut LeanObject,
    mut v_borrow_9472_: u8,
    mut v_a_9473_: *mut LeanObject,
    mut v_a_9474_: *mut LeanObject,
    mut v_a_9475_: *mut LeanObject,
    mut v_a_9476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9481_: *mut LeanObject = core::ptr::null_mut();
    v___x_9478_ = l_Lean_Compiler_LCNF_mkParam___closed__1;
    v___x_9479_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_9478_, v_a_9474_);
    v_a_9480_ = lean_ctor_get(v___x_9479_, 0);
    lean_inc(v_a_9480_);
    lean_dec_ref(v___x_9479_);
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
    mut v_pu_9482_: *mut LeanObject,
    mut v_type_9483_: *mut LeanObject,
    mut v_borrow_9484_: *mut LeanObject,
    mut v_a_9485_: *mut LeanObject,
    mut v_a_9486_: *mut LeanObject,
    mut v_a_9487_: *mut LeanObject,
    mut v_a_9488_: *mut LeanObject,
    mut v_a_9489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_9490_: u8 = 0;
    let mut v_borrow_boxed_9491_: u8 = 0;
    let mut v_res_9492_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_9490_ = (lean_unbox(v_pu_9482_) as u8);
    v_borrow_boxed_9491_ = (lean_unbox(v_borrow_9484_) as u8);
    v_res_9492_ = l_Lean_Compiler_LCNF_mkAuxParam(
        v_pu_boxed_9490_,
        v_type_9483_,
        v_borrow_boxed_9491_,
        v_a_9485_,
        v_a_9486_,
        v_a_9487_,
        v_a_9488_,
    );
    lean_dec(v_a_9488_);
    lean_dec_ref(v_a_9487_);
    lean_dec(v_a_9486_);
    lean_dec_ref(v_a_9485_);
    return v_res_9492_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___redArg(
    mut v_a_9493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_9495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9496_: *mut LeanObject = core::ptr::null_mut();
    v_config_9495_ = lean_ctor_get(v_a_9493_, 0);
    lean_inc_ref(v_config_9495_);
    v___x_9496_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9496_, 0, v_config_9495_);
    return v___x_9496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___redArg___boxed(
    mut v_a_9497_: *mut LeanObject,
    mut v_a_9498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9499_: *mut LeanObject = core::ptr::null_mut();
    v_res_9499_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_9497_);
    lean_dec_ref(v_a_9497_);
    return v_res_9499_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig(
    mut v_a_9500_: *mut LeanObject,
    mut v_a_9501_: *mut LeanObject,
    mut v_a_9502_: *mut LeanObject,
    mut v_a_9503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9505_: *mut LeanObject = core::ptr::null_mut();
    v___x_9505_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_9500_);
    return v___x_9505_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getConfig___boxed(
    mut v_a_9506_: *mut LeanObject,
    mut v_a_9507_: *mut LeanObject,
    mut v_a_9508_: *mut LeanObject,
    mut v_a_9509_: *mut LeanObject,
    mut v_a_9510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9511_: *mut LeanObject = core::ptr::null_mut();
    v_res_9511_ = l_Lean_Compiler_LCNF_getConfig(v_a_9506_, v_a_9507_, v_a_9508_, v_a_9509_);
    lean_dec(v_a_9509_);
    lean_dec_ref(v_a_9508_);
    lean_dec(v_a_9507_);
    lean_dec_ref(v_a_9506_);
    return v_res_9511_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run___redArg(
    mut v_x_9512_: *mut LeanObject,
    mut v_s_9513_: *mut LeanObject,
    mut v_phase_9514_: u8,
    mut v_a_9515_: *mut LeanObject,
    mut v_a_9516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_9519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9526_: u8 = 0;
    let mut v___x_9527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9518_ = lean_st_mk_ref(v_s_9513_);
                v_options_9519_ = lean_ctor_get(v_a_9515_, 2);
                v___x_9520_ = l_Lean_Compiler_LCNF_toConfigOptions(v_options_9519_);
                v___x_9521_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_9521_, 0, v___x_9520_);
                lean_ctor_set_uint8(
                    v___x_9521_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_phase_9514_,
                );
                lean_inc(v_a_9516_);
                lean_inc_ref(v_a_9515_);
                lean_inc(v___x_9518_);
                v___x_9522_ = lean_apply_5(
                    v_x_9512_,
                    v___x_9521_,
                    v___x_9518_,
                    v_a_9515_,
                    v_a_9516_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_9522_) == 0 {
                    v_a_9523_ = lean_ctor_get(v___x_9522_, 0);
                    v_isSharedCheck_9531_ = (!lean_is_exclusive(v___x_9522_)) as u8;
                    if v_isSharedCheck_9531_ == 0 {
                        v___x_9525_ = v___x_9522_;
                        v_isShared_9526_ = v_isSharedCheck_9531_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9523_);
                        lean_dec(v___x_9522_);
                        v___x_9525_ = lean_box(0);
                        v_isShared_9526_ = v_isSharedCheck_9531_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_9518_);
                    return v___x_9522_;
                }
            }
            1 => {
                v___x_9527_ = lean_st_ref_get(v___x_9518_);
                lean_dec(v___x_9518_);
                lean_dec(v___x_9527_);
                if v_isShared_9526_ == 0 {
                    v___x_9529_ = v___x_9525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9530_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9530_, 0, v_a_9523_);
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
    mut v_x_9532_: *mut LeanObject,
    mut v_s_9533_: *mut LeanObject,
    mut v_phase_9534_: *mut LeanObject,
    mut v_a_9535_: *mut LeanObject,
    mut v_a_9536_: *mut LeanObject,
    mut v_a_9537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_9538_: u8 = 0;
    let mut v_res_9539_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_9538_ = (lean_unbox(v_phase_9534_) as u8);
    v_res_9539_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
        v_x_9532_,
        v_s_9533_,
        v_phase_boxed_9538_,
        v_a_9535_,
        v_a_9536_,
    );
    lean_dec(v_a_9536_);
    lean_dec_ref(v_a_9535_);
    return v_res_9539_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_run(
    mut v_00_u03b1_9540_: *mut LeanObject,
    mut v_x_9541_: *mut LeanObject,
    mut v_s_9542_: *mut LeanObject,
    mut v_phase_9543_: u8,
    mut v_a_9544_: *mut LeanObject,
    mut v_a_9545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9547_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_9548_: *mut LeanObject,
    mut v_x_9549_: *mut LeanObject,
    mut v_s_9550_: *mut LeanObject,
    mut v_phase_9551_: *mut LeanObject,
    mut v_a_9552_: *mut LeanObject,
    mut v_a_9553_: *mut LeanObject,
    mut v_a_9554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phase_boxed_9555_: u8 = 0;
    let mut v_res_9556_: *mut LeanObject = core::ptr::null_mut();
    v_phase_boxed_9555_ = (lean_unbox(v_phase_9551_) as u8);
    v_res_9556_ = l_Lean_Compiler_LCNF_CompilerM_run(
        v_00_u03b1_9548_,
        v_x_9549_,
        v_s_9550_,
        v_phase_boxed_9555_,
        v_a_9552_,
        v_a_9553_,
    );
    lean_dec(v_a_9553_);
    lean_dec_ref(v_a_9552_);
    return v_res_9556_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default___closed__0()
-> *mut LeanObject {
    let mut v___x_9557_: *mut LeanObject = core::ptr::null_mut();
    v___x_9557_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
    return v___x_9557_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(
    mut v_00_u03b1_9558_: *mut LeanObject,
    mut v_00_u03b2_9559_: *mut LeanObject,
    mut v_inst_9560_: *mut LeanObject,
    mut v_inst_9561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9562_: *mut LeanObject = core::ptr::null_mut();
    v___x_9562_ = lean_obj_once(
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
    mut v_00_u03b1_9563_: *mut LeanObject,
    mut v_00_u03b2_9564_: *mut LeanObject,
    mut v_inst_9565_: *mut LeanObject,
    mut v_inst_9566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9567_: *mut LeanObject = core::ptr::null_mut();
    v_res_9567_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension_default(
        v_00_u03b1_9563_,
        v_00_u03b2_9564_,
        v_inst_9565_,
        v_inst_9566_,
    );
    lean_dec_ref(v_inst_9566_);
    lean_dec_ref(v_inst_9565_);
    return v_res_9567_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instInhabitedCacheExtension(
    mut v_a_9568_: *mut LeanObject,
    mut v_a_9569_: *mut LeanObject,
    mut v_a_9570_: *mut LeanObject,
    mut v_a_9571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9572_: *mut LeanObject = core::ptr::null_mut();
    v___x_9572_ = lean_obj_once(
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
    mut v_a_9573_: *mut LeanObject,
    mut v_a_9574_: *mut LeanObject,
    mut v_a_9575_: *mut LeanObject,
    mut v_a_9576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9577_: *mut LeanObject = core::ptr::null_mut();
    v_res_9577_ = l_Lean_Compiler_LCNF_instInhabitedCacheExtension(
        v_a_9573_, v_a_9574_, v_a_9575_, v_a_9576_,
    );
    lean_dec_ref(v_a_9576_);
    lean_dec_ref(v_a_9575_);
    return v_res_9577_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9586_: *mut LeanObject = core::ptr::null_mut();
    v___x_9581_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__2;
    v___x_9582_ = lean_unsigned_to_nat(14);
    v___x_9583_ = lean_unsigned_to_nat(177);
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
    mut v_inst_9587_: *mut LeanObject,
    mut v_inst_9588_: *mut LeanObject,
    mut v_snd_9589_: *mut LeanObject,
    mut v_inst_9590_: *mut LeanObject,
    mut v_s_9591_: *mut LeanObject,
    mut v_e_9592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9597_: u8 = 0;
    let mut v___x_9598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9593_ = lean_ctor_get(v_s_9591_, 0);
                v_snd_9594_ = lean_ctor_get(v_s_9591_, 1);
                v_isSharedCheck_9609_ = (!lean_is_exclusive(v_s_9591_)) as u8;
                if v_isSharedCheck_9609_ == 0 {
                    v___x_9596_ = v_s_9591_;
                    v_isShared_9597_ = v_isSharedCheck_9609_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_9594_);
                    lean_inc(v_fst_9593_);
                    lean_dec(v_s_9591_);
                    v___x_9596_ = lean_box(0);
                    v_isShared_9597_ = v_isSharedCheck_9609_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_e_9592_, 2);
                v___x_9598_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_9598_, 0, v_e_9592_);
                lean_ctor_set(v___x_9598_, 1, v_fst_9593_);
                lean_inc_ref(v_inst_9588_);
                lean_inc_ref(v_inst_9587_);
                v___x_9605_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v_inst_9587_,
                    v_inst_9588_,
                    v_snd_9589_,
                    v_e_9592_,
                );
                if lean_obj_tag(v___x_9605_) == 0 {
                    v___x_9606_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___closed__3);
                    v___x_9607_ = l_panic___redArg(v_inst_9590_, v___x_9606_);
                    v___y_9600_ = v___x_9607_;
                    state = 2;
                    continue;
                } else {
                    v_val_9608_ = lean_ctor_get(v___x_9605_, 0);
                    lean_inc(v_val_9608_);
                    lean_dec_ref_known(v___x_9605_, 1);
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
                    lean_ctor_set(v___x_9596_, 1, v___x_9601_);
                    lean_ctor_set(v___x_9596_, 0, v___x_9598_);
                    v___x_9603_ = v___x_9596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9604_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9604_, 0, v___x_9598_);
                    lean_ctor_set(v_reuseFailAlloc_9604_, 1, v___x_9601_);
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
    mut v_inst_9610_: *mut LeanObject,
    mut v_inst_9611_: *mut LeanObject,
    mut v_snd_9612_: *mut LeanObject,
    mut v_inst_9613_: *mut LeanObject,
    mut v_s_9614_: *mut LeanObject,
    mut v_e_9615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9616_: *mut LeanObject = core::ptr::null_mut();
    v_res_9616_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0(
        v_inst_9610_,
        v_inst_9611_,
        v_snd_9612_,
        v_inst_9613_,
        v_s_9614_,
        v_e_9615_,
    );
    lean_dec(v_inst_9613_);
    lean_dec(v_snd_9612_);
    return v_res_9616_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(
    mut v_inst_9619_: *mut LeanObject,
    mut v_inst_9620_: *mut LeanObject,
    mut v_inst_9621_: *mut LeanObject,
    mut v_oldState_9622_: *mut LeanObject,
    mut v_newState_9623_: *mut LeanObject,
    mut v_x_9624_: *mut LeanObject,
    mut v_s_9625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_9628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_9634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9635_: *mut LeanObject = core::ptr::null_mut();
    v_fst_9626_ = lean_ctor_get(v_newState_9623_, 0);
    lean_inc_n(v_fst_9626_, 2);
    v_snd_9627_ = lean_ctor_get(v_newState_9623_, 1);
    lean_inc(v_snd_9627_);
    lean_dec_ref(v_newState_9623_);
    v_fst_9628_ = lean_ctor_get(v_oldState_9622_, 0);
    v___f_9629_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_9629_, 0, v_inst_9619_);
    lean_closure_set(v___f_9629_, 1, v_inst_9620_);
    lean_closure_set(v___f_9629_, 2, v_snd_9627_);
    lean_closure_set(v___f_9629_, 3, v_inst_9621_);
    v___x_9630_ = l_List_lengthTR___redArg(v_fst_9626_);
    v___x_9631_ = l_List_lengthTR___redArg(v_fst_9628_);
    v___x_9632_ = lean_nat_sub(v___x_9630_, v___x_9631_);
    lean_dec(v___x_9631_);
    lean_dec(v___x_9630_);
    v___x_9633_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___closed__0;
    v_newEntries_9634_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_fst_9626_,
        v_fst_9626_,
        v___x_9632_,
        v___x_9633_,
    );
    lean_dec(v_fst_9626_);
    v___x_9635_ = l_List_foldl___redArg(v___f_9629_, v_s_9625_, v_newEntries_9634_);
    return v___x_9635_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed(
    mut v_inst_9636_: *mut LeanObject,
    mut v_inst_9637_: *mut LeanObject,
    mut v_inst_9638_: *mut LeanObject,
    mut v_oldState_9639_: *mut LeanObject,
    mut v_newState_9640_: *mut LeanObject,
    mut v_x_9641_: *mut LeanObject,
    mut v_s_9642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9643_: *mut LeanObject = core::ptr::null_mut();
    v_res_9643_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1(
        v_inst_9636_,
        v_inst_9637_,
        v_inst_9638_,
        v_oldState_9639_,
        v_newState_9640_,
        v_x_9641_,
        v_s_9642_,
    );
    lean_dec(v_x_9641_);
    lean_dec_ref(v_oldState_9639_);
    return v_res_9643_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_9644_: *mut LeanObject = core::ptr::null_mut();
    v___x_9644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_9644_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_9645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9646_: *mut LeanObject = core::ptr::null_mut();
    v___x_9645_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__0,
    );
    v___x_9646_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9646_, 0, v___x_9645_);
    return v___x_9646_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_9647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9649_: *mut LeanObject = core::ptr::null_mut();
    v___x_9647_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__1,
    );
    v___x_9648_ = lean_box(0);
    v___x_9649_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_9649_, 0, v___x_9648_);
    lean_ctor_set(v___x_9649_, 1, v___x_9647_);
    return v___x_9649_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_9650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9651_: *mut LeanObject = core::ptr::null_mut();
    v___x_9650_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__2,
    );
    v___x_9651_ = lean_alloc_closure(
        l_instMonadEIO___aux__5___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_9651_, 0, lean_box(0));
    lean_closure_set(v___x_9651_, 1, lean_box(0));
    lean_closure_set(v___x_9651_, 2, v___x_9650_);
    return v___x_9651_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
    mut v_inst_9652_: *mut LeanObject,
    mut v_inst_9653_: *mut LeanObject,
    mut v_inst_9654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9664_: u8 = 0;
    let mut v___x_9666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9668_: u8 = 0;
    let mut v_a_9669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9672_: u8 = 0;
    let mut v___x_9674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_9656_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_CacheExtension_register___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_9656_, 0, v_inst_9652_);
                lean_closure_set(v___f_9656_, 1, v_inst_9653_);
                lean_closure_set(v___f_9656_, 2, v_inst_9654_);
                v___x_9657_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_CacheExtension_register___redArg___closed__3,
                );
                v___x_9658_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9658_, 0, v___f_9656_);
                v___x_9659_ = lean_box(0);
                v___x_9660_ =
                    l_Lean_registerEnvExtension___redArg(v___x_9657_, v___x_9658_, v___x_9659_);
                if lean_obj_tag(v___x_9660_) == 0 {
                    v_a_9661_ = lean_ctor_get(v___x_9660_, 0);
                    v_isSharedCheck_9668_ = (!lean_is_exclusive(v___x_9660_)) as u8;
                    if v_isSharedCheck_9668_ == 0 {
                        v___x_9663_ = v___x_9660_;
                        v_isShared_9664_ = v_isSharedCheck_9668_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9661_);
                        lean_dec(v___x_9660_);
                        v___x_9663_ = lean_box(0);
                        v_isShared_9664_ = v_isSharedCheck_9668_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9669_ = lean_ctor_get(v___x_9660_, 0);
                    v_isSharedCheck_9676_ = (!lean_is_exclusive(v___x_9660_)) as u8;
                    if v_isSharedCheck_9676_ == 0 {
                        v___x_9671_ = v___x_9660_;
                        v_isShared_9672_ = v_isSharedCheck_9676_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9669_);
                        lean_dec(v___x_9660_);
                        v___x_9671_ = lean_box(0);
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
                    v_reuseFailAlloc_9667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9667_, 0, v_a_9661_);
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
                    v_reuseFailAlloc_9675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9675_, 0, v_a_9669_);
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
    mut v_inst_9677_: *mut LeanObject,
    mut v_inst_9678_: *mut LeanObject,
    mut v_inst_9679_: *mut LeanObject,
    mut v_a_9680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9681_: *mut LeanObject = core::ptr::null_mut();
    v_res_9681_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
        v_inst_9677_,
        v_inst_9678_,
        v_inst_9679_,
    );
    return v_res_9681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register(
    mut v_00_u03b1_9682_: *mut LeanObject,
    mut v_00_u03b2_9683_: *mut LeanObject,
    mut v_inst_9684_: *mut LeanObject,
    mut v_inst_9685_: *mut LeanObject,
    mut v_inst_9686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9688_: *mut LeanObject = core::ptr::null_mut();
    v___x_9688_ = l_Lean_Compiler_LCNF_CacheExtension_register___redArg(
        v_inst_9684_,
        v_inst_9685_,
        v_inst_9686_,
    );
    return v___x_9688_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___boxed(
    mut v_00_u03b1_9689_: *mut LeanObject,
    mut v_00_u03b2_9690_: *mut LeanObject,
    mut v_inst_9691_: *mut LeanObject,
    mut v_inst_9692_: *mut LeanObject,
    mut v_inst_9693_: *mut LeanObject,
    mut v_a_9694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9695_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_9696_: *mut LeanObject,
    mut v_inst_9697_: *mut LeanObject,
    mut v_inst_9698_: *mut LeanObject,
    mut v_b_9699_: *mut LeanObject,
    mut v_x_9700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_9701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9705_: u8 = 0;
    let mut v___x_9706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_9701_ = lean_ctor_get(v_x_9700_, 0);
                v_snd_9702_ = lean_ctor_get(v_x_9700_, 1);
                v_isSharedCheck_9711_ = (!lean_is_exclusive(v_x_9700_)) as u8;
                if v_isSharedCheck_9711_ == 0 {
                    v___x_9704_ = v_x_9700_;
                    v_isShared_9705_ = v_isSharedCheck_9711_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_9702_);
                    lean_inc(v_fst_9701_);
                    lean_dec(v_x_9700_);
                    v___x_9704_ = lean_box(0);
                    v_isShared_9705_ = v_isSharedCheck_9711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_9696_);
                v___x_9706_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_9706_, 0, v_a_9696_);
                lean_ctor_set(v___x_9706_, 1, v_fst_9701_);
                v___x_9707_ = l_Lean_PersistentHashMap_insert___redArg(
                    v_inst_9697_,
                    v_inst_9698_,
                    v_snd_9702_,
                    v_a_9696_,
                    v_b_9699_,
                );
                if v_isShared_9705_ == 0 {
                    lean_ctor_set(v___x_9704_, 1, v___x_9707_);
                    lean_ctor_set(v___x_9704_, 0, v___x_9706_);
                    v___x_9709_ = v___x_9704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9710_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9710_, 0, v___x_9706_);
                    lean_ctor_set(v_reuseFailAlloc_9710_, 1, v___x_9707_);
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
-> *mut LeanObject {
    let mut v___x_9712_: *mut LeanObject = core::ptr::null_mut();
    v___x_9712_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_9712_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9714_: *mut LeanObject = core::ptr::null_mut();
    v___x_9713_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__0,
    );
    v___x_9714_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9714_, 0, v___x_9713_);
    return v___x_9714_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9716_: *mut LeanObject = core::ptr::null_mut();
    v___x_9715_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__1,
    );
    v___x_9716_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_9716_, 0, v___x_9715_);
    lean_ctor_set(v___x_9716_, 1, v___x_9715_);
    return v___x_9716_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(
    mut v_inst_9717_: *mut LeanObject,
    mut v_inst_9718_: *mut LeanObject,
    mut v_ext_9719_: *mut LeanObject,
    mut v_a_9720_: *mut LeanObject,
    mut v_b_9721_: *mut LeanObject,
    mut v_a_9722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_9726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_9727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_9728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_9729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_9730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_9731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_9732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9735_: u8 = 0;
    let mut v_asyncMode_9736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9747_: u8 = 0;
    let mut v_unused_9748_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9724_ = lean_st_ref_take(v_a_9722_);
                v_env_9725_ = lean_ctor_get(v___x_9724_, 0);
                v_nextMacroScope_9726_ = lean_ctor_get(v___x_9724_, 1);
                v_ngen_9727_ = lean_ctor_get(v___x_9724_, 2);
                v_auxDeclNGen_9728_ = lean_ctor_get(v___x_9724_, 3);
                v_traceState_9729_ = lean_ctor_get(v___x_9724_, 4);
                v_messages_9730_ = lean_ctor_get(v___x_9724_, 6);
                v_infoState_9731_ = lean_ctor_get(v___x_9724_, 7);
                v_snapshotTasks_9732_ = lean_ctor_get(v___x_9724_, 8);
                v_isSharedCheck_9747_ = (!lean_is_exclusive(v___x_9724_)) as u8;
                if v_isSharedCheck_9747_ == 0 {
                    v_unused_9748_ = lean_ctor_get(v___x_9724_, 5);
                    lean_dec(v_unused_9748_);
                    v___x_9734_ = v___x_9724_;
                    v_isShared_9735_ = v_isSharedCheck_9747_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_9732_);
                    lean_inc(v_infoState_9731_);
                    lean_inc(v_messages_9730_);
                    lean_inc(v_traceState_9729_);
                    lean_inc(v_auxDeclNGen_9728_);
                    lean_inc(v_ngen_9727_);
                    lean_inc(v_nextMacroScope_9726_);
                    lean_inc(v_env_9725_);
                    lean_dec(v___x_9724_);
                    v___x_9734_ = lean_box(0);
                    v_isShared_9735_ = v_isSharedCheck_9747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_9736_ = lean_ctor_get(v_ext_9719_, 2);
                lean_inc(v_asyncMode_9736_);
                v___f_9737_ = lean_alloc_closure(
                    l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___lam__0
                        as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_9737_, 0, v_a_9720_);
                lean_closure_set(v___f_9737_, 1, v_inst_9717_);
                lean_closure_set(v___f_9737_, 2, v_inst_9718_);
                lean_closure_set(v___f_9737_, 3, v_b_9721_);
                v___x_9738_ = lean_box(0);
                v___x_9739_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_9719_,
                    v_env_9725_,
                    v___f_9737_,
                    v_asyncMode_9736_,
                    v___x_9738_,
                );
                lean_dec(v_asyncMode_9736_);
                v___x_9740_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___closed__2,
                );
                if v_isShared_9735_ == 0 {
                    lean_ctor_set(v___x_9734_, 5, v___x_9740_);
                    lean_ctor_set(v___x_9734_, 0, v___x_9739_);
                    v___x_9742_ = v___x_9734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9746_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 0, v___x_9739_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 1, v_nextMacroScope_9726_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 2, v_ngen_9727_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 3, v_auxDeclNGen_9728_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 4, v_traceState_9729_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 5, v___x_9740_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 6, v_messages_9730_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 7, v_infoState_9731_);
                    lean_ctor_set(v_reuseFailAlloc_9746_, 8, v_snapshotTasks_9732_);
                    v___x_9742_ = v_reuseFailAlloc_9746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9743_ = lean_st_ref_set(v_a_9722_, v___x_9742_);
                v___x_9744_ = lean_box(0);
                v___x_9745_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9745_, 0, v___x_9744_);
                return v___x_9745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___redArg___boxed(
    mut v_inst_9749_: *mut LeanObject,
    mut v_inst_9750_: *mut LeanObject,
    mut v_ext_9751_: *mut LeanObject,
    mut v_a_9752_: *mut LeanObject,
    mut v_b_9753_: *mut LeanObject,
    mut v_a_9754_: *mut LeanObject,
    mut v_a_9755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9756_: *mut LeanObject = core::ptr::null_mut();
    v_res_9756_ = l_Lean_Compiler_LCNF_CacheExtension_insert___redArg(
        v_inst_9749_,
        v_inst_9750_,
        v_ext_9751_,
        v_a_9752_,
        v_b_9753_,
        v_a_9754_,
    );
    lean_dec(v_a_9754_);
    return v_res_9756_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert(
    mut v_00_u03b1_9757_: *mut LeanObject,
    mut v_00_u03b2_9758_: *mut LeanObject,
    mut v_inst_9759_: *mut LeanObject,
    mut v_inst_9760_: *mut LeanObject,
    mut v_inst_9761_: *mut LeanObject,
    mut v_ext_9762_: *mut LeanObject,
    mut v_a_9763_: *mut LeanObject,
    mut v_b_9764_: *mut LeanObject,
    mut v_a_9765_: *mut LeanObject,
    mut v_a_9766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9768_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_9769_: *mut LeanObject,
    mut v_00_u03b2_9770_: *mut LeanObject,
    mut v_inst_9771_: *mut LeanObject,
    mut v_inst_9772_: *mut LeanObject,
    mut v_inst_9773_: *mut LeanObject,
    mut v_ext_9774_: *mut LeanObject,
    mut v_a_9775_: *mut LeanObject,
    mut v_b_9776_: *mut LeanObject,
    mut v_a_9777_: *mut LeanObject,
    mut v_a_9778_: *mut LeanObject,
    mut v_a_9779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9780_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_9778_);
    lean_dec_ref(v_a_9777_);
    lean_dec(v_inst_9773_);
    return v_res_9780_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(
    mut v_inst_9781_: *mut LeanObject,
    mut v_inst_9782_: *mut LeanObject,
    mut v_ext_9783_: *mut LeanObject,
    mut v_a_9784_: *mut LeanObject,
    mut v_a_9785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_9788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_9789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9797_: *mut LeanObject = core::ptr::null_mut();
    v___x_9787_ = lean_st_ref_get(v_a_9785_);
    v_env_9788_ = lean_ctor_get(v___x_9787_, 0);
    lean_inc_ref(v_env_9788_);
    lean_dec(v___x_9787_);
    v_asyncMode_9789_ = lean_ctor_get(v_ext_9783_, 2);
    v___x_9790_ = lean_box(0);
    v___x_9791_ = l_Lean_PersistentHashMap_instInhabited(
        lean_box(0),
        lean_box(0),
        v_inst_9781_,
        v_inst_9782_,
    );
    v___x_9792_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_9792_, 0, v___x_9790_);
    lean_ctor_set(v___x_9792_, 1, v___x_9791_);
    v___x_9793_ = lean_box(0);
    v___x_9794_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_9792_,
        v_ext_9783_,
        v_env_9788_,
        v_asyncMode_9789_,
        v___x_9793_,
    );
    lean_dec_ref_known(v___x_9792_, 2);
    v_snd_9795_ = lean_ctor_get(v___x_9794_, 1);
    lean_inc(v_snd_9795_);
    lean_dec(v___x_9794_);
    v___x_9796_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v_inst_9781_,
        v_inst_9782_,
        v_snd_9795_,
        v_a_9784_,
    );
    lean_dec(v_snd_9795_);
    v___x_9797_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9797_, 0, v___x_9796_);
    return v___x_9797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg___boxed(
    mut v_inst_9798_: *mut LeanObject,
    mut v_inst_9799_: *mut LeanObject,
    mut v_ext_9800_: *mut LeanObject,
    mut v_a_9801_: *mut LeanObject,
    mut v_a_9802_: *mut LeanObject,
    mut v_a_9803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9804_: *mut LeanObject = core::ptr::null_mut();
    v_res_9804_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___redArg(
        v_inst_9798_,
        v_inst_9799_,
        v_ext_9800_,
        v_a_9801_,
        v_a_9802_,
    );
    lean_dec(v_a_9802_);
    lean_dec_ref(v_ext_9800_);
    return v_res_9804_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f(
    mut v_00_u03b1_9805_: *mut LeanObject,
    mut v_00_u03b2_9806_: *mut LeanObject,
    mut v_inst_9807_: *mut LeanObject,
    mut v_inst_9808_: *mut LeanObject,
    mut v_inst_9809_: *mut LeanObject,
    mut v_ext_9810_: *mut LeanObject,
    mut v_a_9811_: *mut LeanObject,
    mut v_a_9812_: *mut LeanObject,
    mut v_a_9813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9815_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_9816_: *mut LeanObject,
    mut v_00_u03b2_9817_: *mut LeanObject,
    mut v_inst_9818_: *mut LeanObject,
    mut v_inst_9819_: *mut LeanObject,
    mut v_inst_9820_: *mut LeanObject,
    mut v_ext_9821_: *mut LeanObject,
    mut v_a_9822_: *mut LeanObject,
    mut v_a_9823_: *mut LeanObject,
    mut v_a_9824_: *mut LeanObject,
    mut v_a_9825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9826_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_9824_);
    lean_dec_ref(v_a_9823_);
    lean_dec_ref(v_ext_9821_);
    lean_dec(v_inst_9820_);
    return v_res_9826_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedPhase_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedPhase_default();
    l_Lean_Compiler_LCNF_instInhabitedPhase = _init_l_Lean_Compiler_LCNF_instInhabitedPhase();
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState_default);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedState =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedState();
    lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedState);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext_default);
    l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext =
        _init_l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext();
    lean_mark_persistent(l_Lean_Compiler_LCNF_CompilerM_instInhabitedContext);
    l_Lean_Compiler_LCNF_instMonadCompilerM = _init_l_Lean_Compiler_LCNF_instMonadCompilerM();
    lean_mark_persistent(l_Lean_Compiler_LCNF_instMonadCompilerM);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_CompilerM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_CompilerM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_CompilerM(builtin);
}
