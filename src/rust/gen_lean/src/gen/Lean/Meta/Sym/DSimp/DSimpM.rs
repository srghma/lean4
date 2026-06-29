// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.DSimpM
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.ExprPtr
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get, lean_sym_dsimp};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwError___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instAddMessageContextMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr, runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value:
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
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value:
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
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value:
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
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value:
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
    m_data: [60, 100, 101, 102, 97, 117, 108, 116, 62, 0],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = crate::leanh::lean_unsigned_to_nat(100000);
    return v___x_566_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = crate::leanh::lean_unsigned_to_nat(100000);
    return v___x_567_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorIdx(
    mut v_x_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_568_) == 0 {
        let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_569_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_569_;
    } else {
        let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_570_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_570_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorIdx___boxed(
    mut v_x_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l_Lean_Meta_Sym_DSimp_Result_ctorIdx(v_x_571_);
    crate::leanh::lean_dec_ref(v_x_571_);
    return v_res_572_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(
    mut v_t_573_: *mut crate::leanh::LeanObject,
    mut v_k_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_573_) == 0 {
        let mut v_done_575_: u8 = 0;
        let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_done_575_ = crate::leanh::lean_ctor_get_uint8(v_t_573_, 0 as u32);
        crate::leanh::lean_dec_ref_known(v_t_573_, 0);
        v___x_576_ = crate::leanh::lean_box((v_done_575_) as usize);
        v___x_577_ = crate::leanh::lean_apply_1(v_k_574_, v___x_576_);
        return v___x_577_;
    } else {
        let mut v_e_x27_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_done_579_: u8 = 0;
        let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_x27_578_ = crate::leanh::lean_ctor_get(v_t_573_, 0);
        crate::leanh::lean_inc_ref(v_e_x27_578_);
        v_done_579_ = crate::leanh::lean_ctor_get_uint8(
            v_t_573_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_t_573_, 1);
        v___x_580_ = crate::leanh::lean_box((v_done_579_) as usize);
        v___x_581_ = crate::leanh::lean_apply_2(v_k_574_, v_e_x27_578_, v___x_580_);
        return v___x_581_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim(
    mut v_motive_582_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_583_: *mut crate::leanh::LeanObject,
    mut v_t_584_: *mut crate::leanh::LeanObject,
    mut v_h_585_: *mut crate::leanh::LeanObject,
    mut v_k_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_584_, v_k_586_);
    return v___x_587_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim___boxed(
    mut v_motive_588_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_589_: *mut crate::leanh::LeanObject,
    mut v_t_590_: *mut crate::leanh::LeanObject,
    mut v_h_591_: *mut crate::leanh::LeanObject,
    mut v_k_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_593_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim(
        v_motive_588_,
        v_ctorIdx_589_,
        v_t_590_,
        v_h_591_,
        v_k_592_,
    );
    crate::leanh::lean_dec(v_ctorIdx_589_);
    return v_res_593_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_rfl_elim___redArg(
    mut v_t_594_: *mut crate::leanh::LeanObject,
    mut v_rfl_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_594_, v_rfl_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_rfl_elim(
    mut v_motive_597_: *mut crate::leanh::LeanObject,
    mut v_t_598_: *mut crate::leanh::LeanObject,
    mut v_h_599_: *mut crate::leanh::LeanObject,
    mut v_rfl_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_598_, v_rfl_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_step_elim___redArg(
    mut v_t_602_: *mut crate::leanh::LeanObject,
    mut v_step_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_602_, v_step_603_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_step_elim(
    mut v_motive_605_: *mut crate::leanh::LeanObject,
    mut v_t_606_: *mut crate::leanh::LeanObject,
    mut v_h_607_: *mut crate::leanh::LeanObject,
    mut v_step_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_606_, v_step_608_);
    return v___x_609_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed()
-> *mut crate::leanh::LeanObject {
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = crate::leanh::lean_box(0);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_615_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_616_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0,
    );
    v___x_617_ = l_StateRefT_x27_instMonad___redArg(v___x_616_);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_623_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_623_, 0, v___x_622_);
    return v___f_623_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_625_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_625_, 0, v___x_624_);
    return v___f_625_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___f_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_626_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7,
    );
    v___f_627_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6,
    );
    v___x_628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_628_, 0, v___f_627_);
    crate::leanh::lean_ctor_set(v___x_628_, 1, v___f_626_);
    return v___x_628_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8,
    );
    v___f_630_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_630_, 0, v___x_629_);
    return v___f_630_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8,
    );
    v___f_632_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_632_, 0, v___x_631_);
    return v___f_632_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___f_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10,
    );
    v___f_634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9,
    );
    v___x_635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_635_, 0, v___f_634_);
    crate::leanh::lean_ctor_set(v___x_635_, 1, v___f_633_);
    return v___x_635_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11,
    );
    v___f_637_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_637_, 0, v___x_636_);
    return v___f_637_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11,
    );
    v___f_639_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_639_, 0, v___x_638_);
    return v___f_639_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___f_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13,
    );
    v___f_641_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12,
    );
    v___x_642_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_642_, 0, v___f_641_);
    crate::leanh::lean_ctor_set(v___x_642_, 1, v___f_640_);
    return v___x_642_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14,
    );
    v___f_644_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_644_, 0, v___x_643_);
    return v___f_644_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14,
    );
    v___f_646_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_646_, 0, v___x_645_);
    return v___f_646_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___f_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16,
    );
    v___f_648_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15,
    );
    v___x_649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_649_, 0, v___f_648_);
    crate::leanh::lean_ctor_set(v___x_649_, 1, v___f_647_);
    return v___x_649_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17,
    );
    v___f_651_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_651_, 0, v___x_650_);
    return v___f_651_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17,
    );
    v___f_653_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_653_, 0, v___x_652_);
    return v___f_653_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___f_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19,
    );
    v___f_655_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18,
    );
    v___x_656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_656_, 0, v___f_655_);
    crate::leanh::lean_ctor_set(v___x_656_, 1, v___f_654_);
    return v___x_656_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20,
    );
    v___f_658_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_658_, 0, v___x_657_);
    return v___f_658_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20,
    );
    v___f_660_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_660_, 0, v___x_659_);
    return v___f_660_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___f_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22,
    );
    v___f_662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21,
    );
    v___x_663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_663_, 0, v___f_662_);
    crate::leanh::lean_ctor_set(v___x_663_, 1, v___f_661_);
    return v___x_663_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23,
    );
    v___f_665_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_665_, 0, v___x_664_);
    return v___f_665_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23,
    );
    v___f_667_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_667_, 0, v___x_666_);
    return v___f_667_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_668_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25,
    );
    v___f_669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24,
    );
    v___x_670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_670_, 0, v___f_669_);
    crate::leanh::lean_ctor_set(v___x_670_, 1, v___f_668_);
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_676_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_677_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29;
    v___x_678_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_677_, v___x_676_, v___x_675_,
    );
    return v___x_678_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31,
    );
    v___f_680_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_681_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27;
    v___x_682_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_681_, v___f_680_, v___x_679_,
    );
    return v___x_682_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32,
    );
    v___x_684_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_685_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29;
    v___x_686_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_685_, v___x_684_, v___x_683_,
    );
    return v___x_686_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33,
    );
    v___f_688_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_689_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27;
    v___x_690_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_689_, v___f_688_, v___x_687_,
    );
    return v___x_690_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34,
    );
    v___x_692_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_693_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29;
    v___x_694_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_693_, v___x_692_, v___x_691_,
    );
    return v___x_694_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35,
    );
    v___f_696_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_697_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27;
    v___x_698_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_697_, v___f_696_, v___x_695_,
    );
    return v___x_698_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36,
    );
    v___f_700_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_701_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27;
    v___x_702_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_701_, v___f_700_, v___x_699_,
    );
    return v___x_702_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_704_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_705_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_705_, 0, v___x_704_);
    crate::leanh::lean_closure_set(v___f_705_, 1, v___x_703_);
    return v___f_705_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___f_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_706_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_707_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38,
    );
    v___f_708_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_708_, 0, v___f_707_);
    crate::leanh::lean_closure_set(v___f_708_, 1, v___f_706_);
    return v___f_708_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___f_710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39,
    );
    v___f_711_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_711_, 0, v___f_710_);
    crate::leanh::lean_closure_set(v___f_711_, 1, v___x_709_);
    return v___f_711_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___f_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_712_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40,
    );
    v___f_714_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_714_, 0, v___f_713_);
    crate::leanh::lean_closure_set(v___f_714_, 1, v___f_712_);
    return v___f_714_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___f_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_715_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41,
    );
    v___f_717_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_717_, 0, v___f_716_);
    crate::leanh::lean_closure_set(v___f_717_, 1, v___f_715_);
    return v___f_717_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43;
    v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
    return v___x_720_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(
    mut v_00_u03b1_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v_toFunctor_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v___f_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut v_unused_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_unused_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1,
                );
                v_toApplicative_723_ = crate::leanh::lean_ctor_get(v___x_722_, 0);
                v_toFunctor_724_ = crate::leanh::lean_ctor_get(v_toApplicative_723_, 0);
                v_toSeq_725_ = crate::leanh::lean_ctor_get(v_toApplicative_723_, 2);
                v_toSeqLeft_726_ = crate::leanh::lean_ctor_get(v_toApplicative_723_, 3);
                v_toSeqRight_727_ = crate::leanh::lean_ctor_get(v_toApplicative_723_, 4);
                v___f_728_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2;
                v___f_729_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_724_, 2);
                v___f_730_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_730_, 0, v_toFunctor_724_);
                v___f_731_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_731_, 0, v_toFunctor_724_);
                v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_732_, 0, v___f_730_);
                crate::leanh::lean_ctor_set(v___x_732_, 1, v___f_731_);
                crate::leanh::lean_inc(v_toSeqRight_727_);
                v___f_733_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_733_, 0, v_toSeqRight_727_);
                crate::leanh::lean_inc(v_toSeqLeft_726_);
                v___f_734_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_734_, 0, v_toSeqLeft_726_);
                crate::leanh::lean_inc(v_toSeq_725_);
                v___f_735_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_735_, 0, v_toSeq_725_);
                v___x_736_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_736_, 0, v___x_732_);
                crate::leanh::lean_ctor_set(v___x_736_, 1, v___f_728_);
                crate::leanh::lean_ctor_set(v___x_736_, 2, v___f_735_);
                crate::leanh::lean_ctor_set(v___x_736_, 3, v___f_734_);
                crate::leanh::lean_ctor_set(v___x_736_, 4, v___f_733_);
                v___x_737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_737_, 0, v___x_736_);
                crate::leanh::lean_ctor_set(v___x_737_, 1, v___f_729_);
                v___x_738_ = l_StateRefT_x27_instMonad___redArg(v___x_737_);
                v_toApplicative_739_ = crate::leanh::lean_ctor_get(v___x_738_, 0);
                v_isSharedCheck_779_ = (!crate::leanh::lean_is_exclusive(v___x_738_)) as u8;
                if v_isSharedCheck_779_ == 0 {
                    v_unused_780_ = crate::leanh::lean_ctor_get(v___x_738_, 1);
                    crate::leanh::lean_dec(v_unused_780_);
                    v___x_741_ = v___x_738_;
                    v_isShared_742_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_739_);
                    crate::leanh::lean_dec(v___x_738_);
                    v___x_741_ = crate::leanh::lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_743_ = crate::leanh::lean_ctor_get(v_toApplicative_739_, 0);
                v_toSeq_744_ = crate::leanh::lean_ctor_get(v_toApplicative_739_, 2);
                v_toSeqLeft_745_ = crate::leanh::lean_ctor_get(v_toApplicative_739_, 3);
                v_toSeqRight_746_ = crate::leanh::lean_ctor_get(v_toApplicative_739_, 4);
                v_isSharedCheck_777_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_739_)) as u8;
                if v_isSharedCheck_777_ == 0 {
                    v_unused_778_ = crate::leanh::lean_ctor_get(v_toApplicative_739_, 1);
                    crate::leanh::lean_dec(v_unused_778_);
                    v___x_748_ = v_toApplicative_739_;
                    v_isShared_749_ = v_isSharedCheck_777_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_746_);
                    crate::leanh::lean_inc(v_toSeqLeft_745_);
                    crate::leanh::lean_inc(v_toSeq_744_);
                    crate::leanh::lean_inc(v_toFunctor_743_);
                    crate::leanh::lean_dec(v_toApplicative_739_);
                    v___x_748_ = crate::leanh::lean_box(0);
                    v_isShared_749_ = v_isSharedCheck_777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_750_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4;
                v___f_751_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_743_);
                v___f_752_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_752_, 0, v_toFunctor_743_);
                v___f_753_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_753_, 0, v_toFunctor_743_);
                v___x_754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_754_, 0, v___f_752_);
                crate::leanh::lean_ctor_set(v___x_754_, 1, v___f_753_);
                v___f_755_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_755_, 0, v_toSeqRight_746_);
                v___f_756_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_756_, 0, v_toSeqLeft_745_);
                v___f_757_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_757_, 0, v_toSeq_744_);
                if v_isShared_749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_748_, 4, v___f_755_);
                    crate::leanh::lean_ctor_set(v___x_748_, 3, v___f_756_);
                    crate::leanh::lean_ctor_set(v___x_748_, 2, v___f_757_);
                    crate::leanh::lean_ctor_set(v___x_748_, 1, v___f_750_);
                    crate::leanh::lean_ctor_set(v___x_748_, 0, v___x_754_);
                    v___x_759_ = v___x_748_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 1, v___f_750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 2, v___f_757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 3, v___f_756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 4, v___f_755_);
                    v___x_759_ = v_reuseFailAlloc_776_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_741_, 1, v___f_751_);
                    crate::leanh::lean_ctor_set(v___x_741_, 0, v___x_759_);
                    v___x_761_ = v___x_741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_775_, 1, v___f_751_);
                    v___x_761_ = v_reuseFailAlloc_775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_762_ = l_StateRefT_x27_instMonad___redArg(v___x_761_);
                v___x_763_ = l_ReaderT_instMonad___redArg(v___x_762_);
                v___x_764_ = l_StateRefT_x27_instMonad___redArg(v___x_763_);
                v___x_765_ = l_ReaderT_instMonad___redArg(v___x_764_);
                v___x_766_ = l_ReaderT_instMonad___redArg(v___x_765_);
                v___x_767_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26,
                );
                v___x_768_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37,
                );
                v_toMonadRef_769_ = crate::leanh::lean_ctor_get(v___x_768_, 0);
                v___f_770_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42,
                );
                crate::leanh::lean_inc_ref(v___x_766_);
                v___x_771_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_770_, v___x_766_,
                );
                crate::leanh::lean_inc_ref(v_toMonadRef_769_);
                v___x_772_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_767_);
                crate::leanh::lean_ctor_set(v___x_772_, 1, v_toMonadRef_769_);
                crate::leanh::lean_ctor_set(v___x_772_, 2, v___x_771_);
                v___x_773_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44,
                );
                v___x_774_ = l_Lean_throwError___redArg(v___x_766_, v___x_772_, v___x_773_);
                return v___x_774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(
    mut v_x_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
    mut v___y_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0;
    v___x_793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_792_);
    return v___x_793_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(
    mut v_x_794_: *mut crate::leanh::LeanObject,
    mut v___y_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
    mut v___y_798_: *mut crate::leanh::LeanObject,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
    mut v___y_802_: *mut crate::leanh::LeanObject,
    mut v___y_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(
        v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_,
        v___y_801_, v___y_802_, v___y_803_,
    );
    crate::leanh::lean_dec(v___y_803_);
    crate::leanh::lean_dec_ref(v___y_802_);
    crate::leanh::lean_dec(v___y_801_);
    crate::leanh::lean_dec_ref(v___y_800_);
    crate::leanh::lean_dec(v___y_799_);
    crate::leanh::lean_dec_ref(v___y_798_);
    crate::leanh::lean_dec(v___y_797_);
    crate::leanh::lean_dec(v___y_796_);
    crate::leanh::lean_dec(v___y_795_);
    crate::leanh::lean_dec_ref(v_x_794_);
    return v_res_805_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(
    mut v_m_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_m_811_);
    return v_m_811_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(
    mut v_m_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(v_m_812_);
    crate::leanh::lean_dec_ref(v_m_812_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(
    mut v_m_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_m_814_);
    return v_m_814_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(
    mut v_m_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(v_m_815_);
    crate::leanh::lean_dec(v_m_815_);
    return v_res_816_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___redArg(
    mut v_a_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_817_);
    v___x_819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_819_, 0, v_a_817_);
    return v___x_819_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_820_);
    crate::leanh::lean_dec(v_a_820_);
    return v_res_822_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods(
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
    mut v_a_830_: *mut crate::leanh::LeanObject,
    mut v_a_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_823_);
    v___x_833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_833_, 0, v_a_823_);
    return v___x_833_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___boxed(
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Lean_Meta_Sym_DSimp_getMethods(
        v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_,
    );
    crate::leanh::lean_dec(v_a_842_);
    crate::leanh::lean_dec_ref(v_a_841_);
    crate::leanh::lean_dec(v_a_840_);
    crate::leanh::lean_dec_ref(v_a_839_);
    crate::leanh::lean_dec(v_a_838_);
    crate::leanh::lean_dec_ref(v_a_837_);
    crate::leanh::lean_dec(v_a_836_);
    crate::leanh::lean_dec(v_a_835_);
    crate::leanh::lean_dec(v_a_834_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(
    mut v_x_845_: *mut crate::leanh::LeanObject,
    mut v_methods_846_: *mut crate::leanh::LeanObject,
    mut v_config_847_: *mut crate::leanh::LeanObject,
    mut v_s_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cache_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_a_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_reuseFailAlloc_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_unused_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_856_ = crate::leanh::lean_ctor_get(v_s_848_, 1);
                v_isSharedCheck_884_ = (!crate::leanh::lean_is_exclusive(v_s_848_)) as u8;
                if v_isSharedCheck_884_ == 0 {
                    v_unused_885_ = crate::leanh::lean_ctor_get(v_s_848_, 0);
                    crate::leanh::lean_dec(v_unused_885_);
                    v___x_858_ = v_s_848_;
                    v_isShared_859_ = v_isSharedCheck_884_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cache_856_);
                    crate::leanh::lean_dec(v_s_848_);
                    v___x_858_ = crate::leanh::lean_box(0);
                    v_isShared_859_ = v_isSharedCheck_884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_860_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_883_, 1, v_cache_856_);
                    v___x_862_ = v_reuseFailAlloc_883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = lean_st_mk_ref(v___x_862_);
                crate::leanh::lean_inc(v_a_854_);
                crate::leanh::lean_inc_ref(v_a_853_);
                crate::leanh::lean_inc(v_a_852_);
                crate::leanh::lean_inc_ref(v_a_851_);
                crate::leanh::lean_inc(v_a_850_);
                crate::leanh::lean_inc_ref(v_a_849_);
                crate::leanh::lean_inc(v___x_863_);
                v___x_864_ = crate::leanh::lean_apply_10(
                    v_x_845_,
                    v_methods_846_,
                    v_config_847_,
                    v___x_863_,
                    v_a_849_,
                    v_a_850_,
                    v_a_851_,
                    v_a_852_,
                    v_a_853_,
                    v_a_854_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_874_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_874_ == 0 {
                        v___x_867_ = v___x_864_;
                        v_isShared_868_ = v_isSharedCheck_874_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_865_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_867_ = crate::leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_874_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_863_);
                    v_a_875_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_882_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_882_ == 0 {
                        v___x_877_ = v___x_864_;
                        v_isShared_878_ = v_isSharedCheck_882_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_875_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_877_ = crate::leanh::lean_box(0);
                        v_isShared_878_ = v_isSharedCheck_882_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_869_ = lean_st_ref_get(v___x_863_);
                crate::leanh::lean_dec(v___x_863_);
                v___x_870_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_870_, 0, v_a_865_);
                crate::leanh::lean_ctor_set(v___x_870_, 1, v___x_869_);
                if v_isShared_868_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_867_, 0, v___x_870_);
                    v___x_872_ = v___x_867_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_872_;
            }
            5 => {
                if v_isShared_878_ == 0 {
                    v___x_880_ = v___x_877_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
                    v___x_880_ = v_reuseFailAlloc_881_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg___boxed(
    mut v_x_886_: *mut crate::leanh::LeanObject,
    mut v_methods_887_: *mut crate::leanh::LeanObject,
    mut v_config_888_: *mut crate::leanh::LeanObject,
    mut v_s_889_: *mut crate::leanh::LeanObject,
    mut v_a_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
    mut v_a_892_: *mut crate::leanh::LeanObject,
    mut v_a_893_: *mut crate::leanh::LeanObject,
    mut v_a_894_: *mut crate::leanh::LeanObject,
    mut v_a_895_: *mut crate::leanh::LeanObject,
    mut v_a_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_897_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(
        v_x_886_,
        v_methods_887_,
        v_config_888_,
        v_s_889_,
        v_a_890_,
        v_a_891_,
        v_a_892_,
        v_a_893_,
        v_a_894_,
        v_a_895_,
    );
    crate::leanh::lean_dec(v_a_895_);
    crate::leanh::lean_dec_ref(v_a_894_);
    crate::leanh::lean_dec(v_a_893_);
    crate::leanh::lean_dec_ref(v_a_892_);
    crate::leanh::lean_dec(v_a_891_);
    crate::leanh::lean_dec_ref(v_a_890_);
    return v_res_897_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run(
    mut v_00_u03b1_898_: *mut crate::leanh::LeanObject,
    mut v_x_899_: *mut crate::leanh::LeanObject,
    mut v_methods_900_: *mut crate::leanh::LeanObject,
    mut v_config_901_: *mut crate::leanh::LeanObject,
    mut v_s_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
    mut v_a_904_: *mut crate::leanh::LeanObject,
    mut v_a_905_: *mut crate::leanh::LeanObject,
    mut v_a_906_: *mut crate::leanh::LeanObject,
    mut v_a_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(
        v_x_899_,
        v_methods_900_,
        v_config_901_,
        v_s_902_,
        v_a_903_,
        v_a_904_,
        v_a_905_,
        v_a_906_,
        v_a_907_,
        v_a_908_,
    );
    return v___x_910_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run___boxed(
    mut v_00_u03b1_911_: *mut crate::leanh::LeanObject,
    mut v_x_912_: *mut crate::leanh::LeanObject,
    mut v_methods_913_: *mut crate::leanh::LeanObject,
    mut v_config_914_: *mut crate::leanh::LeanObject,
    mut v_s_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_Lean_Meta_Sym_DSimp_DSimpM_run(
        v_00_u03b1_911_,
        v_x_912_,
        v_methods_913_,
        v_config_914_,
        v_s_915_,
        v_a_916_,
        v_a_917_,
        v_a_918_,
        v_a_919_,
        v_a_920_,
        v_a_921_,
    );
    crate::leanh::lean_dec(v_a_921_);
    crate::leanh::lean_dec_ref(v_a_920_);
    crate::leanh::lean_dec(v_a_919_);
    crate::leanh::lean_dec_ref(v_a_918_);
    crate::leanh::lean_dec(v_a_917_);
    crate::leanh::lean_dec_ref(v_a_916_);
    return v_res_923_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_924_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once),
        _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0,
    );
    v___x_926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_925_);
    return v___x_926_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1,
    );
    v___x_928_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_929_, 0, v___x_928_);
    crate::leanh::lean_ctor_set(v___x_929_, 1, v___x_927_);
    return v___x_929_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(
    mut v_x_930_: *mut crate::leanh::LeanObject,
    mut v_methods_931_: *mut crate::leanh::LeanObject,
    mut v_config_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_940_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2,
                );
                v___x_941_ = lean_st_mk_ref(v___x_940_);
                crate::leanh::lean_inc(v_a_938_);
                crate::leanh::lean_inc_ref(v_a_937_);
                crate::leanh::lean_inc(v_a_936_);
                crate::leanh::lean_inc_ref(v_a_935_);
                crate::leanh::lean_inc(v_a_934_);
                crate::leanh::lean_inc_ref(v_a_933_);
                crate::leanh::lean_inc(v___x_941_);
                v___x_942_ = crate::leanh::lean_apply_10(
                    v_x_930_,
                    v_methods_931_,
                    v_config_932_,
                    v___x_941_,
                    v_a_933_,
                    v_a_934_,
                    v_a_935_,
                    v_a_936_,
                    v_a_937_,
                    v_a_938_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_942_) == 0 {
                    v_a_943_ = crate::leanh::lean_ctor_get(v___x_942_, 0);
                    v_isSharedCheck_951_ = (!crate::leanh::lean_is_exclusive(v___x_942_)) as u8;
                    if v_isSharedCheck_951_ == 0 {
                        v___x_945_ = v___x_942_;
                        v_isShared_946_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_943_);
                        crate::leanh::lean_dec(v___x_942_);
                        v___x_945_ = crate::leanh::lean_box(0);
                        v_isShared_946_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_941_);
                    return v___x_942_;
                }
            }
            1 => {
                v___x_947_ = lean_st_ref_get(v___x_941_);
                crate::leanh::lean_dec(v___x_941_);
                crate::leanh::lean_dec(v___x_947_);
                if v_isShared_946_ == 0 {
                    v___x_949_ = v___x_945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_943_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___boxed(
    mut v_x_952_: *mut crate::leanh::LeanObject,
    mut v_methods_953_: *mut crate::leanh::LeanObject,
    mut v_config_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
    mut v_a_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(
        v_x_952_,
        v_methods_953_,
        v_config_954_,
        v_a_955_,
        v_a_956_,
        v_a_957_,
        v_a_958_,
        v_a_959_,
        v_a_960_,
    );
    crate::leanh::lean_dec(v_a_960_);
    crate::leanh::lean_dec_ref(v_a_959_);
    crate::leanh::lean_dec(v_a_958_);
    crate::leanh::lean_dec_ref(v_a_957_);
    crate::leanh::lean_dec(v_a_956_);
    crate::leanh::lean_dec_ref(v_a_955_);
    return v_res_962_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(
    mut v_00_u03b1_963_: *mut crate::leanh::LeanObject,
    mut v_x_964_: *mut crate::leanh::LeanObject,
    mut v_methods_965_: *mut crate::leanh::LeanObject,
    mut v_config_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
    mut v_a_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(
        v_x_964_,
        v_methods_965_,
        v_config_966_,
        v_a_967_,
        v_a_968_,
        v_a_969_,
        v_a_970_,
        v_a_971_,
        v_a_972_,
    );
    return v___x_974_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___boxed(
    mut v_00_u03b1_975_: *mut crate::leanh::LeanObject,
    mut v_x_976_: *mut crate::leanh::LeanObject,
    mut v_methods_977_: *mut crate::leanh::LeanObject,
    mut v_config_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(
        v_00_u03b1_975_,
        v_x_976_,
        v_methods_977_,
        v_config_978_,
        v_a_979_,
        v_a_980_,
        v_a_981_,
        v_a_982_,
        v_a_983_,
        v_a_984_,
    );
    crate::leanh::lean_dec(v_a_984_);
    crate::leanh::lean_dec_ref(v_a_983_);
    crate::leanh::lean_dec(v_a_982_);
    crate::leanh::lean_dec_ref(v_a_981_);
    crate::leanh::lean_dec(v_a_980_);
    crate::leanh::lean_dec_ref(v_a_979_);
    return v_res_986_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimp___boxed(
    mut v_a_00___x40___internal___hyg_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
    mut v_a_1001_: *mut crate::leanh::LeanObject,
    mut v_a_1002_: *mut crate::leanh::LeanObject,
    mut v_a_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_a_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = lean_sym_dsimp(
        v_a_00___x40___internal___hyg_998_,
        v_a_999_,
        v_a_1000_,
        v_a_1001_,
        v_a_1002_,
        v_a_1003_,
        v_a_1004_,
        v_a_1005_,
        v_a_1006_,
        v_a_1007_,
    );
    return v_res_1009_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig___redArg(
    mut v_a_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1010_);
    v___x_1012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1012_, 0, v_a_1010_);
    return v___x_1012_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_1013_);
    crate::leanh::lean_dec(v_a_1013_);
    return v_res_1015_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig(
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1017_);
    v___x_1026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1026_, 0, v_a_1017_);
    return v___x_1026_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig___boxed(
    mut v_a_1027_: *mut crate::leanh::LeanObject,
    mut v_a_1028_: *mut crate::leanh::LeanObject,
    mut v_a_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
    mut v_a_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
    mut v_a_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1037_ = l_Lean_Meta_Sym_DSimp_getConfig(
        v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_,
        v_a_1035_,
    );
    crate::leanh::lean_dec(v_a_1035_);
    crate::leanh::lean_dec_ref(v_a_1034_);
    crate::leanh::lean_dec(v_a_1033_);
    crate::leanh::lean_dec_ref(v_a_1032_);
    crate::leanh::lean_dec(v_a_1031_);
    crate::leanh::lean_dec_ref(v_a_1030_);
    crate::leanh::lean_dec(v_a_1029_);
    crate::leanh::lean_dec(v_a_1028_);
    crate::leanh::lean_dec(v_a_1027_);
    return v_res_1037_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_pre(
    mut v_e_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pre_1049_ = crate::leanh::lean_ctor_get(v_a_1039_, 0);
    crate::leanh::lean_inc_ref(v_pre_1049_);
    crate::leanh::lean_inc(v_a_1047_);
    crate::leanh::lean_inc_ref(v_a_1046_);
    crate::leanh::lean_inc(v_a_1045_);
    crate::leanh::lean_inc_ref(v_a_1044_);
    crate::leanh::lean_inc(v_a_1043_);
    crate::leanh::lean_inc_ref(v_a_1042_);
    crate::leanh::lean_inc(v_a_1041_);
    crate::leanh::lean_inc(v_a_1040_);
    crate::leanh::lean_inc(v_a_1039_);
    v___x_1050_ = crate::leanh::lean_apply_11(
        v_pre_1049_,
        v_e_1038_,
        v_a_1039_,
        v_a_1040_,
        v_a_1041_,
        v_a_1042_,
        v_a_1043_,
        v_a_1044_,
        v_a_1045_,
        v_a_1046_,
        v_a_1047_,
        crate::leanh::lean_box(0),
    );
    return v___x_1050_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_pre___boxed(
    mut v_e_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
    mut v_a_1054_: *mut crate::leanh::LeanObject,
    mut v_a_1055_: *mut crate::leanh::LeanObject,
    mut v_a_1056_: *mut crate::leanh::LeanObject,
    mut v_a_1057_: *mut crate::leanh::LeanObject,
    mut v_a_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
    mut v_a_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_Meta_Sym_DSimp_pre(
        v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_,
        v_a_1059_, v_a_1060_,
    );
    crate::leanh::lean_dec(v_a_1060_);
    crate::leanh::lean_dec_ref(v_a_1059_);
    crate::leanh::lean_dec(v_a_1058_);
    crate::leanh::lean_dec_ref(v_a_1057_);
    crate::leanh::lean_dec(v_a_1056_);
    crate::leanh::lean_dec_ref(v_a_1055_);
    crate::leanh::lean_dec(v_a_1054_);
    crate::leanh::lean_dec(v_a_1053_);
    crate::leanh::lean_dec(v_a_1052_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_post(
    mut v_e_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_post_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_post_1074_ = crate::leanh::lean_ctor_get(v_a_1064_, 1);
    crate::leanh::lean_inc_ref(v_post_1074_);
    crate::leanh::lean_inc(v_a_1072_);
    crate::leanh::lean_inc_ref(v_a_1071_);
    crate::leanh::lean_inc(v_a_1070_);
    crate::leanh::lean_inc_ref(v_a_1069_);
    crate::leanh::lean_inc(v_a_1068_);
    crate::leanh::lean_inc_ref(v_a_1067_);
    crate::leanh::lean_inc(v_a_1066_);
    crate::leanh::lean_inc(v_a_1065_);
    crate::leanh::lean_inc(v_a_1064_);
    v___x_1075_ = crate::leanh::lean_apply_11(
        v_post_1074_,
        v_e_1063_,
        v_a_1064_,
        v_a_1065_,
        v_a_1066_,
        v_a_1067_,
        v_a_1068_,
        v_a_1069_,
        v_a_1070_,
        v_a_1071_,
        v_a_1072_,
        crate::leanh::lean_box(0),
    );
    return v___x_1075_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_post___boxed(
    mut v_e_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_Lean_Meta_Sym_DSimp_post(
        v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_,
        v_a_1084_, v_a_1085_,
    );
    crate::leanh::lean_dec(v_a_1085_);
    crate::leanh::lean_dec_ref(v_a_1084_);
    crate::leanh::lean_dec(v_a_1083_);
    crate::leanh::lean_dec_ref(v_a_1082_);
    crate::leanh::lean_dec(v_a_1081_);
    crate::leanh::lean_dec_ref(v_a_1080_);
    crate::leanh::lean_dec(v_a_1079_);
    crate::leanh::lean_dec(v_a_1078_);
    crate::leanh::lean_dec(v_a_1077_);
    return v_res_1087_;
}
pub unsafe fn l_Lean_Meta_Sym_dsimp(
    mut v_e_1088_: *mut crate::leanh::LeanObject,
    mut v_methods_1089_: *mut crate::leanh::LeanObject,
    mut v_config_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
    mut v_a_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1103_: u8 = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_a_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1088_);
                v___x_1098_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_DSimp_dsimp___boxed as *mut core::ffi::c_void,
                    11,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_1098_, 0, v_e_1088_);
                v___x_1099_ = l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(
                    v___x_1098_,
                    v_methods_1089_,
                    v_config_1090_,
                    v_a_1091_,
                    v_a_1092_,
                    v_a_1093_,
                    v_a_1094_,
                    v_a_1095_,
                    v_a_1096_,
                );
                if crate::leanh::lean_obj_tag(v___x_1099_) == 0 {
                    v_a_1100_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1111_ = (!crate::leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1102_ = v___x_1099_;
                        v_isShared_1103_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1100_);
                        crate::leanh::lean_dec(v___x_1099_);
                        v___x_1102_ = crate::leanh::lean_box(0);
                        v_isShared_1103_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1088_);
                    v_a_1112_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1119_ = (!crate::leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1114_ = v___x_1099_;
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1112_);
                        crate::leanh::lean_dec(v___x_1099_);
                        v___x_1114_ = crate::leanh::lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1100_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_1100_, 0);
                    if v_isShared_1103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1102_, 0, v_e_1088_);
                        v___x_1105_ = v___x_1102_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_e_1088_);
                        v___x_1105_ = v_reuseFailAlloc_1106_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1088_);
                    v_e_x27_1107_ = crate::leanh::lean_ctor_get(v_a_1100_, 0);
                    crate::leanh::lean_inc_ref(v_e_x27_1107_);
                    crate::leanh::lean_dec_ref_known(v_a_1100_, 1);
                    if v_isShared_1103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1102_, 0, v_e_x27_1107_);
                        v___x_1109_ = v___x_1102_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_e_x27_1107_);
                        v___x_1109_ = v_reuseFailAlloc_1110_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1105_;
            }
            3 => {
                return v___x_1109_;
            }
            4 => {
                if v_isShared_1115_ == 0 {
                    v___x_1117_ = v___x_1114_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_dsimp___boxed(
    mut v_e_1120_: *mut crate::leanh::LeanObject,
    mut v_methods_1121_: *mut crate::leanh::LeanObject,
    mut v_config_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_Meta_Sym_dsimp(
        v_e_1120_,
        v_methods_1121_,
        v_config_1122_,
        v_a_1123_,
        v_a_1124_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
        v_a_1128_,
    );
    crate::leanh::lean_dec(v_a_1128_);
    crate::leanh::lean_dec_ref(v_a_1127_);
    crate::leanh::lean_dec(v_a_1126_);
    crate::leanh::lean_dec_ref(v_a_1125_);
    crate::leanh::lean_dec(v_a_1124_);
    crate::leanh::lean_dec_ref(v_a_1123_);
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default =
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default);
    l_Lean_Meta_Sym_DSimp_instInhabitedConfig = _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig);
    l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed =
        _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
}
