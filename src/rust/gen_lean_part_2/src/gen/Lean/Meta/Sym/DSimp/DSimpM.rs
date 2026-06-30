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
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedConfig: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedResult: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instInhabitedMethods: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default()
-> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = leanh::lean_unsigned_to_nat(100000);
    return v___x_566_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig() -> *mut leanh::LeanObject {
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = leanh::lean_unsigned_to_nat(100000);
    return v___x_567_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorIdx(
    mut v_x_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_568_) == 0 {
        let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_569_ = leanh::lean_unsigned_to_nat(0);
        return v___x_569_;
    } else {
        let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_570_ = leanh::lean_unsigned_to_nat(1);
        return v___x_570_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorIdx___boxed(
    mut v_x_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l_Lean_Meta_Sym_DSimp_Result_ctorIdx(v_x_571_);
    leanh::lean_dec_ref(v_x_571_);
    return v_res_572_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(
    mut v_t_573_: *mut leanh::LeanObject,
    mut v_k_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_573_) == 0 {
        let mut v_done_575_: u8 = 0;
        let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_done_575_ = leanh::lean_ctor_get_uint8(v_t_573_, 0 as u32);
        leanh::lean_dec_ref_known(v_t_573_, 0);
        v___x_576_ = leanh::lean_box((v_done_575_) as usize);
        v___x_577_ = leanh::lean_apply_1(v_k_574_, v___x_576_);
        return v___x_577_;
    } else {
        let mut v_e_x27_578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_done_579_: u8 = 0;
        let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_x27_578_ = leanh::lean_ctor_get(v_t_573_, 0);
        leanh::lean_inc_ref(v_e_x27_578_);
        v_done_579_ = leanh::lean_ctor_get_uint8(
            v_t_573_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        );
        leanh::lean_dec_ref_known(v_t_573_, 1);
        v___x_580_ = leanh::lean_box((v_done_579_) as usize);
        v___x_581_ = leanh::lean_apply_2(v_k_574_, v_e_x27_578_, v___x_580_);
        return v___x_581_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim(
    mut v_motive_582_: *mut leanh::LeanObject,
    mut v_ctorIdx_583_: *mut leanh::LeanObject,
    mut v_t_584_: *mut leanh::LeanObject,
    mut v_h_585_: *mut leanh::LeanObject,
    mut v_k_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_584_, v_k_586_);
    return v___x_587_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_ctorElim___boxed(
    mut v_motive_588_: *mut leanh::LeanObject,
    mut v_ctorIdx_589_: *mut leanh::LeanObject,
    mut v_t_590_: *mut leanh::LeanObject,
    mut v_h_591_: *mut leanh::LeanObject,
    mut v_k_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_593_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim(
        v_motive_588_,
        v_ctorIdx_589_,
        v_t_590_,
        v_h_591_,
        v_k_592_,
    );
    leanh::lean_dec(v_ctorIdx_589_);
    return v_res_593_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_rfl_elim___redArg(
    mut v_t_594_: *mut leanh::LeanObject,
    mut v_rfl_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_594_, v_rfl_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_rfl_elim(
    mut v_motive_597_: *mut leanh::LeanObject,
    mut v_t_598_: *mut leanh::LeanObject,
    mut v_h_599_: *mut leanh::LeanObject,
    mut v_rfl_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_598_, v_rfl_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_step_elim___redArg(
    mut v_t_602_: *mut leanh::LeanObject,
    mut v_step_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_602_, v_step_603_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Result_step_elim(
    mut v_motive_605_: *mut leanh::LeanObject,
    mut v_t_606_: *mut leanh::LeanObject,
    mut v_h_607_: *mut leanh::LeanObject,
    mut v_step_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = l_Lean_Meta_Sym_DSimp_Result_ctorElim___redArg(v_t_606_, v_step_608_);
    return v___x_609_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed()
-> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = leanh::lean_box(0);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_615_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_616_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__0,
    );
    v___x_617_ = l_StateRefT_x27_instMonad___redArg(v___x_616_);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_623_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_623_, 0, v___x_622_);
    return v___f_623_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_625_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_625_, 0, v___x_624_);
    return v___f_625_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8()
-> *mut leanh::LeanObject {
    let mut v___f_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_626_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__7,
    );
    v___f_627_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__6,
    );
    v___x_628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_628_, 0, v___f_627_);
    leanh::lean_ctor_set(v___x_628_, 1, v___f_626_);
    return v___x_628_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8,
    );
    v___f_630_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_630_, 0, v___x_629_);
    return v___f_630_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__8,
    );
    v___f_632_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_632_, 0, v___x_631_);
    return v___f_632_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11()
-> *mut leanh::LeanObject {
    let mut v___f_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_633_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__10,
    );
    v___f_634_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__9,
    );
    v___x_635_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_635_, 0, v___f_634_);
    leanh::lean_ctor_set(v___x_635_, 1, v___f_633_);
    return v___x_635_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11,
    );
    v___f_637_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_637_, 0, v___x_636_);
    return v___f_637_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__11,
    );
    v___f_639_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_639_, 0, v___x_638_);
    return v___f_639_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14()
-> *mut leanh::LeanObject {
    let mut v___f_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__13,
    );
    v___f_641_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__12,
    );
    v___x_642_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_642_, 0, v___f_641_);
    leanh::lean_ctor_set(v___x_642_, 1, v___f_640_);
    return v___x_642_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14,
    );
    v___f_644_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_644_, 0, v___x_643_);
    return v___f_644_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__14,
    );
    v___f_646_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_646_, 0, v___x_645_);
    return v___f_646_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17()
-> *mut leanh::LeanObject {
    let mut v___f_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_647_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__16,
    );
    v___f_648_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__15,
    );
    v___x_649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_649_, 0, v___f_648_);
    leanh::lean_ctor_set(v___x_649_, 1, v___f_647_);
    return v___x_649_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17,
    );
    v___f_651_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_651_, 0, v___x_650_);
    return v___f_651_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__17,
    );
    v___f_653_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_653_, 0, v___x_652_);
    return v___f_653_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20()
-> *mut leanh::LeanObject {
    let mut v___f_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_654_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__19,
    );
    v___f_655_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__18,
    );
    v___x_656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_656_, 0, v___f_655_);
    leanh::lean_ctor_set(v___x_656_, 1, v___f_654_);
    return v___x_656_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_657_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20,
    );
    v___f_658_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_658_, 0, v___x_657_);
    return v___f_658_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__20,
    );
    v___f_660_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_660_, 0, v___x_659_);
    return v___f_660_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23()
-> *mut leanh::LeanObject {
    let mut v___f_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_661_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__22,
    );
    v___f_662_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__21,
    );
    v___x_663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_663_, 0, v___f_662_);
    leanh::lean_ctor_set(v___x_663_, 1, v___f_661_);
    return v___x_663_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23,
    );
    v___f_665_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_665_, 0, v___x_664_);
    return v___f_665_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__23,
    );
    v___f_667_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_667_, 0, v___x_666_);
    return v___f_667_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26()
-> *mut leanh::LeanObject {
    let mut v___f_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__25,
    );
    v___f_669_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__24,
    );
    v___x_670_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_670_, 0, v___f_669_);
    leanh::lean_ctor_set(v___x_670_, 1, v___f_668_);
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_676_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_677_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__29;
    v___x_678_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_677_, v___x_676_, v___x_675_,
    );
    return v___x_678_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___x_704_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_705_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_705_, 0, v___x_704_);
    leanh::lean_closure_set(v___f_705_, 1, v___x_703_);
    return v___f_705_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39()
-> *mut leanh::LeanObject {
    let mut v___f_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_706_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_707_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__38,
    );
    v___f_708_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_708_, 0, v___f_707_);
    leanh::lean_closure_set(v___f_708_, 1, v___f_706_);
    return v___f_708_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__30;
    v___f_710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__39,
    );
    v___f_711_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_711_, 0, v___f_710_);
    leanh::lean_closure_set(v___f_711_, 1, v___x_709_);
    return v___f_711_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41()
-> *mut leanh::LeanObject {
    let mut v___f_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_712_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_713_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__40,
    );
    v___f_714_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_714_, 0, v___f_713_);
    leanh::lean_closure_set(v___f_714_, 1, v___f_712_);
    return v___f_714_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42()
-> *mut leanh::LeanObject {
    let mut v___f_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_715_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__28;
    v___f_716_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41_once),
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__41,
    );
    v___f_717_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_717_, 0, v___f_716_);
    leanh::lean_closure_set(v___f_717_, 1, v___f_715_);
    return v___f_717_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__43;
    v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
    return v___x_720_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(
    mut v_00_u03b1_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v_toFunctor_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_749_: u8 = 0;
    let mut v___f_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut v_unused_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_unused_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__1,
                );
                v_toApplicative_723_ = leanh::lean_ctor_get(v___x_722_, 0);
                v_toFunctor_724_ = leanh::lean_ctor_get(v_toApplicative_723_, 0);
                v_toSeq_725_ = leanh::lean_ctor_get(v_toApplicative_723_, 2);
                v_toSeqLeft_726_ = leanh::lean_ctor_get(v_toApplicative_723_, 3);
                v_toSeqRight_727_ = leanh::lean_ctor_get(v_toApplicative_723_, 4);
                v___f_728_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__2;
                v___f_729_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_724_, 2);
                v___f_730_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_730_, 0, v_toFunctor_724_);
                v___f_731_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_731_, 0, v_toFunctor_724_);
                v___x_732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_732_, 0, v___f_730_);
                leanh::lean_ctor_set(v___x_732_, 1, v___f_731_);
                leanh::lean_inc(v_toSeqRight_727_);
                v___f_733_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_733_, 0, v_toSeqRight_727_);
                leanh::lean_inc(v_toSeqLeft_726_);
                v___f_734_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_734_, 0, v_toSeqLeft_726_);
                leanh::lean_inc(v_toSeq_725_);
                v___f_735_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_735_, 0, v_toSeq_725_);
                v___x_736_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_736_, 0, v___x_732_);
                leanh::lean_ctor_set(v___x_736_, 1, v___f_728_);
                leanh::lean_ctor_set(v___x_736_, 2, v___f_735_);
                leanh::lean_ctor_set(v___x_736_, 3, v___f_734_);
                leanh::lean_ctor_set(v___x_736_, 4, v___f_733_);
                v___x_737_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_737_, 0, v___x_736_);
                leanh::lean_ctor_set(v___x_737_, 1, v___f_729_);
                v___x_738_ = l_StateRefT_x27_instMonad___redArg(v___x_737_);
                v_toApplicative_739_ = leanh::lean_ctor_get(v___x_738_, 0);
                v_isSharedCheck_779_ = (!leanh::lean_is_exclusive(v___x_738_)) as u8;
                if v_isSharedCheck_779_ == 0 {
                    v_unused_780_ = leanh::lean_ctor_get(v___x_738_, 1);
                    leanh::lean_dec(v_unused_780_);
                    v___x_741_ = v___x_738_;
                    v_isShared_742_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_739_);
                    leanh::lean_dec(v___x_738_);
                    v___x_741_ = leanh::lean_box(0);
                    v_isShared_742_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_743_ = leanh::lean_ctor_get(v_toApplicative_739_, 0);
                v_toSeq_744_ = leanh::lean_ctor_get(v_toApplicative_739_, 2);
                v_toSeqLeft_745_ = leanh::lean_ctor_get(v_toApplicative_739_, 3);
                v_toSeqRight_746_ = leanh::lean_ctor_get(v_toApplicative_739_, 4);
                v_isSharedCheck_777_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_739_)) as u8;
                if v_isSharedCheck_777_ == 0 {
                    v_unused_778_ = leanh::lean_ctor_get(v_toApplicative_739_, 1);
                    leanh::lean_dec(v_unused_778_);
                    v___x_748_ = v_toApplicative_739_;
                    v_isShared_749_ = v_isSharedCheck_777_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_746_);
                    leanh::lean_inc(v_toSeqLeft_745_);
                    leanh::lean_inc(v_toSeq_744_);
                    leanh::lean_inc(v_toFunctor_743_);
                    leanh::lean_dec(v_toApplicative_739_);
                    v___x_748_ = leanh::lean_box(0);
                    v_isShared_749_ = v_isSharedCheck_777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_750_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__4;
                v___f_751_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__5;
                leanh::lean_inc_ref(v_toFunctor_743_);
                v___f_752_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_752_, 0, v_toFunctor_743_);
                v___f_753_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_753_, 0, v_toFunctor_743_);
                v___x_754_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_754_, 0, v___f_752_);
                leanh::lean_ctor_set(v___x_754_, 1, v___f_753_);
                v___f_755_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_755_, 0, v_toSeqRight_746_);
                v___f_756_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_756_, 0, v_toSeqLeft_745_);
                v___f_757_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_757_, 0, v_toSeq_744_);
                if v_isShared_749_ == 0 {
                    leanh::lean_ctor_set(v___x_748_, 4, v___f_755_);
                    leanh::lean_ctor_set(v___x_748_, 3, v___f_756_);
                    leanh::lean_ctor_set(v___x_748_, 2, v___f_757_);
                    leanh::lean_ctor_set(v___x_748_, 1, v___f_750_);
                    leanh::lean_ctor_set(v___x_748_, 0, v___x_754_);
                    v___x_759_ = v___x_748_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 1, v___f_750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 2, v___f_757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 3, v___f_756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 4, v___f_755_);
                    v___x_759_ = v_reuseFailAlloc_776_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_742_ == 0 {
                    leanh::lean_ctor_set(v___x_741_, 1, v___f_751_);
                    leanh::lean_ctor_set(v___x_741_, 0, v___x_759_);
                    v___x_761_ = v___x_741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_775_, 1, v___f_751_);
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
                v___x_767_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__26,
                );
                v___x_768_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__37,
                );
                v_toMonadRef_769_ = leanh::lean_ctor_get(v___x_768_, 0);
                v___f_770_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM___closed__42,
                );
                leanh::lean_inc_ref(v___x_766_);
                v___x_771_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_770_, v___x_766_,
                );
                leanh::lean_inc_ref(v_toMonadRef_769_);
                v___x_772_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_772_, 0, v___x_767_);
                leanh::lean_ctor_set(v___x_772_, 1, v_toMonadRef_769_);
                leanh::lean_ctor_set(v___x_772_, 2, v___x_771_);
                v___x_773_ = leanh::lean_obj_once(
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
    mut v_x_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
    mut v___y_788_: *mut leanh::LeanObject,
    mut v___y_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l_Lean_Meta_Sym_DSimp_instInhabitedResult_default___closed__0;
    v___x_793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_793_, 0, v___x_792_);
    return v___x_793_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0___boxed(
    mut v_x_794_: *mut leanh::LeanObject,
    mut v___y_795_: *mut leanh::LeanObject,
    mut v___y_796_: *mut leanh::LeanObject,
    mut v___y_797_: *mut leanh::LeanObject,
    mut v___y_798_: *mut leanh::LeanObject,
    mut v___y_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
    mut v___y_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lean_Meta_Sym_DSimp_instInhabitedMethods_default___lam__0(
        v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_,
        v___y_801_, v___y_802_, v___y_803_,
    );
    leanh::lean_dec(v___y_803_);
    leanh::lean_dec_ref(v___y_802_);
    leanh::lean_dec(v___y_801_);
    leanh::lean_dec_ref(v___y_800_);
    leanh::lean_dec(v___y_799_);
    leanh::lean_dec_ref(v___y_798_);
    leanh::lean_dec(v___y_797_);
    leanh::lean_dec(v___y_796_);
    leanh::lean_dec(v___y_795_);
    leanh::lean_dec_ref(v_x_794_);
    return v_res_805_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(
    mut v_m_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_m_811_);
    return v_m_811_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl___boxed(
    mut v_m_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Meta_Sym_DSimp_Methods_toMethodsRefImpl(v_m_812_);
    leanh::lean_dec_ref(v_m_812_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(
    mut v_m_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_m_814_);
    return v_m_814_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl___boxed(
    mut v_m_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Meta_Sym_DSimp_MethodsRef_toMethodsImpl(v_m_815_);
    leanh::lean_dec(v_m_815_);
    return v_res_816_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___redArg(
    mut v_a_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_817_);
    v___x_819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_819_, 0, v_a_817_);
    return v___x_819_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___redArg___boxed(
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Lean_Meta_Sym_DSimp_getMethods___redArg(v_a_820_);
    leanh::lean_dec(v_a_820_);
    return v_res_822_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods(
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
    mut v_a_827_: *mut leanh::LeanObject,
    mut v_a_828_: *mut leanh::LeanObject,
    mut v_a_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_823_);
    v___x_833_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_833_, 0, v_a_823_);
    return v___x_833_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getMethods___boxed(
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
    mut v_a_837_: *mut leanh::LeanObject,
    mut v_a_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_a_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Lean_Meta_Sym_DSimp_getMethods(
        v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_,
    );
    leanh::lean_dec(v_a_842_);
    leanh::lean_dec_ref(v_a_841_);
    leanh::lean_dec(v_a_840_);
    leanh::lean_dec_ref(v_a_839_);
    leanh::lean_dec(v_a_838_);
    leanh::lean_dec_ref(v_a_837_);
    leanh::lean_dec(v_a_836_);
    leanh::lean_dec(v_a_835_);
    leanh::lean_dec(v_a_834_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(
    mut v_x_845_: *mut leanh::LeanObject,
    mut v_methods_846_: *mut leanh::LeanObject,
    mut v_config_847_: *mut leanh::LeanObject,
    mut v_s_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cache_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_a_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_unused_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cache_856_ = leanh::lean_ctor_get(v_s_848_, 1);
                v_isSharedCheck_884_ = (!leanh::lean_is_exclusive(v_s_848_)) as u8;
                if v_isSharedCheck_884_ == 0 {
                    v_unused_885_ = leanh::lean_ctor_get(v_s_848_, 0);
                    leanh::lean_dec(v_unused_885_);
                    v___x_858_ = v_s_848_;
                    v_isShared_859_ = v_isSharedCheck_884_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_856_);
                    leanh::lean_dec(v_s_848_);
                    v___x_858_ = leanh::lean_box(0);
                    v_isShared_859_ = v_isSharedCheck_884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_860_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_859_ == 0 {
                    leanh::lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 1, v_cache_856_);
                    v___x_862_ = v_reuseFailAlloc_883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = lean_st_mk_ref(v___x_862_);
                leanh::lean_inc(v_a_854_);
                leanh::lean_inc_ref(v_a_853_);
                leanh::lean_inc(v_a_852_);
                leanh::lean_inc_ref(v_a_851_);
                leanh::lean_inc(v_a_850_);
                leanh::lean_inc_ref(v_a_849_);
                leanh::lean_inc(v___x_863_);
                v___x_864_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_874_ = (!leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_874_ == 0 {
                        v___x_867_ = v___x_864_;
                        v_isShared_868_ = v_isSharedCheck_874_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_865_);
                        leanh::lean_dec(v___x_864_);
                        v___x_867_ = leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_874_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_863_);
                    v_a_875_ = leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_882_ = (!leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_882_ == 0 {
                        v___x_877_ = v___x_864_;
                        v_isShared_878_ = v_isSharedCheck_882_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_875_);
                        leanh::lean_dec(v___x_864_);
                        v___x_877_ = leanh::lean_box(0);
                        v_isShared_878_ = v_isSharedCheck_882_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_869_ = lean_st_ref_get(v___x_863_);
                leanh::lean_dec(v___x_863_);
                v___x_870_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_870_, 0, v_a_865_);
                leanh::lean_ctor_set(v___x_870_, 1, v___x_869_);
                if v_isShared_868_ == 0 {
                    leanh::lean_ctor_set(v___x_867_, 0, v___x_870_);
                    v___x_872_ = v___x_867_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
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
                    v_reuseFailAlloc_881_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
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
    mut v_x_886_: *mut leanh::LeanObject,
    mut v_methods_887_: *mut leanh::LeanObject,
    mut v_config_888_: *mut leanh::LeanObject,
    mut v_s_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_a_892_: *mut leanh::LeanObject,
    mut v_a_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_897_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_895_);
    leanh::lean_dec_ref(v_a_894_);
    leanh::lean_dec(v_a_893_);
    leanh::lean_dec_ref(v_a_892_);
    leanh::lean_dec(v_a_891_);
    leanh::lean_dec_ref(v_a_890_);
    return v_res_897_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run(
    mut v_00_u03b1_898_: *mut leanh::LeanObject,
    mut v_x_899_: *mut leanh::LeanObject,
    mut v_methods_900_: *mut leanh::LeanObject,
    mut v_config_901_: *mut leanh::LeanObject,
    mut v_s_902_: *mut leanh::LeanObject,
    mut v_a_903_: *mut leanh::LeanObject,
    mut v_a_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_911_: *mut leanh::LeanObject,
    mut v_x_912_: *mut leanh::LeanObject,
    mut v_methods_913_: *mut leanh::LeanObject,
    mut v_config_914_: *mut leanh::LeanObject,
    mut v_s_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
    mut v_a_920_: *mut leanh::LeanObject,
    mut v_a_921_: *mut leanh::LeanObject,
    mut v_a_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_923_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_921_);
    leanh::lean_dec_ref(v_a_920_);
    leanh::lean_dec(v_a_919_);
    leanh::lean_dec_ref(v_a_918_);
    leanh::lean_dec(v_a_917_);
    leanh::lean_dec_ref(v_a_916_);
    return v_res_923_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_924_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0_once),
        _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__0,
    );
    v___x_926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_926_, 0, v___x_925_);
    return v___x_926_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__1,
    );
    v___x_928_ = leanh::lean_unsigned_to_nat(0);
    v___x_929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_929_, 0, v___x_928_);
    leanh::lean_ctor_set(v___x_929_, 1, v___x_927_);
    return v___x_929_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg(
    mut v_x_930_: *mut leanh::LeanObject,
    mut v_methods_931_: *mut leanh::LeanObject,
    mut v_config_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
    mut v_a_937_: *mut leanh::LeanObject,
    mut v_a_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_940_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Sym_DSimp_DSimpM_run_x27___redArg___closed__2,
                );
                v___x_941_ = lean_st_mk_ref(v___x_940_);
                leanh::lean_inc(v_a_938_);
                leanh::lean_inc_ref(v_a_937_);
                leanh::lean_inc(v_a_936_);
                leanh::lean_inc_ref(v_a_935_);
                leanh::lean_inc(v_a_934_);
                leanh::lean_inc_ref(v_a_933_);
                leanh::lean_inc(v___x_941_);
                v___x_942_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_942_) == 0 {
                    v_a_943_ = leanh::lean_ctor_get(v___x_942_, 0);
                    v_isSharedCheck_951_ = (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                    if v_isSharedCheck_951_ == 0 {
                        v___x_945_ = v___x_942_;
                        v_isShared_946_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_943_);
                        leanh::lean_dec(v___x_942_);
                        v___x_945_ = leanh::lean_box(0);
                        v_isShared_946_ = v_isSharedCheck_951_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_941_);
                    return v___x_942_;
                }
            }
            1 => {
                v___x_947_ = lean_st_ref_get(v___x_941_);
                leanh::lean_dec(v___x_941_);
                leanh::lean_dec(v___x_947_);
                if v_isShared_946_ == 0 {
                    v___x_949_ = v___x_945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_943_);
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
    mut v_x_952_: *mut leanh::LeanObject,
    mut v_methods_953_: *mut leanh::LeanObject,
    mut v_config_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
    mut v_a_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
    mut v_a_959_: *mut leanh::LeanObject,
    mut v_a_960_: *mut leanh::LeanObject,
    mut v_a_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_962_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_960_);
    leanh::lean_dec_ref(v_a_959_);
    leanh::lean_dec(v_a_958_);
    leanh::lean_dec_ref(v_a_957_);
    leanh::lean_dec(v_a_956_);
    leanh::lean_dec_ref(v_a_955_);
    return v_res_962_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimpM_run_x27(
    mut v_00_u03b1_963_: *mut leanh::LeanObject,
    mut v_x_964_: *mut leanh::LeanObject,
    mut v_methods_965_: *mut leanh::LeanObject,
    mut v_config_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
    mut v_a_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
    mut v_a_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_975_: *mut leanh::LeanObject,
    mut v_x_976_: *mut leanh::LeanObject,
    mut v_methods_977_: *mut leanh::LeanObject,
    mut v_config_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
    mut v_a_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
    mut v_a_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_986_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_984_);
    leanh::lean_dec_ref(v_a_983_);
    leanh::lean_dec(v_a_982_);
    leanh::lean_dec_ref(v_a_981_);
    leanh::lean_dec(v_a_980_);
    leanh::lean_dec_ref(v_a_979_);
    return v_res_986_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimp___boxed(
    mut v_a_00___x40___internal___hyg_998_: *mut leanh::LeanObject,
    mut v_a_999_: *mut leanh::LeanObject,
    mut v_a_1000_: *mut leanh::LeanObject,
    mut v_a_1001_: *mut leanh::LeanObject,
    mut v_a_1002_: *mut leanh::LeanObject,
    mut v_a_1003_: *mut leanh::LeanObject,
    mut v_a_1004_: *mut leanh::LeanObject,
    mut v_a_1005_: *mut leanh::LeanObject,
    mut v_a_1006_: *mut leanh::LeanObject,
    mut v_a_1007_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1010_);
    v___x_1012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1012_, 0, v_a_1010_);
    return v___x_1012_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig___redArg___boxed(
    mut v_a_1013_: *mut leanh::LeanObject,
    mut v_a_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Lean_Meta_Sym_DSimp_getConfig___redArg(v_a_1013_);
    leanh::lean_dec(v_a_1013_);
    return v_res_1015_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig(
    mut v_a_1016_: *mut leanh::LeanObject,
    mut v_a_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
    mut v_a_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1017_);
    v___x_1026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1026_, 0, v_a_1017_);
    return v___x_1026_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_getConfig___boxed(
    mut v_a_1027_: *mut leanh::LeanObject,
    mut v_a_1028_: *mut leanh::LeanObject,
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_a_1031_: *mut leanh::LeanObject,
    mut v_a_1032_: *mut leanh::LeanObject,
    mut v_a_1033_: *mut leanh::LeanObject,
    mut v_a_1034_: *mut leanh::LeanObject,
    mut v_a_1035_: *mut leanh::LeanObject,
    mut v_a_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1037_ = l_Lean_Meta_Sym_DSimp_getConfig(
        v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_,
        v_a_1035_,
    );
    leanh::lean_dec(v_a_1035_);
    leanh::lean_dec_ref(v_a_1034_);
    leanh::lean_dec(v_a_1033_);
    leanh::lean_dec_ref(v_a_1032_);
    leanh::lean_dec(v_a_1031_);
    leanh::lean_dec_ref(v_a_1030_);
    leanh::lean_dec(v_a_1029_);
    leanh::lean_dec(v_a_1028_);
    leanh::lean_dec(v_a_1027_);
    return v_res_1037_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_pre(
    mut v_e_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
    mut v_a_1043_: *mut leanh::LeanObject,
    mut v_a_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pre_1049_ = leanh::lean_ctor_get(v_a_1039_, 0);
    leanh::lean_inc_ref(v_pre_1049_);
    leanh::lean_inc(v_a_1047_);
    leanh::lean_inc_ref(v_a_1046_);
    leanh::lean_inc(v_a_1045_);
    leanh::lean_inc_ref(v_a_1044_);
    leanh::lean_inc(v_a_1043_);
    leanh::lean_inc_ref(v_a_1042_);
    leanh::lean_inc(v_a_1041_);
    leanh::lean_inc(v_a_1040_);
    leanh::lean_inc(v_a_1039_);
    v___x_1050_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_1050_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_pre___boxed(
    mut v_e_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
    mut v_a_1053_: *mut leanh::LeanObject,
    mut v_a_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_a_1056_: *mut leanh::LeanObject,
    mut v_a_1057_: *mut leanh::LeanObject,
    mut v_a_1058_: *mut leanh::LeanObject,
    mut v_a_1059_: *mut leanh::LeanObject,
    mut v_a_1060_: *mut leanh::LeanObject,
    mut v_a_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_Meta_Sym_DSimp_pre(
        v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_,
        v_a_1059_, v_a_1060_,
    );
    leanh::lean_dec(v_a_1060_);
    leanh::lean_dec_ref(v_a_1059_);
    leanh::lean_dec(v_a_1058_);
    leanh::lean_dec_ref(v_a_1057_);
    leanh::lean_dec(v_a_1056_);
    leanh::lean_dec_ref(v_a_1055_);
    leanh::lean_dec(v_a_1054_);
    leanh::lean_dec(v_a_1053_);
    leanh::lean_dec(v_a_1052_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_post(
    mut v_e_1063_: *mut leanh::LeanObject,
    mut v_a_1064_: *mut leanh::LeanObject,
    mut v_a_1065_: *mut leanh::LeanObject,
    mut v_a_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_post_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_post_1074_ = leanh::lean_ctor_get(v_a_1064_, 1);
    leanh::lean_inc_ref(v_post_1074_);
    leanh::lean_inc(v_a_1072_);
    leanh::lean_inc_ref(v_a_1071_);
    leanh::lean_inc(v_a_1070_);
    leanh::lean_inc_ref(v_a_1069_);
    leanh::lean_inc(v_a_1068_);
    leanh::lean_inc_ref(v_a_1067_);
    leanh::lean_inc(v_a_1066_);
    leanh::lean_inc(v_a_1065_);
    leanh::lean_inc(v_a_1064_);
    v___x_1075_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_1075_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_post___boxed(
    mut v_e_1076_: *mut leanh::LeanObject,
    mut v_a_1077_: *mut leanh::LeanObject,
    mut v_a_1078_: *mut leanh::LeanObject,
    mut v_a_1079_: *mut leanh::LeanObject,
    mut v_a_1080_: *mut leanh::LeanObject,
    mut v_a_1081_: *mut leanh::LeanObject,
    mut v_a_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_a_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_Lean_Meta_Sym_DSimp_post(
        v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_,
        v_a_1084_, v_a_1085_,
    );
    leanh::lean_dec(v_a_1085_);
    leanh::lean_dec_ref(v_a_1084_);
    leanh::lean_dec(v_a_1083_);
    leanh::lean_dec_ref(v_a_1082_);
    leanh::lean_dec(v_a_1081_);
    leanh::lean_dec_ref(v_a_1080_);
    leanh::lean_dec(v_a_1079_);
    leanh::lean_dec(v_a_1078_);
    leanh::lean_dec(v_a_1077_);
    return v_res_1087_;
}
pub unsafe fn l_Lean_Meta_Sym_dsimp(
    mut v_e_1088_: *mut leanh::LeanObject,
    mut v_methods_1089_: *mut leanh::LeanObject,
    mut v_config_1090_: *mut leanh::LeanObject,
    mut v_a_1091_: *mut leanh::LeanObject,
    mut v_a_1092_: *mut leanh::LeanObject,
    mut v_a_1093_: *mut leanh::LeanObject,
    mut v_a_1094_: *mut leanh::LeanObject,
    mut v_a_1095_: *mut leanh::LeanObject,
    mut v_a_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1103_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_a_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1088_);
                v___x_1098_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_DSimp_dsimp___boxed as *mut core::ffi::c_void,
                    11,
                    1,
                );
                leanh::lean_closure_set(v___x_1098_, 0, v_e_1088_);
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
                if leanh::lean_obj_tag(v___x_1099_) == 0 {
                    v_a_1100_ = leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1111_ = (!leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1102_ = v___x_1099_;
                        v_isShared_1103_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1100_);
                        leanh::lean_dec(v___x_1099_);
                        v___x_1102_ = leanh::lean_box(0);
                        v_isShared_1103_ = v_isSharedCheck_1111_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1088_);
                    v_a_1112_ = leanh::lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1119_ = (!leanh::lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1114_ = v___x_1099_;
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1112_);
                        leanh::lean_dec(v___x_1099_);
                        v___x_1114_ = leanh::lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1100_) == 0 {
                    leanh::lean_dec_ref_known(v_a_1100_, 0);
                    if v_isShared_1103_ == 0 {
                        leanh::lean_ctor_set(v___x_1102_, 0, v_e_1088_);
                        v___x_1105_ = v___x_1102_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_e_1088_);
                        v___x_1105_ = v_reuseFailAlloc_1106_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1088_);
                    v_e_x27_1107_ = leanh::lean_ctor_get(v_a_1100_, 0);
                    leanh::lean_inc_ref(v_e_x27_1107_);
                    leanh::lean_dec_ref_known(v_a_1100_, 1);
                    if v_isShared_1103_ == 0 {
                        leanh::lean_ctor_set(v___x_1102_, 0, v_e_x27_1107_);
                        v___x_1109_ = v___x_1102_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_e_x27_1107_);
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
                    v_reuseFailAlloc_1118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
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
    mut v_e_1120_: *mut leanh::LeanObject,
    mut v_methods_1121_: *mut leanh::LeanObject,
    mut v_config_1122_: *mut leanh::LeanObject,
    mut v_a_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_a_1126_: *mut leanh::LeanObject,
    mut v_a_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1128_);
    leanh::lean_dec_ref(v_a_1127_);
    leanh::lean_dec(v_a_1126_);
    leanh::lean_dec_ref(v_a_1125_);
    leanh::lean_dec(v_a_1124_);
    leanh::lean_dec_ref(v_a_1123_);
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default =
        _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig_default);
    l_Lean_Meta_Sym_DSimp_instInhabitedConfig = _init_l_Lean_Meta_Sym_DSimp_instInhabitedConfig();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_DSimp_instInhabitedConfig);
    l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed =
        _init_l___private_Lean_Meta_Sym_DSimp_DSimpM_0__Lean_Meta_Sym_DSimp_MethodsRefPointed();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
}