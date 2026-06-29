// Lean compiler output
// Module: Lean.Meta.Sym.Simp.SimpM
// Imports: Lean.Meta.Sym.Pattern
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_sym_simp,
};
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
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern, runtime_initialize_Lean_Meta_Sym_Pattern,
};
pub static l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value:
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
        (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedResult_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorIdx(
    mut v_x_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_903_) == 0 {
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_904_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_904_;
    } else {
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_905_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_905_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorIdx___boxed(
    mut v_x_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Meta_Sym_Simp_Result_ctorIdx(v_x_906_);
    crate::leanh::lean_dec_ref(v_x_906_);
    return v_res_907_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(
    mut v_t_908_: *mut crate::leanh::LeanObject,
    mut v_k_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_908_) == 0 {
        let mut v_done_910_: u8 = 0;
        let mut v_contextDependent_911_: u8 = 0;
        let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_done_910_ = crate::leanh::lean_ctor_get_uint8(v_t_908_, 0 as u32);
        v_contextDependent_911_ = crate::leanh::lean_ctor_get_uint8(v_t_908_, 1 as u32);
        crate::leanh::lean_dec_ref_known(v_t_908_, 0);
        v___x_912_ = crate::leanh::lean_box((v_done_910_) as usize);
        v___x_913_ = crate::leanh::lean_box((v_contextDependent_911_) as usize);
        v___x_914_ = crate::leanh::lean_apply_2(v_k_909_, v___x_912_, v___x_913_);
        return v___x_914_;
    } else {
        let mut v_e_x27_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_done_917_: u8 = 0;
        let mut v_contextDependent_918_: u8 = 0;
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_x27_915_ = crate::leanh::lean_ctor_get(v_t_908_, 0);
        crate::leanh::lean_inc_ref(v_e_x27_915_);
        v_proof_916_ = crate::leanh::lean_ctor_get(v_t_908_, 1);
        crate::leanh::lean_inc_ref(v_proof_916_);
        v_done_917_ = crate::leanh::lean_ctor_get_uint8(
            v_t_908_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        v_contextDependent_918_ = crate::leanh::lean_ctor_get_uint8(
            v_t_908_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_t_908_, 2);
        v___x_919_ = crate::leanh::lean_box((v_done_917_) as usize);
        v___x_920_ = crate::leanh::lean_box((v_contextDependent_918_) as usize);
        v___x_921_ = crate::leanh::lean_apply_4(
            v_k_909_,
            v_e_x27_915_,
            v_proof_916_,
            v___x_919_,
            v___x_920_,
        );
        return v___x_921_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorElim(
    mut v_motive_922_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_923_: *mut crate::leanh::LeanObject,
    mut v_t_924_: *mut crate::leanh::LeanObject,
    mut v_h_925_: *mut crate::leanh::LeanObject,
    mut v_k_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_924_, v_k_926_);
    return v___x_927_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(
    mut v_motive_928_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_929_: *mut crate::leanh::LeanObject,
    mut v_t_930_: *mut crate::leanh::LeanObject,
    mut v_h_931_: *mut crate::leanh::LeanObject,
    mut v_k_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l_Lean_Meta_Sym_Simp_Result_ctorElim(
        v_motive_928_,
        v_ctorIdx_929_,
        v_t_930_,
        v_h_931_,
        v_k_932_,
    );
    crate::leanh::lean_dec(v_ctorIdx_929_);
    return v_res_933_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(
    mut v_t_934_: *mut crate::leanh::LeanObject,
    mut v_rfl_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_934_, v_rfl_935_);
    return v___x_936_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_rfl_elim(
    mut v_motive_937_: *mut crate::leanh::LeanObject,
    mut v_t_938_: *mut crate::leanh::LeanObject,
    mut v_h_939_: *mut crate::leanh::LeanObject,
    mut v_rfl_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_938_, v_rfl_940_);
    return v___x_941_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(
    mut v_t_942_: *mut crate::leanh::LeanObject,
    mut v_step_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_942_, v_step_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_step_elim(
    mut v_motive_945_: *mut crate::leanh::LeanObject,
    mut v_t_946_: *mut crate::leanh::LeanObject,
    mut v_h_947_: *mut crate::leanh::LeanObject,
    mut v_step_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_946_, v_step_948_);
    return v___x_949_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResult(
    mut v_done_954_: u8,
    mut v_contextDependent_955_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_done_954_ == 0 {
        if v_contextDependent_955_ == 0 {
            let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_956_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
            crate::leanh::lean_ctor_set_uint8(v___x_956_, 0 as u32, v_contextDependent_955_);
            crate::leanh::lean_ctor_set_uint8(v___x_956_, 1 as u32, v_contextDependent_955_);
            return v___x_956_;
        } else {
            let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_957_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
            crate::leanh::lean_ctor_set_uint8(v___x_957_, 0 as u32, v_done_954_);
            crate::leanh::lean_ctor_set_uint8(v___x_957_, 1 as u32, v_contextDependent_955_);
            return v___x_957_;
        }
    } else {
        if v_contextDependent_955_ == 0 {
            let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_958_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
            crate::leanh::lean_ctor_set_uint8(v___x_958_, 0 as u32, v_done_954_);
            crate::leanh::lean_ctor_set_uint8(v___x_958_, 1 as u32, v_contextDependent_955_);
            return v___x_958_;
        } else {
            let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_959_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
            crate::leanh::lean_ctor_set_uint8(v___x_959_, 0 as u32, v_contextDependent_955_);
            crate::leanh::lean_ctor_set_uint8(v___x_959_, 1 as u32, v_contextDependent_955_);
            return v___x_959_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResult___boxed(
    mut v_done_960_: *mut crate::leanh::LeanObject,
    mut v_contextDependent_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_done_boxed_962_: u8 = 0;
    let mut v_contextDependent_boxed_963_: u8 = 0;
    let mut v_res_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_done_boxed_962_ = (crate::leanh::lean_unbox(v_done_960_) as u8);
    v_contextDependent_boxed_963_ = (crate::leanh::lean_unbox(v_contextDependent_961_) as u8);
    v_res_964_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_boxed_962_, v_contextDependent_boxed_963_);
    return v_res_964_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResultCD(
    mut v_contextDependent_965_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_contextDependent_965_ == 0 {
        let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_966_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_966_, 0 as u32, v_contextDependent_965_);
        crate::leanh::lean_ctor_set_uint8(v___x_966_, 1 as u32, v_contextDependent_965_);
        return v___x_966_;
    } else {
        let mut v___x_967_: u8 = 0;
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_967_ = 0;
        v___x_968_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_968_, 0 as u32, v___x_967_);
        crate::leanh::lean_ctor_set_uint8(v___x_968_, 1 as u32, v_contextDependent_965_);
        return v___x_968_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(
    mut v_contextDependent_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_contextDependent_boxed_970_: u8 = 0;
    let mut v_res_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_contextDependent_boxed_970_ = (crate::leanh::lean_unbox(v_contextDependent_969_) as u8);
    v_res_971_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_boxed_970_);
    return v_res_971_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isContextDependent(
    mut v_x_972_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_972_) == 0 {
        let mut v_contextDependent_973_: u8 = 0;
        v_contextDependent_973_ = crate::leanh::lean_ctor_get_uint8(v_x_972_, 1 as u32);
        return v_contextDependent_973_;
    } else {
        let mut v_contextDependent_974_: u8 = 0;
        v_contextDependent_974_ = crate::leanh::lean_ctor_get_uint8(
            v_x_972_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        );
        return v_contextDependent_974_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(
    mut v_x_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_976_: u8 = 0;
    let mut v_r_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_975_);
    crate::leanh::lean_dec_ref(v_x_975_);
    v_r_977_ = crate::leanh::lean_box((v_res_976_) as usize);
    return v_r_977_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_withContextDependent(
    mut v_x_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_done_979_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v_e_x27_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_990_: u8 = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_993_: u8 = 0;
    let mut v___x_994_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_978_) == 0 {
                    v_done_979_ = crate::leanh::lean_ctor_get_uint8(v_x_978_, 0 as u32);
                    v_isSharedCheck_987_ = (!crate::leanh::lean_is_exclusive(v_x_978_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v___x_981_ = v_x_978_;
                        v_isShared_982_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_978_);
                        v___x_981_ = crate::leanh::lean_box(0);
                        v_isShared_982_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_x27_988_ = crate::leanh::lean_ctor_get(v_x_978_, 0);
                    v_proof_989_ = crate::leanh::lean_ctor_get(v_x_978_, 1);
                    v_done_990_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_978_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_998_ = (!crate::leanh::lean_is_exclusive(v_x_978_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_992_ = v_x_978_;
                        v_isShared_993_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_proof_989_);
                        crate::leanh::lean_inc(v_e_x27_988_);
                        crate::leanh::lean_dec(v_x_978_);
                        v___x_992_ = crate::leanh::lean_box(0);
                        v_isShared_993_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_983_ = 1;
                if v_isShared_982_ == 0 {
                    v___x_985_ = v___x_981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_986_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_986_, 0 as u32, v_done_979_);
                    v___x_985_ = v_reuseFailAlloc_986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v___x_985_, 1 as u32, v___x_983_);
                return v___x_985_;
            }
            3 => {
                v___x_994_ = 1;
                if v_isShared_993_ == 0 {
                    v___x_996_ = v___x_992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_e_x27_988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v_proof_989_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_997_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_done_990_,
                    );
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_996_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_994_,
                );
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed()
-> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = crate::leanh::lean_box(0);
    return v___x_999_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1000_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0,
    );
    v___x_1002_ = l_StateRefT_x27_instMonad___redArg(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_1008_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1008_, 0, v___x_1007_);
    return v___f_1008_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_1010_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1010_, 0, v___x_1009_);
    return v___f_1010_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7,
    );
    v___f_1012_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6,
    );
    v___x_1013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___f_1012_);
    crate::leanh::lean_ctor_set(v___x_1013_, 1, v___f_1011_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8,
    );
    v___f_1015_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1015_, 0, v___x_1014_);
    return v___f_1015_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8,
    );
    v___f_1017_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1017_, 0, v___x_1016_);
    return v___f_1017_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1018_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10,
    );
    v___f_1019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9,
    );
    v___x_1020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1020_, 0, v___f_1019_);
    crate::leanh::lean_ctor_set(v___x_1020_, 1, v___f_1018_);
    return v___x_1020_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11,
    );
    v___f_1022_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1022_, 0, v___x_1021_);
    return v___f_1022_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11,
    );
    v___f_1024_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1024_, 0, v___x_1023_);
    return v___f_1024_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1025_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13,
    );
    v___f_1026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12,
    );
    v___x_1027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___f_1026_);
    crate::leanh::lean_ctor_set(v___x_1027_, 1, v___f_1025_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14,
    );
    v___f_1029_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1029_, 0, v___x_1028_);
    return v___f_1029_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14,
    );
    v___f_1031_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1031_, 0, v___x_1030_);
    return v___f_1031_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1032_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16,
    );
    v___f_1033_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15,
    );
    v___x_1034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1034_, 0, v___f_1033_);
    crate::leanh::lean_ctor_set(v___x_1034_, 1, v___f_1032_);
    return v___x_1034_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17,
    );
    v___f_1036_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1036_, 0, v___x_1035_);
    return v___f_1036_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17,
    );
    v___f_1038_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1038_, 0, v___x_1037_);
    return v___f_1038_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1039_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19,
    );
    v___f_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18,
    );
    v___x_1041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1041_, 0, v___f_1040_);
    crate::leanh::lean_ctor_set(v___x_1041_, 1, v___f_1039_);
    return v___x_1041_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20,
    );
    v___f_1043_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1043_, 0, v___x_1042_);
    return v___f_1043_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20,
    );
    v___f_1045_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1045_, 0, v___x_1044_);
    return v___f_1045_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1046_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22,
    );
    v___f_1047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21,
    );
    v___x_1048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___f_1047_);
    crate::leanh::lean_ctor_set(v___x_1048_, 1, v___f_1046_);
    return v___x_1048_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23,
    );
    v___f_1050_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1050_, 0, v___x_1049_);
    return v___f_1050_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23,
    );
    v___f_1052_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1052_, 0, v___x_1051_);
    return v___f_1052_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1053_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25,
    );
    v___f_1054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24,
    );
    v___x_1055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1055_, 0, v___f_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 1, v___f_1053_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_1061_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___x_1062_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29;
    v___x_1063_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_1062_,
        v___x_1061_,
        v___x_1060_,
    );
    return v___x_1063_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31,
    );
    v___f_1065_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1066_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27;
    v___x_1067_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_1066_,
        v___f_1065_,
        v___x_1064_,
    );
    return v___x_1067_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32,
    );
    v___x_1069_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___x_1070_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29;
    v___x_1071_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_1070_,
        v___x_1069_,
        v___x_1068_,
    );
    return v___x_1071_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33,
    );
    v___f_1073_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1074_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27;
    v___x_1075_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_1074_,
        v___f_1073_,
        v___x_1072_,
    );
    return v___x_1075_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34,
    );
    v___x_1077_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___x_1078_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29;
    v___x_1079_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_1078_,
        v___x_1077_,
        v___x_1076_,
    );
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35,
    );
    v___f_1081_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1082_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27;
    v___x_1083_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_1082_,
        v___f_1081_,
        v___x_1080_,
    );
    return v___x_1083_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36,
    );
    v___f_1085_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1086_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27;
    v___x_1087_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_1086_,
        v___f_1085_,
        v___x_1084_,
    );
    return v___x_1087_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___x_1089_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_1090_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1090_, 0, v___x_1089_);
    crate::leanh::lean_closure_set(v___f_1090_, 1, v___x_1088_);
    return v___f_1090_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1091_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1092_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38,
    );
    v___f_1093_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1093_, 0, v___f_1092_);
    crate::leanh::lean_closure_set(v___f_1093_, 1, v___f_1091_);
    return v___f_1093_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___f_1095_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39,
    );
    v___f_1096_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1096_, 0, v___f_1095_);
    crate::leanh::lean_closure_set(v___f_1096_, 1, v___x_1094_);
    return v___f_1096_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1097_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40,
    );
    v___f_1099_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1099_, 0, v___f_1098_);
    crate::leanh::lean_closure_set(v___f_1099_, 1, v___f_1097_);
    return v___f_1099_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1100_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1101_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41,
    );
    v___f_1102_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1102_, 0, v___f_1101_);
    crate::leanh::lean_closure_set(v___f_1102_, 1, v___f_1100_);
    return v___f_1102_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43;
    v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instInhabitedSimpM(
    mut v_00_u03b1_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1127_: u8 = 0;
    let mut v_toFunctor_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___f_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1162_: u8 = 0;
    let mut v_unused_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v_unused_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1107_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1,
                );
                v_toApplicative_1108_ = crate::leanh::lean_ctor_get(v___x_1107_, 0);
                v_toFunctor_1109_ = crate::leanh::lean_ctor_get(v_toApplicative_1108_, 0);
                v_toSeq_1110_ = crate::leanh::lean_ctor_get(v_toApplicative_1108_, 2);
                v_toSeqLeft_1111_ = crate::leanh::lean_ctor_get(v_toApplicative_1108_, 3);
                v_toSeqRight_1112_ = crate::leanh::lean_ctor_get(v_toApplicative_1108_, 4);
                v___f_1113_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2;
                v___f_1114_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_1109_, 2);
                v___f_1115_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1115_, 0, v_toFunctor_1109_);
                v___f_1116_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1116_, 0, v_toFunctor_1109_);
                v___x_1117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1117_, 0, v___f_1115_);
                crate::leanh::lean_ctor_set(v___x_1117_, 1, v___f_1116_);
                crate::leanh::lean_inc(v_toSeqRight_1112_);
                v___f_1118_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1118_, 0, v_toSeqRight_1112_);
                crate::leanh::lean_inc(v_toSeqLeft_1111_);
                v___f_1119_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1119_, 0, v_toSeqLeft_1111_);
                crate::leanh::lean_inc(v_toSeq_1110_);
                v___f_1120_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1120_, 0, v_toSeq_1110_);
                v___x_1121_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1121_, 0, v___x_1117_);
                crate::leanh::lean_ctor_set(v___x_1121_, 1, v___f_1113_);
                crate::leanh::lean_ctor_set(v___x_1121_, 2, v___f_1120_);
                crate::leanh::lean_ctor_set(v___x_1121_, 3, v___f_1119_);
                crate::leanh::lean_ctor_set(v___x_1121_, 4, v___f_1118_);
                v___x_1122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                crate::leanh::lean_ctor_set(v___x_1122_, 1, v___f_1114_);
                v___x_1123_ = l_StateRefT_x27_instMonad___redArg(v___x_1122_);
                v_toApplicative_1124_ = crate::leanh::lean_ctor_get(v___x_1123_, 0);
                v_isSharedCheck_1164_ = (!crate::leanh::lean_is_exclusive(v___x_1123_)) as u8;
                if v_isSharedCheck_1164_ == 0 {
                    v_unused_1165_ = crate::leanh::lean_ctor_get(v___x_1123_, 1);
                    crate::leanh::lean_dec(v_unused_1165_);
                    v___x_1126_ = v___x_1123_;
                    v_isShared_1127_ = v_isSharedCheck_1164_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1124_);
                    crate::leanh::lean_dec(v___x_1123_);
                    v___x_1126_ = crate::leanh::lean_box(0);
                    v_isShared_1127_ = v_isSharedCheck_1164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1128_ = crate::leanh::lean_ctor_get(v_toApplicative_1124_, 0);
                v_toSeq_1129_ = crate::leanh::lean_ctor_get(v_toApplicative_1124_, 2);
                v_toSeqLeft_1130_ = crate::leanh::lean_ctor_get(v_toApplicative_1124_, 3);
                v_toSeqRight_1131_ = crate::leanh::lean_ctor_get(v_toApplicative_1124_, 4);
                v_isSharedCheck_1162_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1124_)) as u8;
                if v_isSharedCheck_1162_ == 0 {
                    v_unused_1163_ = crate::leanh::lean_ctor_get(v_toApplicative_1124_, 1);
                    crate::leanh::lean_dec(v_unused_1163_);
                    v___x_1133_ = v_toApplicative_1124_;
                    v_isShared_1134_ = v_isSharedCheck_1162_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1131_);
                    crate::leanh::lean_inc(v_toSeqLeft_1130_);
                    crate::leanh::lean_inc(v_toSeq_1129_);
                    crate::leanh::lean_inc(v_toFunctor_1128_);
                    crate::leanh::lean_dec(v_toApplicative_1124_);
                    v___x_1133_ = crate::leanh::lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1135_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4;
                v___f_1136_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_1128_);
                v___f_1137_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1137_, 0, v_toFunctor_1128_);
                v___f_1138_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1138_, 0, v_toFunctor_1128_);
                v___x_1139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1139_, 0, v___f_1137_);
                crate::leanh::lean_ctor_set(v___x_1139_, 1, v___f_1138_);
                v___f_1140_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1140_, 0, v_toSeqRight_1131_);
                v___f_1141_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1141_, 0, v_toSeqLeft_1130_);
                v___f_1142_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1142_, 0, v_toSeq_1129_);
                if v_isShared_1134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1133_, 4, v___f_1140_);
                    crate::leanh::lean_ctor_set(v___x_1133_, 3, v___f_1141_);
                    crate::leanh::lean_ctor_set(v___x_1133_, 2, v___f_1142_);
                    crate::leanh::lean_ctor_set(v___x_1133_, 1, v___f_1135_);
                    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1139_);
                    v___x_1144_ = v___x_1133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1161_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___f_1135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 2, v___f_1142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 3, v___f_1141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 4, v___f_1140_);
                    v___x_1144_ = v_reuseFailAlloc_1161_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1126_, 1, v___f_1136_);
                    crate::leanh::lean_ctor_set(v___x_1126_, 0, v___x_1144_);
                    v___x_1146_ = v___x_1126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___f_1136_);
                    v___x_1146_ = v_reuseFailAlloc_1160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1147_ = l_StateRefT_x27_instMonad___redArg(v___x_1146_);
                v___x_1148_ = l_ReaderT_instMonad___redArg(v___x_1147_);
                v___x_1149_ = l_StateRefT_x27_instMonad___redArg(v___x_1148_);
                v___x_1150_ = l_ReaderT_instMonad___redArg(v___x_1149_);
                v___x_1151_ = l_ReaderT_instMonad___redArg(v___x_1150_);
                v___x_1152_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26,
                );
                v___x_1153_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37,
                );
                v_toMonadRef_1154_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                v___f_1155_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42,
                );
                crate::leanh::lean_inc_ref(v___x_1151_);
                v___x_1156_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_1155_,
                    v___x_1151_,
                );
                crate::leanh::lean_inc_ref(v_toMonadRef_1154_);
                v___x_1157_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1157_, 0, v___x_1152_);
                crate::leanh::lean_ctor_set(v___x_1157_, 1, v_toMonadRef_1154_);
                crate::leanh::lean_ctor_set(v___x_1157_, 2, v___x_1156_);
                v___x_1158_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44,
                );
                v___x_1159_ = l_Lean_throwError___redArg(v___x_1151_, v___x_1157_, v___x_1158_);
                return v___x_1159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0;
    v___x_1178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(
    mut v_x_1179_: *mut crate::leanh::LeanObject,
    mut v___y_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ = l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0(
        v_x_1179_,
        v___y_1180_,
        v___y_1181_,
        v___y_1182_,
        v___y_1183_,
        v___y_1184_,
        v___y_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
    );
    crate::leanh::lean_dec(v___y_1188_);
    crate::leanh::lean_dec_ref(v___y_1187_);
    crate::leanh::lean_dec(v___y_1186_);
    crate::leanh::lean_dec_ref(v___y_1185_);
    crate::leanh::lean_dec(v___y_1184_);
    crate::leanh::lean_dec_ref(v___y_1183_);
    crate::leanh::lean_dec(v___y_1182_);
    crate::leanh::lean_dec_ref(v___y_1181_);
    crate::leanh::lean_dec(v___y_1180_);
    crate::leanh::lean_dec_ref(v_x_1179_);
    return v_res_1190_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(
    mut v_m_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_m_1196_);
    return v_m_1196_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(
    mut v_m_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_1197_);
    crate::leanh::lean_dec_ref(v_m_1197_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(
    mut v_m_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_m_1199_);
    return v_m_1199_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(
    mut v_m_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_1200_);
    crate::leanh::lean_dec(v_m_1200_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___redArg(
    mut v_a_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1202_);
    v___x_1204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1204_, 0, v_a_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(
    mut v_a_1205_: *mut crate::leanh::LeanObject,
    mut v_a_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_1205_);
    crate::leanh::lean_dec(v_a_1205_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods(
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
    mut v_a_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
    mut v_a_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
    mut v_a_1215_: *mut crate::leanh::LeanObject,
    mut v_a_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1208_);
    v___x_1218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1218_, 0, v_a_1208_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___boxed(
    mut v_a_1219_: *mut crate::leanh::LeanObject,
    mut v_a_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
    mut v_a_1223_: *mut crate::leanh::LeanObject,
    mut v_a_1224_: *mut crate::leanh::LeanObject,
    mut v_a_1225_: *mut crate::leanh::LeanObject,
    mut v_a_1226_: *mut crate::leanh::LeanObject,
    mut v_a_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lean_Meta_Sym_Simp_getMethods(
        v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_,
        v_a_1227_,
    );
    crate::leanh::lean_dec(v_a_1227_);
    crate::leanh::lean_dec_ref(v_a_1226_);
    crate::leanh::lean_dec(v_a_1225_);
    crate::leanh::lean_dec_ref(v_a_1224_);
    crate::leanh::lean_dec(v_a_1223_);
    crate::leanh::lean_dec_ref(v_a_1222_);
    crate::leanh::lean_dec(v_a_1221_);
    crate::leanh::lean_dec_ref(v_a_1220_);
    crate::leanh::lean_dec(v_a_1219_);
    return v_res_1229_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1230_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0,
    );
    v___x_1232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1232_, 0, v___x_1231_);
    return v___x_1232_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
    mut v_x_1233_: *mut crate::leanh::LeanObject,
    mut v_methods_1234_: *mut crate::leanh::LeanObject,
    mut v_config_1235_: *mut crate::leanh::LeanObject,
    mut v_s_1236_: *mut crate::leanh::LeanObject,
    mut v_a_1237_: *mut crate::leanh::LeanObject,
    mut v_a_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
    mut v_a_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1268_: u8 = 0;
    let mut v_a_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v_reuseFailAlloc_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_unused_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1244_ = crate::leanh::lean_ctor_get(v_a_1239_, 2);
                v_decls_1245_ = crate::leanh::lean_ctor_get(v_lctx_1244_, 1);
                v_size_1246_ = crate::leanh::lean_ctor_get(v_decls_1245_, 2);
                v_persistentCache_1247_ = crate::leanh::lean_ctor_get(v_s_1236_, 1);
                v_funext_1248_ = crate::leanh::lean_ctor_get(v_s_1236_, 3);
                v_isSharedCheck_1278_ = (!crate::leanh::lean_is_exclusive(v_s_1236_)) as u8;
                if v_isSharedCheck_1278_ == 0 {
                    v_unused_1279_ = crate::leanh::lean_ctor_get(v_s_1236_, 2);
                    crate::leanh::lean_dec(v_unused_1279_);
                    v_unused_1280_ = crate::leanh::lean_ctor_get(v_s_1236_, 0);
                    crate::leanh::lean_dec(v_unused_1280_);
                    v___x_1250_ = v_s_1236_;
                    v_isShared_1251_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_funext_1248_);
                    crate::leanh::lean_inc(v_persistentCache_1247_);
                    crate::leanh::lean_dec(v_s_1236_);
                    v___x_1250_ = crate::leanh::lean_box(0);
                    v_isShared_1251_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1252_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v_size_1246_);
                v___x_1253_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1253_, 0, v_config_1235_);
                crate::leanh::lean_ctor_set(v___x_1253_, 1, v_size_1246_);
                crate::leanh::lean_ctor_set(v___x_1253_, 2, v___x_1252_);
                v___x_1254_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1,
                );
                if v_isShared_1251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1250_, 2, v___x_1254_);
                    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1252_);
                    v___x_1256_ = v___x_1250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_persistentCache_1247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 2, v___x_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_funext_1248_);
                    v___x_1256_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1257_ = lean_st_mk_ref(v___x_1256_);
                crate::leanh::lean_inc(v_a_1242_);
                crate::leanh::lean_inc_ref(v_a_1241_);
                crate::leanh::lean_inc(v_a_1240_);
                crate::leanh::lean_inc_ref(v_a_1239_);
                crate::leanh::lean_inc(v_a_1238_);
                crate::leanh::lean_inc_ref(v_a_1237_);
                crate::leanh::lean_inc(v___x_1257_);
                v___x_1258_ = crate::leanh::lean_apply_10(
                    v_x_1233_,
                    v_methods_1234_,
                    v___x_1253_,
                    v___x_1257_,
                    v_a_1237_,
                    v_a_1238_,
                    v_a_1239_,
                    v_a_1240_,
                    v_a_1241_,
                    v_a_1242_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1258_) == 0 {
                    v_a_1259_ = crate::leanh::lean_ctor_get(v___x_1258_, 0);
                    v_isSharedCheck_1268_ = (!crate::leanh::lean_is_exclusive(v___x_1258_)) as u8;
                    if v_isSharedCheck_1268_ == 0 {
                        v___x_1261_ = v___x_1258_;
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1259_);
                        crate::leanh::lean_dec(v___x_1258_);
                        v___x_1261_ = crate::leanh::lean_box(0);
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1257_);
                    v_a_1269_ = crate::leanh::lean_ctor_get(v___x_1258_, 0);
                    v_isSharedCheck_1276_ = (!crate::leanh::lean_is_exclusive(v___x_1258_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1271_ = v___x_1258_;
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1269_);
                        crate::leanh::lean_dec(v___x_1258_);
                        v___x_1271_ = crate::leanh::lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1263_ = lean_st_ref_get(v___x_1257_);
                crate::leanh::lean_dec(v___x_1257_);
                v___x_1264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1264_, 0, v_a_1259_);
                crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
                if v_isShared_1262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1261_, 0, v___x_1264_);
                    v___x_1266_ = v___x_1261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
                    v___x_1266_ = v_reuseFailAlloc_1267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1266_;
            }
            5 => {
                if v_isShared_1272_ == 0 {
                    v___x_1274_ = v___x_1271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
                    v___x_1274_ = v_reuseFailAlloc_1275_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run___redArg___boxed(
    mut v_x_1281_: *mut crate::leanh::LeanObject,
    mut v_methods_1282_: *mut crate::leanh::LeanObject,
    mut v_config_1283_: *mut crate::leanh::LeanObject,
    mut v_s_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
        v_x_1281_,
        v_methods_1282_,
        v_config_1283_,
        v_s_1284_,
        v_a_1285_,
        v_a_1286_,
        v_a_1287_,
        v_a_1288_,
        v_a_1289_,
        v_a_1290_,
    );
    crate::leanh::lean_dec(v_a_1290_);
    crate::leanh::lean_dec_ref(v_a_1289_);
    crate::leanh::lean_dec(v_a_1288_);
    crate::leanh::lean_dec_ref(v_a_1287_);
    crate::leanh::lean_dec(v_a_1286_);
    crate::leanh::lean_dec_ref(v_a_1285_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run(
    mut v_00_u03b1_1293_: *mut crate::leanh::LeanObject,
    mut v_x_1294_: *mut crate::leanh::LeanObject,
    mut v_methods_1295_: *mut crate::leanh::LeanObject,
    mut v_config_1296_: *mut crate::leanh::LeanObject,
    mut v_s_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
        v_x_1294_,
        v_methods_1295_,
        v_config_1296_,
        v_s_1297_,
        v_a_1298_,
        v_a_1299_,
        v_a_1300_,
        v_a_1301_,
        v_a_1302_,
        v_a_1303_,
    );
    return v___x_1305_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run___boxed(
    mut v_00_u03b1_1306_: *mut crate::leanh::LeanObject,
    mut v_x_1307_: *mut crate::leanh::LeanObject,
    mut v_methods_1308_: *mut crate::leanh::LeanObject,
    mut v_config_1309_: *mut crate::leanh::LeanObject,
    mut v_s_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
    mut v_a_1314_: *mut crate::leanh::LeanObject,
    mut v_a_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1318_ = l_Lean_Meta_Sym_Simp_SimpM_run(
        v_00_u03b1_1306_,
        v_x_1307_,
        v_methods_1308_,
        v_config_1309_,
        v_s_1310_,
        v_a_1311_,
        v_a_1312_,
        v_a_1313_,
        v_a_1314_,
        v_a_1315_,
        v_a_1316_,
    );
    crate::leanh::lean_dec(v_a_1316_);
    crate::leanh::lean_dec_ref(v_a_1315_);
    crate::leanh::lean_dec(v_a_1314_);
    crate::leanh::lean_dec_ref(v_a_1313_);
    crate::leanh::lean_dec(v_a_1312_);
    crate::leanh::lean_dec_ref(v_a_1311_);
    return v_res_1318_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1,
    );
    v___x_1320_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1321_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    crate::leanh::lean_ctor_set(v___x_1321_, 1, v___x_1319_);
    crate::leanh::lean_ctor_set(v___x_1321_, 2, v___x_1319_);
    crate::leanh::lean_ctor_set(v___x_1321_, 3, v___x_1319_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
    mut v_x_1322_: *mut crate::leanh::LeanObject,
    mut v_methods_1323_: *mut crate::leanh::LeanObject,
    mut v_config_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_a_1328_: *mut crate::leanh::LeanObject,
    mut v_a_1329_: *mut crate::leanh::LeanObject,
    mut v_a_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1332_ = crate::leanh::lean_ctor_get(v_a_1327_, 2);
                v_decls_1333_ = crate::leanh::lean_ctor_get(v_lctx_1332_, 1);
                v_size_1334_ = crate::leanh::lean_ctor_get(v_decls_1333_, 2);
                v___x_1335_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v_size_1334_);
                v___x_1336_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1336_, 0, v_config_1324_);
                crate::leanh::lean_ctor_set(v___x_1336_, 1, v_size_1334_);
                crate::leanh::lean_ctor_set(v___x_1336_, 2, v___x_1335_);
                v___x_1337_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0,
                );
                v___x_1338_ = lean_st_mk_ref(v___x_1337_);
                crate::leanh::lean_inc(v_a_1330_);
                crate::leanh::lean_inc_ref(v_a_1329_);
                crate::leanh::lean_inc(v_a_1328_);
                crate::leanh::lean_inc_ref(v_a_1327_);
                crate::leanh::lean_inc(v_a_1326_);
                crate::leanh::lean_inc_ref(v_a_1325_);
                crate::leanh::lean_inc(v___x_1338_);
                v___x_1339_ = crate::leanh::lean_apply_10(
                    v_x_1322_,
                    v_methods_1323_,
                    v___x_1336_,
                    v___x_1338_,
                    v_a_1325_,
                    v_a_1326_,
                    v_a_1327_,
                    v_a_1328_,
                    v_a_1329_,
                    v_a_1330_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1339_) == 0 {
                    v_a_1340_ = crate::leanh::lean_ctor_get(v___x_1339_, 0);
                    v_isSharedCheck_1348_ = (!crate::leanh::lean_is_exclusive(v___x_1339_)) as u8;
                    if v_isSharedCheck_1348_ == 0 {
                        v___x_1342_ = v___x_1339_;
                        v_isShared_1343_ = v_isSharedCheck_1348_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1340_);
                        crate::leanh::lean_dec(v___x_1339_);
                        v___x_1342_ = crate::leanh::lean_box(0);
                        v_isShared_1343_ = v_isSharedCheck_1348_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1338_);
                    return v___x_1339_;
                }
            }
            1 => {
                v___x_1344_ = lean_st_ref_get(v___x_1338_);
                crate::leanh::lean_dec(v___x_1338_);
                crate::leanh::lean_dec(v___x_1344_);
                if v_isShared_1343_ == 0 {
                    v___x_1346_ = v___x_1342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1340_);
                    v___x_1346_ = v_reuseFailAlloc_1347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___boxed(
    mut v_x_1349_: *mut crate::leanh::LeanObject,
    mut v_methods_1350_: *mut crate::leanh::LeanObject,
    mut v_config_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
        v_x_1349_,
        v_methods_1350_,
        v_config_1351_,
        v_a_1352_,
        v_a_1353_,
        v_a_1354_,
        v_a_1355_,
        v_a_1356_,
        v_a_1357_,
    );
    crate::leanh::lean_dec(v_a_1357_);
    crate::leanh::lean_dec_ref(v_a_1356_);
    crate::leanh::lean_dec(v_a_1355_);
    crate::leanh::lean_dec_ref(v_a_1354_);
    crate::leanh::lean_dec(v_a_1353_);
    crate::leanh::lean_dec_ref(v_a_1352_);
    return v_res_1359_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27(
    mut v_00_u03b1_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
    mut v_methods_1362_: *mut crate::leanh::LeanObject,
    mut v_config_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_a_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
        v_x_1361_,
        v_methods_1362_,
        v_config_1363_,
        v_a_1364_,
        v_a_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
    );
    return v___x_1371_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27___boxed(
    mut v_00_u03b1_1372_: *mut crate::leanh::LeanObject,
    mut v_x_1373_: *mut crate::leanh::LeanObject,
    mut v_methods_1374_: *mut crate::leanh::LeanObject,
    mut v_config_1375_: *mut crate::leanh::LeanObject,
    mut v_a_1376_: *mut crate::leanh::LeanObject,
    mut v_a_1377_: *mut crate::leanh::LeanObject,
    mut v_a_1378_: *mut crate::leanh::LeanObject,
    mut v_a_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27(
        v_00_u03b1_1372_,
        v_x_1373_,
        v_methods_1374_,
        v_config_1375_,
        v_a_1376_,
        v_a_1377_,
        v_a_1378_,
        v_a_1379_,
        v_a_1380_,
        v_a_1381_,
    );
    crate::leanh::lean_dec(v_a_1381_);
    crate::leanh::lean_dec_ref(v_a_1380_);
    crate::leanh::lean_dec(v_a_1379_);
    crate::leanh::lean_dec_ref(v_a_1378_);
    crate::leanh::lean_dec(v_a_1377_);
    crate::leanh::lean_dec_ref(v_a_1376_);
    return v_res_1383_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simp___boxed(
    mut v_a_00___x40___internal___hyg_1395_: *mut crate::leanh::LeanObject,
    mut v_a_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = lean_sym_simp(
        v_a_00___x40___internal___hyg_1395_,
        v_a_1396_,
        v_a_1397_,
        v_a_1398_,
        v_a_1399_,
        v_a_1400_,
        v_a_1401_,
        v_a_1402_,
        v_a_1403_,
        v_a_1404_,
    );
    return v_res_1406_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig___redArg(
    mut v_a_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1409_ = crate::leanh::lean_ctor_get(v_a_1407_, 0);
    crate::leanh::lean_inc_ref(v_config_1409_);
    v___x_1410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1410_, 0, v_config_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(
    mut v_a_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1411_);
    crate::leanh::lean_dec_ref(v_a_1411_);
    return v_res_1413_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig(
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
    mut v_a_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1415_);
    return v___x_1424_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig___boxed(
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_a_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1435_ = l_Lean_Meta_Sym_Simp_getConfig(
        v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_,
        v_a_1433_,
    );
    crate::leanh::lean_dec(v_a_1433_);
    crate::leanh::lean_dec_ref(v_a_1432_);
    crate::leanh::lean_dec(v_a_1431_);
    crate::leanh::lean_dec_ref(v_a_1430_);
    crate::leanh::lean_dec(v_a_1429_);
    crate::leanh::lean_dec_ref(v_a_1428_);
    crate::leanh::lean_dec(v_a_1427_);
    crate::leanh::lean_dec_ref(v_a_1426_);
    crate::leanh::lean_dec(v_a_1425_);
    return v_res_1435_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_pre(
    mut v_e_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
    mut v_a_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pre_1447_ = crate::leanh::lean_ctor_get(v_a_1437_, 0);
    crate::leanh::lean_inc_ref(v_pre_1447_);
    crate::leanh::lean_inc(v_a_1445_);
    crate::leanh::lean_inc_ref(v_a_1444_);
    crate::leanh::lean_inc(v_a_1443_);
    crate::leanh::lean_inc_ref(v_a_1442_);
    crate::leanh::lean_inc(v_a_1441_);
    crate::leanh::lean_inc_ref(v_a_1440_);
    crate::leanh::lean_inc(v_a_1439_);
    crate::leanh::lean_inc_ref(v_a_1438_);
    crate::leanh::lean_inc(v_a_1437_);
    v___x_1448_ = crate::leanh::lean_apply_11(
        v_pre_1447_,
        v_e_1436_,
        v_a_1437_,
        v_a_1438_,
        v_a_1439_,
        v_a_1440_,
        v_a_1441_,
        v_a_1442_,
        v_a_1443_,
        v_a_1444_,
        v_a_1445_,
        crate::leanh::lean_box(0),
    );
    return v___x_1448_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_pre___boxed(
    mut v_e_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_a_1452_: *mut crate::leanh::LeanObject,
    mut v_a_1453_: *mut crate::leanh::LeanObject,
    mut v_a_1454_: *mut crate::leanh::LeanObject,
    mut v_a_1455_: *mut crate::leanh::LeanObject,
    mut v_a_1456_: *mut crate::leanh::LeanObject,
    mut v_a_1457_: *mut crate::leanh::LeanObject,
    mut v_a_1458_: *mut crate::leanh::LeanObject,
    mut v_a_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Lean_Meta_Sym_Simp_pre(
        v_e_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_,
        v_a_1457_, v_a_1458_,
    );
    crate::leanh::lean_dec(v_a_1458_);
    crate::leanh::lean_dec_ref(v_a_1457_);
    crate::leanh::lean_dec(v_a_1456_);
    crate::leanh::lean_dec_ref(v_a_1455_);
    crate::leanh::lean_dec(v_a_1454_);
    crate::leanh::lean_dec_ref(v_a_1453_);
    crate::leanh::lean_dec(v_a_1452_);
    crate::leanh::lean_dec_ref(v_a_1451_);
    crate::leanh::lean_dec(v_a_1450_);
    return v_res_1460_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_post(
    mut v_e_1461_: *mut crate::leanh::LeanObject,
    mut v_a_1462_: *mut crate::leanh::LeanObject,
    mut v_a_1463_: *mut crate::leanh::LeanObject,
    mut v_a_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_a_1466_: *mut crate::leanh::LeanObject,
    mut v_a_1467_: *mut crate::leanh::LeanObject,
    mut v_a_1468_: *mut crate::leanh::LeanObject,
    mut v_a_1469_: *mut crate::leanh::LeanObject,
    mut v_a_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_post_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_post_1472_ = crate::leanh::lean_ctor_get(v_a_1462_, 1);
    crate::leanh::lean_inc_ref(v_post_1472_);
    crate::leanh::lean_inc(v_a_1470_);
    crate::leanh::lean_inc_ref(v_a_1469_);
    crate::leanh::lean_inc(v_a_1468_);
    crate::leanh::lean_inc_ref(v_a_1467_);
    crate::leanh::lean_inc(v_a_1466_);
    crate::leanh::lean_inc_ref(v_a_1465_);
    crate::leanh::lean_inc(v_a_1464_);
    crate::leanh::lean_inc_ref(v_a_1463_);
    crate::leanh::lean_inc(v_a_1462_);
    v___x_1473_ = crate::leanh::lean_apply_11(
        v_post_1472_,
        v_e_1461_,
        v_a_1462_,
        v_a_1463_,
        v_a_1464_,
        v_a_1465_,
        v_a_1466_,
        v_a_1467_,
        v_a_1468_,
        v_a_1469_,
        v_a_1470_,
        crate::leanh::lean_box(0),
    );
    return v___x_1473_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_post___boxed(
    mut v_e_1474_: *mut crate::leanh::LeanObject,
    mut v_a_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_Meta_Sym_Simp_post(
        v_e_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_,
        v_a_1482_, v_a_1483_,
    );
    crate::leanh::lean_dec(v_a_1483_);
    crate::leanh::lean_dec_ref(v_a_1482_);
    crate::leanh::lean_dec(v_a_1481_);
    crate::leanh::lean_dec_ref(v_a_1480_);
    crate::leanh::lean_dec(v_a_1479_);
    crate::leanh::lean_dec_ref(v_a_1478_);
    crate::leanh::lean_dec(v_a_1477_);
    crate::leanh::lean_dec_ref(v_a_1476_);
    crate::leanh::lean_dec(v_a_1475_);
    return v_res_1485_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_persistentCache_1487_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1488_: *mut crate::leanh::LeanObject,
    mut v_funext_1489_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v_unused_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1492_ = lean_st_ref_take(v_a_1486_);
                v_numSteps_1493_ = crate::leanh::lean_ctor_get(v___x_1492_, 0);
                v_isSharedCheck_1503_ = (!crate::leanh::lean_is_exclusive(v___x_1492_)) as u8;
                if v_isSharedCheck_1503_ == 0 {
                    v_unused_1504_ = crate::leanh::lean_ctor_get(v___x_1492_, 3);
                    crate::leanh::lean_dec(v_unused_1504_);
                    v_unused_1505_ = crate::leanh::lean_ctor_get(v___x_1492_, 2);
                    crate::leanh::lean_dec(v_unused_1505_);
                    v_unused_1506_ = crate::leanh::lean_ctor_get(v___x_1492_, 1);
                    crate::leanh::lean_dec(v_unused_1506_);
                    v___x_1495_ = v___x_1492_;
                    v_isShared_1496_ = v_isSharedCheck_1503_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numSteps_1493_);
                    crate::leanh::lean_dec(v___x_1492_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v_isShared_1496_ = v_isSharedCheck_1503_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1495_, 3, v_funext_1489_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 2, v_transientCache_1488_);
                    crate::leanh::lean_ctor_set(v___x_1495_, 1, v_persistentCache_1487_);
                    v___x_1498_ = v___x_1495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_numSteps_1493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_persistentCache_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_transientCache_1488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_funext_1489_);
                    v___x_1498_ = v_reuseFailAlloc_1502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1499_ = lean_st_ref_set(v_a_1486_, v___x_1498_);
                v___x_1500_ = crate::leanh::lean_box(0);
                v___x_1501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
                return v___x_1501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_persistentCache_1508_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1509_: *mut crate::leanh::LeanObject,
    mut v_funext_1510_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1513_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
        v_a_1507_,
        v_persistentCache_1508_,
        v_transientCache_1509_,
        v_funext_1510_,
        v_a_x3f_1511_,
    );
    crate::leanh::lean_dec(v_a_x3f_1511_);
    crate::leanh::lean_dec(v_a_1507_);
    return v_res_1513_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(
    mut v_k_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_a_1517_: *mut crate::leanh::LeanObject,
    mut v_a_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
    mut v_a_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_unused_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v_a_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut v_unused_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1525_ = lean_st_ref_get(v_a_1517_);
                v___x_1526_ = lean_st_ref_get(v_a_1517_);
                v___x_1527_ = lean_st_ref_get(v_a_1517_);
                v_persistentCache_1528_ = crate::leanh::lean_ctor_get(v___x_1525_, 1);
                crate::leanh::lean_inc_ref(v_persistentCache_1528_);
                crate::leanh::lean_dec(v___x_1525_);
                v_transientCache_1529_ = crate::leanh::lean_ctor_get(v___x_1526_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_1529_);
                crate::leanh::lean_dec(v___x_1526_);
                v_funext_1530_ = crate::leanh::lean_ctor_get(v___x_1527_, 3);
                crate::leanh::lean_inc_ref(v_funext_1530_);
                crate::leanh::lean_dec(v___x_1527_);
                crate::leanh::lean_inc(v_a_1523_);
                crate::leanh::lean_inc_ref(v_a_1522_);
                crate::leanh::lean_inc(v_a_1521_);
                crate::leanh::lean_inc_ref(v_a_1520_);
                crate::leanh::lean_inc(v_a_1519_);
                crate::leanh::lean_inc_ref(v_a_1518_);
                crate::leanh::lean_inc(v_a_1517_);
                crate::leanh::lean_inc_ref(v_a_1516_);
                crate::leanh::lean_inc(v_a_1515_);
                v_r_1531_ = crate::leanh::lean_apply_10(
                    v_k_1514_,
                    v_a_1515_,
                    v_a_1516_,
                    v_a_1517_,
                    v_a_1518_,
                    v_a_1519_,
                    v_a_1520_,
                    v_a_1521_,
                    v_a_1522_,
                    v_a_1523_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1531_) == 0 {
                    v_a_1532_ = crate::leanh::lean_ctor_get(v_r_1531_, 0);
                    v_isSharedCheck_1548_ = (!crate::leanh::lean_is_exclusive(v_r_1531_)) as u8;
                    if v_isSharedCheck_1548_ == 0 {
                        v___x_1534_ = v_r_1531_;
                        v_isShared_1535_ = v_isSharedCheck_1548_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1532_);
                        crate::leanh::lean_dec(v_r_1531_);
                        v___x_1534_ = crate::leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1548_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1549_ = crate::leanh::lean_ctor_get(v_r_1531_, 0);
                    crate::leanh::lean_inc(v_a_1549_);
                    crate::leanh::lean_dec_ref_known(v_r_1531_, 1);
                    v___x_1550_ = crate::leanh::lean_box(0);
                    v___x_1551_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                        v_a_1517_,
                        v_persistentCache_1528_,
                        v_transientCache_1529_,
                        v_funext_1530_,
                        v___x_1550_,
                    );
                    v_isSharedCheck_1558_ = (!crate::leanh::lean_is_exclusive(v___x_1551_)) as u8;
                    if v_isSharedCheck_1558_ == 0 {
                        v_unused_1559_ = crate::leanh::lean_ctor_get(v___x_1551_, 0);
                        crate::leanh::lean_dec(v_unused_1559_);
                        v___x_1553_ = v___x_1551_;
                        v_isShared_1554_ = v_isSharedCheck_1558_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1551_);
                        v___x_1553_ = crate::leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1558_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1532_);
                if v_isShared_1535_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1534_, 1);
                    v___x_1537_ = v___x_1534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1532_);
                    v___x_1537_ = v_reuseFailAlloc_1547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1538_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                    v_a_1517_,
                    v_persistentCache_1528_,
                    v_transientCache_1529_,
                    v_funext_1530_,
                    v___x_1537_,
                );
                crate::leanh::lean_dec_ref(v___x_1537_);
                v_isSharedCheck_1545_ = (!crate::leanh::lean_is_exclusive(v___x_1538_)) as u8;
                if v_isSharedCheck_1545_ == 0 {
                    v_unused_1546_ = crate::leanh::lean_ctor_get(v___x_1538_, 0);
                    crate::leanh::lean_dec(v_unused_1546_);
                    v___x_1540_ = v___x_1538_;
                    v_isShared_1541_ = v_isSharedCheck_1545_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1538_);
                    v___x_1540_ = crate::leanh::lean_box(0);
                    v_isShared_1541_ = v_isSharedCheck_1545_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1540_, 0, v_a_1532_);
                    v___x_1543_ = v___x_1540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1532_);
                    v___x_1543_ = v_reuseFailAlloc_1544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1543_;
            }
            5 => {
                if v_isShared_1554_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1553_, 1);
                    crate::leanh::lean_ctor_set(v___x_1553_, 0, v_a_1549_);
                    v___x_1556_ = v___x_1553_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1549_);
                    v___x_1556_ = v_reuseFailAlloc_1557_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___boxed(
    mut v_k_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(
        v_k_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_,
        v_a_1568_, v_a_1569_,
    );
    crate::leanh::lean_dec(v_a_1569_);
    crate::leanh::lean_dec_ref(v_a_1568_);
    crate::leanh::lean_dec(v_a_1567_);
    crate::leanh::lean_dec_ref(v_a_1566_);
    crate::leanh::lean_dec(v_a_1565_);
    crate::leanh::lean_dec_ref(v_a_1564_);
    crate::leanh::lean_dec(v_a_1563_);
    crate::leanh::lean_dec_ref(v_a_1562_);
    crate::leanh::lean_dec(v_a_1561_);
    return v_res_1571_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache(
    mut v_00_u03b1_1572_: *mut crate::leanh::LeanObject,
    mut v_k_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_unused_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut v_unused_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1584_ = lean_st_ref_get(v_a_1576_);
                v___x_1585_ = lean_st_ref_get(v_a_1576_);
                v___x_1586_ = lean_st_ref_get(v_a_1576_);
                v_persistentCache_1587_ = crate::leanh::lean_ctor_get(v___x_1584_, 1);
                crate::leanh::lean_inc_ref(v_persistentCache_1587_);
                crate::leanh::lean_dec(v___x_1584_);
                v_transientCache_1588_ = crate::leanh::lean_ctor_get(v___x_1585_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_1588_);
                crate::leanh::lean_dec(v___x_1585_);
                v_funext_1589_ = crate::leanh::lean_ctor_get(v___x_1586_, 3);
                crate::leanh::lean_inc_ref(v_funext_1589_);
                crate::leanh::lean_dec(v___x_1586_);
                crate::leanh::lean_inc(v_a_1582_);
                crate::leanh::lean_inc_ref(v_a_1581_);
                crate::leanh::lean_inc(v_a_1580_);
                crate::leanh::lean_inc_ref(v_a_1579_);
                crate::leanh::lean_inc(v_a_1578_);
                crate::leanh::lean_inc_ref(v_a_1577_);
                crate::leanh::lean_inc(v_a_1576_);
                crate::leanh::lean_inc_ref(v_a_1575_);
                crate::leanh::lean_inc(v_a_1574_);
                v_r_1590_ = crate::leanh::lean_apply_10(
                    v_k_1573_,
                    v_a_1574_,
                    v_a_1575_,
                    v_a_1576_,
                    v_a_1577_,
                    v_a_1578_,
                    v_a_1579_,
                    v_a_1580_,
                    v_a_1581_,
                    v_a_1582_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1590_) == 0 {
                    v_a_1591_ = crate::leanh::lean_ctor_get(v_r_1590_, 0);
                    v_isSharedCheck_1607_ = (!crate::leanh::lean_is_exclusive(v_r_1590_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1593_ = v_r_1590_;
                        v_isShared_1594_ = v_isSharedCheck_1607_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1591_);
                        crate::leanh::lean_dec(v_r_1590_);
                        v___x_1593_ = crate::leanh::lean_box(0);
                        v_isShared_1594_ = v_isSharedCheck_1607_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1608_ = crate::leanh::lean_ctor_get(v_r_1590_, 0);
                    crate::leanh::lean_inc(v_a_1608_);
                    crate::leanh::lean_dec_ref_known(v_r_1590_, 1);
                    v___x_1609_ = crate::leanh::lean_box(0);
                    v___x_1610_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                        v_a_1576_,
                        v_persistentCache_1587_,
                        v_transientCache_1588_,
                        v_funext_1589_,
                        v___x_1609_,
                    );
                    v_isSharedCheck_1617_ = (!crate::leanh::lean_is_exclusive(v___x_1610_)) as u8;
                    if v_isSharedCheck_1617_ == 0 {
                        v_unused_1618_ = crate::leanh::lean_ctor_get(v___x_1610_, 0);
                        crate::leanh::lean_dec(v_unused_1618_);
                        v___x_1612_ = v___x_1610_;
                        v_isShared_1613_ = v_isSharedCheck_1617_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1610_);
                        v___x_1612_ = crate::leanh::lean_box(0);
                        v_isShared_1613_ = v_isSharedCheck_1617_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1591_);
                if v_isShared_1594_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1593_, 1);
                    v___x_1596_ = v___x_1593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1591_);
                    v___x_1596_ = v_reuseFailAlloc_1606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1597_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                    v_a_1576_,
                    v_persistentCache_1587_,
                    v_transientCache_1588_,
                    v_funext_1589_,
                    v___x_1596_,
                );
                crate::leanh::lean_dec_ref(v___x_1596_);
                v_isSharedCheck_1604_ = (!crate::leanh::lean_is_exclusive(v___x_1597_)) as u8;
                if v_isSharedCheck_1604_ == 0 {
                    v_unused_1605_ = crate::leanh::lean_ctor_get(v___x_1597_, 0);
                    crate::leanh::lean_dec(v_unused_1605_);
                    v___x_1599_ = v___x_1597_;
                    v_isShared_1600_ = v_isSharedCheck_1604_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1597_);
                    v___x_1599_ = crate::leanh::lean_box(0);
                    v_isShared_1600_ = v_isSharedCheck_1604_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1599_, 0, v_a_1591_);
                    v___x_1602_ = v___x_1599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1591_);
                    v___x_1602_ = v_reuseFailAlloc_1603_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1602_;
            }
            5 => {
                if v_isShared_1613_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1612_, 1);
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v_a_1608_);
                    v___x_1615_ = v___x_1612_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1608_);
                    v___x_1615_ = v_reuseFailAlloc_1616_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___boxed(
    mut v_00_u03b1_1619_: *mut crate::leanh::LeanObject,
    mut v_k_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache(
        v_00_u03b1_1619_,
        v_k_1620_,
        v_a_1621_,
        v_a_1622_,
        v_a_1623_,
        v_a_1624_,
        v_a_1625_,
        v_a_1626_,
        v_a_1627_,
        v_a_1628_,
        v_a_1629_,
    );
    crate::leanh::lean_dec(v_a_1629_);
    crate::leanh::lean_dec_ref(v_a_1628_);
    crate::leanh::lean_dec(v_a_1627_);
    crate::leanh::lean_dec_ref(v_a_1626_);
    crate::leanh::lean_dec(v_a_1625_);
    crate::leanh::lean_dec_ref(v_a_1624_);
    crate::leanh::lean_dec(v_a_1623_);
    crate::leanh::lean_dec_ref(v_a_1622_);
    crate::leanh::lean_dec(v_a_1621_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1633_: *mut crate::leanh::LeanObject,
    mut v_funext_1634_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_unused_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1637_ = lean_st_ref_take(v_a_1632_);
                v_numSteps_1638_ = crate::leanh::lean_ctor_get(v___x_1637_, 0);
                v_persistentCache_1639_ = crate::leanh::lean_ctor_get(v___x_1637_, 1);
                v_isSharedCheck_1649_ = (!crate::leanh::lean_is_exclusive(v___x_1637_)) as u8;
                if v_isSharedCheck_1649_ == 0 {
                    v_unused_1650_ = crate::leanh::lean_ctor_get(v___x_1637_, 3);
                    crate::leanh::lean_dec(v_unused_1650_);
                    v_unused_1651_ = crate::leanh::lean_ctor_get(v___x_1637_, 2);
                    crate::leanh::lean_dec(v_unused_1651_);
                    v___x_1641_ = v___x_1637_;
                    v_isShared_1642_ = v_isSharedCheck_1649_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_persistentCache_1639_);
                    crate::leanh::lean_inc(v_numSteps_1638_);
                    crate::leanh::lean_dec(v___x_1637_);
                    v___x_1641_ = crate::leanh::lean_box(0);
                    v_isShared_1642_ = v_isSharedCheck_1649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1641_, 3, v_funext_1634_);
                    crate::leanh::lean_ctor_set(v___x_1641_, 2, v_transientCache_1633_);
                    v___x_1644_ = v___x_1641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_numSteps_1638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_persistentCache_1639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_transientCache_1633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_funext_1634_);
                    v___x_1644_ = v_reuseFailAlloc_1648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1645_ = lean_st_ref_set(v_a_1632_, v___x_1644_);
                v___x_1646_ = crate::leanh::lean_box(0);
                v___x_1647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1647_, 0, v___x_1646_);
                return v___x_1647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1653_: *mut crate::leanh::LeanObject,
    mut v_funext_1654_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
        v_a_1652_,
        v_transientCache_1653_,
        v_funext_1654_,
        v_a_x3f_1655_,
    );
    crate::leanh::lean_dec(v_a_x3f_1655_);
    crate::leanh::lean_dec(v_a_1652_);
    return v_res_1657_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(
    mut v_k_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_unused_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_a_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut v_unused_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_st_ref_get(v_a_1661_);
                v___x_1670_ = lean_st_ref_get(v_a_1661_);
                v_transientCache_1671_ = crate::leanh::lean_ctor_get(v___x_1669_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_1671_);
                crate::leanh::lean_dec(v___x_1669_);
                v_funext_1672_ = crate::leanh::lean_ctor_get(v___x_1670_, 3);
                crate::leanh::lean_inc_ref(v_funext_1672_);
                crate::leanh::lean_dec(v___x_1670_);
                crate::leanh::lean_inc(v_a_1667_);
                crate::leanh::lean_inc_ref(v_a_1666_);
                crate::leanh::lean_inc(v_a_1665_);
                crate::leanh::lean_inc_ref(v_a_1664_);
                crate::leanh::lean_inc(v_a_1663_);
                crate::leanh::lean_inc_ref(v_a_1662_);
                crate::leanh::lean_inc(v_a_1661_);
                crate::leanh::lean_inc_ref(v_a_1660_);
                crate::leanh::lean_inc(v_a_1659_);
                v_r_1673_ = crate::leanh::lean_apply_10(
                    v_k_1658_,
                    v_a_1659_,
                    v_a_1660_,
                    v_a_1661_,
                    v_a_1662_,
                    v_a_1663_,
                    v_a_1664_,
                    v_a_1665_,
                    v_a_1666_,
                    v_a_1667_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1673_) == 0 {
                    v_a_1674_ = crate::leanh::lean_ctor_get(v_r_1673_, 0);
                    v_isSharedCheck_1690_ = (!crate::leanh::lean_is_exclusive(v_r_1673_)) as u8;
                    if v_isSharedCheck_1690_ == 0 {
                        v___x_1676_ = v_r_1673_;
                        v_isShared_1677_ = v_isSharedCheck_1690_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1674_);
                        crate::leanh::lean_dec(v_r_1673_);
                        v___x_1676_ = crate::leanh::lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1691_ = crate::leanh::lean_ctor_get(v_r_1673_, 0);
                    crate::leanh::lean_inc(v_a_1691_);
                    crate::leanh::lean_dec_ref_known(v_r_1673_, 1);
                    v___x_1692_ = crate::leanh::lean_box(0);
                    v___x_1693_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                        v_a_1661_,
                        v_transientCache_1671_,
                        v_funext_1672_,
                        v___x_1692_,
                    );
                    v_isSharedCheck_1700_ = (!crate::leanh::lean_is_exclusive(v___x_1693_)) as u8;
                    if v_isSharedCheck_1700_ == 0 {
                        v_unused_1701_ = crate::leanh::lean_ctor_get(v___x_1693_, 0);
                        crate::leanh::lean_dec(v_unused_1701_);
                        v___x_1695_ = v___x_1693_;
                        v_isShared_1696_ = v_isSharedCheck_1700_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1693_);
                        v___x_1695_ = crate::leanh::lean_box(0);
                        v_isShared_1696_ = v_isSharedCheck_1700_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1674_);
                if v_isShared_1677_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1676_, 1);
                    v___x_1679_ = v___x_1676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1674_);
                    v___x_1679_ = v_reuseFailAlloc_1689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1680_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                    v_a_1661_,
                    v_transientCache_1671_,
                    v_funext_1672_,
                    v___x_1679_,
                );
                crate::leanh::lean_dec_ref(v___x_1679_);
                v_isSharedCheck_1687_ = (!crate::leanh::lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1687_ == 0 {
                    v_unused_1688_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                    crate::leanh::lean_dec(v_unused_1688_);
                    v___x_1682_ = v___x_1680_;
                    v_isShared_1683_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1680_);
                    v___x_1682_ = crate::leanh::lean_box(0);
                    v_isShared_1683_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v_a_1674_);
                    v___x_1685_ = v___x_1682_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1674_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1685_;
            }
            5 => {
                if v_isShared_1696_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1695_, 1);
                    crate::leanh::lean_ctor_set(v___x_1695_, 0, v_a_1691_);
                    v___x_1698_ = v___x_1695_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1691_);
                    v___x_1698_ = v_reuseFailAlloc_1699_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___boxed(
    mut v_k_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(
        v_k_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
        v_a_1710_, v_a_1711_,
    );
    crate::leanh::lean_dec(v_a_1711_);
    crate::leanh::lean_dec_ref(v_a_1710_);
    crate::leanh::lean_dec(v_a_1709_);
    crate::leanh::lean_dec_ref(v_a_1708_);
    crate::leanh::lean_dec(v_a_1707_);
    crate::leanh::lean_dec_ref(v_a_1706_);
    crate::leanh::lean_dec(v_a_1705_);
    crate::leanh::lean_dec_ref(v_a_1704_);
    crate::leanh::lean_dec(v_a_1703_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache(
    mut v_00_u03b1_1714_: *mut crate::leanh::LeanObject,
    mut v_k_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
    mut v_a_1718_: *mut crate::leanh::LeanObject,
    mut v_a_1719_: *mut crate::leanh::LeanObject,
    mut v_a_1720_: *mut crate::leanh::LeanObject,
    mut v_a_1721_: *mut crate::leanh::LeanObject,
    mut v_a_1722_: *mut crate::leanh::LeanObject,
    mut v_a_1723_: *mut crate::leanh::LeanObject,
    mut v_a_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut v_unused_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_unused_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1726_ = lean_st_ref_get(v_a_1718_);
                v___x_1727_ = lean_st_ref_get(v_a_1718_);
                v_transientCache_1728_ = crate::leanh::lean_ctor_get(v___x_1726_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_1728_);
                crate::leanh::lean_dec(v___x_1726_);
                v_funext_1729_ = crate::leanh::lean_ctor_get(v___x_1727_, 3);
                crate::leanh::lean_inc_ref(v_funext_1729_);
                crate::leanh::lean_dec(v___x_1727_);
                crate::leanh::lean_inc(v_a_1724_);
                crate::leanh::lean_inc_ref(v_a_1723_);
                crate::leanh::lean_inc(v_a_1722_);
                crate::leanh::lean_inc_ref(v_a_1721_);
                crate::leanh::lean_inc(v_a_1720_);
                crate::leanh::lean_inc_ref(v_a_1719_);
                crate::leanh::lean_inc(v_a_1718_);
                crate::leanh::lean_inc_ref(v_a_1717_);
                crate::leanh::lean_inc(v_a_1716_);
                v_r_1730_ = crate::leanh::lean_apply_10(
                    v_k_1715_,
                    v_a_1716_,
                    v_a_1717_,
                    v_a_1718_,
                    v_a_1719_,
                    v_a_1720_,
                    v_a_1721_,
                    v_a_1722_,
                    v_a_1723_,
                    v_a_1724_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1730_) == 0 {
                    v_a_1731_ = crate::leanh::lean_ctor_get(v_r_1730_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v_r_1730_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1733_ = v_r_1730_;
                        v_isShared_1734_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1731_);
                        crate::leanh::lean_dec(v_r_1730_);
                        v___x_1733_ = crate::leanh::lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1748_ = crate::leanh::lean_ctor_get(v_r_1730_, 0);
                    crate::leanh::lean_inc(v_a_1748_);
                    crate::leanh::lean_dec_ref_known(v_r_1730_, 1);
                    v___x_1749_ = crate::leanh::lean_box(0);
                    v___x_1750_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                        v_a_1718_,
                        v_transientCache_1728_,
                        v_funext_1729_,
                        v___x_1749_,
                    );
                    v_isSharedCheck_1757_ = (!crate::leanh::lean_is_exclusive(v___x_1750_)) as u8;
                    if v_isSharedCheck_1757_ == 0 {
                        v_unused_1758_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                        crate::leanh::lean_dec(v_unused_1758_);
                        v___x_1752_ = v___x_1750_;
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1750_);
                        v___x_1752_ = crate::leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1731_);
                if v_isShared_1734_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1733_, 1);
                    v___x_1736_ = v___x_1733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1731_);
                    v___x_1736_ = v_reuseFailAlloc_1746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1737_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                    v_a_1718_,
                    v_transientCache_1728_,
                    v_funext_1729_,
                    v___x_1736_,
                );
                crate::leanh::lean_dec_ref(v___x_1736_);
                v_isSharedCheck_1744_ = (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                if v_isSharedCheck_1744_ == 0 {
                    v_unused_1745_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    crate::leanh::lean_dec(v_unused_1745_);
                    v___x_1739_ = v___x_1737_;
                    v_isShared_1740_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1737_);
                    v___x_1739_ = crate::leanh::lean_box(0);
                    v_isShared_1740_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v_a_1731_);
                    v___x_1742_ = v___x_1739_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1731_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1742_;
            }
            5 => {
                if v_isShared_1753_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1752_, 1);
                    crate::leanh::lean_ctor_set(v___x_1752_, 0, v_a_1748_);
                    v___x_1755_ = v___x_1752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1748_);
                    v___x_1755_ = v_reuseFailAlloc_1756_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___boxed(
    mut v_00_u03b1_1759_: *mut crate::leanh::LeanObject,
    mut v_k_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache(
        v_00_u03b1_1759_,
        v_k_1760_,
        v_a_1761_,
        v_a_1762_,
        v_a_1763_,
        v_a_1764_,
        v_a_1765_,
        v_a_1766_,
        v_a_1767_,
        v_a_1768_,
        v_a_1769_,
    );
    crate::leanh::lean_dec(v_a_1769_);
    crate::leanh::lean_dec_ref(v_a_1768_);
    crate::leanh::lean_dec(v_a_1767_);
    crate::leanh::lean_dec_ref(v_a_1766_);
    crate::leanh::lean_dec(v_a_1765_);
    crate::leanh::lean_dec_ref(v_a_1764_);
    crate::leanh::lean_dec(v_a_1763_);
    crate::leanh::lean_dec_ref(v_a_1762_);
    crate::leanh::lean_dec(v_a_1761_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Meta_Sym_simp(
    mut v_e_1772_: *mut crate::leanh::LeanObject,
    mut v_methods_1773_: *mut crate::leanh::LeanObject,
    mut v_config_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_simp___boxed as *mut core::ffi::c_void,
        11,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1782_, 0, v_e_1772_);
    v___x_1783_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
        v___x_1782_,
        v_methods_1773_,
        v_config_1774_,
        v_a_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
        v_a_1779_,
        v_a_1780_,
    );
    return v___x_1783_;
}
pub unsafe fn l_Lean_Meta_Sym_simp___boxed(
    mut v_e_1784_: *mut crate::leanh::LeanObject,
    mut v_methods_1785_: *mut crate::leanh::LeanObject,
    mut v_config_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_a_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Lean_Meta_Sym_simp(
        v_e_1784_,
        v_methods_1785_,
        v_config_1786_,
        v_a_1787_,
        v_a_1788_,
        v_a_1789_,
        v_a_1790_,
        v_a_1791_,
        v_a_1792_,
    );
    crate::leanh::lean_dec(v_a_1792_);
    crate::leanh::lean_dec_ref(v_a_1791_);
    crate::leanh::lean_dec(v_a_1790_);
    crate::leanh::lean_dec_ref(v_a_1789_);
    crate::leanh::lean_dec(v_a_1788_);
    crate::leanh::lean_dec_ref(v_a_1787_);
    return v_res_1794_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_SimpM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed =
        _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_SimpM(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_SimpM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
}
