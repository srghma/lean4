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
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedResult_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedResult: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value:
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
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instInhabitedMethods: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorIdx(
    mut v_x_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_903_) == 0 {
        let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_904_ = leanh::lean_unsigned_to_nat(0);
        return v___x_904_;
    } else {
        let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_905_ = leanh::lean_unsigned_to_nat(1);
        return v___x_905_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorIdx___boxed(
    mut v_x_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Meta_Sym_Simp_Result_ctorIdx(v_x_906_);
    leanh::lean_dec_ref(v_x_906_);
    return v_res_907_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(
    mut v_t_908_: *mut leanh::LeanObject,
    mut v_k_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_908_) == 0 {
        let mut v_done_910_: u8 = 0;
        let mut v_contextDependent_911_: u8 = 0;
        let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_done_910_ = leanh::lean_ctor_get_uint8(v_t_908_, 0 as u32);
        v_contextDependent_911_ = leanh::lean_ctor_get_uint8(v_t_908_, 1 as u32);
        leanh::lean_dec_ref_known(v_t_908_, 0);
        v___x_912_ = leanh::lean_box((v_done_910_) as usize);
        v___x_913_ = leanh::lean_box((v_contextDependent_911_) as usize);
        v___x_914_ = leanh::lean_apply_2(v_k_909_, v___x_912_, v___x_913_);
        return v___x_914_;
    } else {
        let mut v_e_x27_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_done_917_: u8 = 0;
        let mut v_contextDependent_918_: u8 = 0;
        let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_x27_915_ = leanh::lean_ctor_get(v_t_908_, 0);
        leanh::lean_inc_ref(v_e_x27_915_);
        v_proof_916_ = leanh::lean_ctor_get(v_t_908_, 1);
        leanh::lean_inc_ref(v_proof_916_);
        v_done_917_ = leanh::lean_ctor_get_uint8(
            v_t_908_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        v_contextDependent_918_ = leanh::lean_ctor_get_uint8(
            v_t_908_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
        );
        leanh::lean_dec_ref_known(v_t_908_, 2);
        v___x_919_ = leanh::lean_box((v_done_917_) as usize);
        v___x_920_ = leanh::lean_box((v_contextDependent_918_) as usize);
        v___x_921_ = leanh::lean_apply_4(
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
    mut v_motive_922_: *mut leanh::LeanObject,
    mut v_ctorIdx_923_: *mut leanh::LeanObject,
    mut v_t_924_: *mut leanh::LeanObject,
    mut v_h_925_: *mut leanh::LeanObject,
    mut v_k_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_924_, v_k_926_);
    return v___x_927_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_ctorElim___boxed(
    mut v_motive_928_: *mut leanh::LeanObject,
    mut v_ctorIdx_929_: *mut leanh::LeanObject,
    mut v_t_930_: *mut leanh::LeanObject,
    mut v_h_931_: *mut leanh::LeanObject,
    mut v_k_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l_Lean_Meta_Sym_Simp_Result_ctorElim(
        v_motive_928_,
        v_ctorIdx_929_,
        v_t_930_,
        v_h_931_,
        v_k_932_,
    );
    leanh::lean_dec(v_ctorIdx_929_);
    return v_res_933_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_rfl_elim___redArg(
    mut v_t_934_: *mut leanh::LeanObject,
    mut v_rfl_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_934_, v_rfl_935_);
    return v___x_936_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_rfl_elim(
    mut v_motive_937_: *mut leanh::LeanObject,
    mut v_t_938_: *mut leanh::LeanObject,
    mut v_h_939_: *mut leanh::LeanObject,
    mut v_rfl_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_938_, v_rfl_940_);
    return v___x_941_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_step_elim___redArg(
    mut v_t_942_: *mut leanh::LeanObject,
    mut v_step_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_942_, v_step_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_step_elim(
    mut v_motive_945_: *mut leanh::LeanObject,
    mut v_t_946_: *mut leanh::LeanObject,
    mut v_h_947_: *mut leanh::LeanObject,
    mut v_step_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = l_Lean_Meta_Sym_Simp_Result_ctorElim___redArg(v_t_946_, v_step_948_);
    return v___x_949_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResult(
    mut v_done_954_: u8,
    mut v_contextDependent_955_: u8,
) -> *mut leanh::LeanObject {
    if v_done_954_ == 0 {
        if v_contextDependent_955_ == 0 {
            let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_956_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
            leanh::lean_ctor_set_uint8(v___x_956_, 0 as u32, v_contextDependent_955_);
            leanh::lean_ctor_set_uint8(v___x_956_, 1 as u32, v_contextDependent_955_);
            return v___x_956_;
        } else {
            let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_957_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
            leanh::lean_ctor_set_uint8(v___x_957_, 0 as u32, v_done_954_);
            leanh::lean_ctor_set_uint8(v___x_957_, 1 as u32, v_contextDependent_955_);
            return v___x_957_;
        }
    } else {
        if v_contextDependent_955_ == 0 {
            let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_958_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
            leanh::lean_ctor_set_uint8(v___x_958_, 0 as u32, v_done_954_);
            leanh::lean_ctor_set_uint8(v___x_958_, 1 as u32, v_contextDependent_955_);
            return v___x_958_;
        } else {
            let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_959_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
            leanh::lean_ctor_set_uint8(v___x_959_, 0 as u32, v_contextDependent_955_);
            leanh::lean_ctor_set_uint8(v___x_959_, 1 as u32, v_contextDependent_955_);
            return v___x_959_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResult___boxed(
    mut v_done_960_: *mut leanh::LeanObject,
    mut v_contextDependent_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_done_boxed_962_: u8 = 0;
    let mut v_contextDependent_boxed_963_: u8 = 0;
    let mut v_res_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_done_boxed_962_ = (leanh::lean_unbox(v_done_960_) as u8);
    v_contextDependent_boxed_963_ = (leanh::lean_unbox(v_contextDependent_961_) as u8);
    v_res_964_ = l_Lean_Meta_Sym_Simp_mkRflResult(v_done_boxed_962_, v_contextDependent_boxed_963_);
    return v_res_964_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResultCD(
    mut v_contextDependent_965_: u8,
) -> *mut leanh::LeanObject {
    if v_contextDependent_965_ == 0 {
        let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_966_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_966_, 0 as u32, v_contextDependent_965_);
        leanh::lean_ctor_set_uint8(v___x_966_, 1 as u32, v_contextDependent_965_);
        return v___x_966_;
    } else {
        let mut v___x_967_: u8 = 0;
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_967_ = 0;
        v___x_968_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_968_, 0 as u32, v___x_967_);
        leanh::lean_ctor_set_uint8(v___x_968_, 1 as u32, v_contextDependent_965_);
        return v___x_968_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkRflResultCD___boxed(
    mut v_contextDependent_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_contextDependent_boxed_970_: u8 = 0;
    let mut v_res_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_contextDependent_boxed_970_ = (leanh::lean_unbox(v_contextDependent_969_) as u8);
    v_res_971_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_boxed_970_);
    return v_res_971_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isContextDependent(
    mut v_x_972_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_972_) == 0 {
        let mut v_contextDependent_973_: u8 = 0;
        v_contextDependent_973_ = leanh::lean_ctor_get_uint8(v_x_972_, 1 as u32);
        return v_contextDependent_973_;
    } else {
        let mut v_contextDependent_974_: u8 = 0;
        v_contextDependent_974_ = leanh::lean_ctor_get_uint8(
            v_x_972_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
        );
        return v_contextDependent_974_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isContextDependent___boxed(
    mut v_x_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_976_: u8 = 0;
    let mut v_r_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_Lean_Meta_Sym_Simp_Result_isContextDependent(v_x_975_);
    leanh::lean_dec_ref(v_x_975_);
    v_r_977_ = leanh::lean_box((v_res_976_) as usize);
    return v_r_977_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_withContextDependent(
    mut v_x_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_done_979_: u8 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v_e_x27_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_990_: u8 = 0;
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_993_: u8 = 0;
    let mut v___x_994_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_978_) == 0 {
                    v_done_979_ = leanh::lean_ctor_get_uint8(v_x_978_, 0 as u32);
                    v_isSharedCheck_987_ = (!leanh::lean_is_exclusive(v_x_978_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v___x_981_ = v_x_978_;
                        v_isShared_982_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_978_);
                        v___x_981_ = leanh::lean_box(0);
                        v_isShared_982_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_x27_988_ = leanh::lean_ctor_get(v_x_978_, 0);
                    v_proof_989_ = leanh::lean_ctor_get(v_x_978_, 1);
                    v_done_990_ = leanh::lean_ctor_get_uint8(
                        v_x_978_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_998_ = (!leanh::lean_is_exclusive(v_x_978_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_992_ = v_x_978_;
                        v_isShared_993_ = v_isSharedCheck_998_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_proof_989_);
                        leanh::lean_inc(v_e_x27_988_);
                        leanh::lean_dec(v_x_978_);
                        v___x_992_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_986_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    leanh::lean_ctor_set_uint8(v_reuseFailAlloc_986_, 0 as u32, v_done_979_);
                    v___x_985_ = v_reuseFailAlloc_986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v___x_985_, 1 as u32, v___x_983_);
                return v___x_985_;
            }
            3 => {
                v___x_994_ = 1;
                if v_isShared_993_ == 0 {
                    v___x_996_ = v___x_992_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_e_x27_988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v_proof_989_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_997_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_done_990_,
                    );
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_996_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_994_,
                );
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed()
-> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = leanh::lean_box(0);
    return v___x_999_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1000_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__0,
    );
    v___x_1002_ = l_StateRefT_x27_instMonad___redArg(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_1008_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1008_, 0, v___x_1007_);
    return v___f_1008_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_1010_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1010_, 0, v___x_1009_);
    return v___f_1010_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8()
-> *mut leanh::LeanObject {
    let mut v___f_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1011_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__7,
    );
    v___f_1012_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__6,
    );
    v___x_1013_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1013_, 0, v___f_1012_);
    leanh::lean_ctor_set(v___x_1013_, 1, v___f_1011_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8,
    );
    v___f_1015_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1015_, 0, v___x_1014_);
    return v___f_1015_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__8,
    );
    v___f_1017_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1017_, 0, v___x_1016_);
    return v___f_1017_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11()
-> *mut leanh::LeanObject {
    let mut v___f_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1018_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__10,
    );
    v___f_1019_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__9,
    );
    v___x_1020_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1020_, 0, v___f_1019_);
    leanh::lean_ctor_set(v___x_1020_, 1, v___f_1018_);
    return v___x_1020_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11,
    );
    v___f_1022_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1022_, 0, v___x_1021_);
    return v___f_1022_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__11,
    );
    v___f_1024_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1024_, 0, v___x_1023_);
    return v___f_1024_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14()
-> *mut leanh::LeanObject {
    let mut v___f_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1025_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__13,
    );
    v___f_1026_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__12,
    );
    v___x_1027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1027_, 0, v___f_1026_);
    leanh::lean_ctor_set(v___x_1027_, 1, v___f_1025_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14,
    );
    v___f_1029_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1029_, 0, v___x_1028_);
    return v___f_1029_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__14,
    );
    v___f_1031_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1031_, 0, v___x_1030_);
    return v___f_1031_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17()
-> *mut leanh::LeanObject {
    let mut v___f_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__16,
    );
    v___f_1033_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__15,
    );
    v___x_1034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1034_, 0, v___f_1033_);
    leanh::lean_ctor_set(v___x_1034_, 1, v___f_1032_);
    return v___x_1034_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17,
    );
    v___f_1036_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1036_, 0, v___x_1035_);
    return v___f_1036_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__17,
    );
    v___f_1038_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1038_, 0, v___x_1037_);
    return v___f_1038_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20()
-> *mut leanh::LeanObject {
    let mut v___f_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1039_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__19,
    );
    v___f_1040_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__18,
    );
    v___x_1041_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1041_, 0, v___f_1040_);
    leanh::lean_ctor_set(v___x_1041_, 1, v___f_1039_);
    return v___x_1041_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20,
    );
    v___f_1043_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1043_, 0, v___x_1042_);
    return v___f_1043_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__20,
    );
    v___f_1045_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1045_, 0, v___x_1044_);
    return v___f_1045_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23()
-> *mut leanh::LeanObject {
    let mut v___f_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1046_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__22,
    );
    v___f_1047_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__21,
    );
    v___x_1048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1048_, 0, v___f_1047_);
    leanh::lean_ctor_set(v___x_1048_, 1, v___f_1046_);
    return v___x_1048_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23,
    );
    v___f_1050_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1050_, 0, v___x_1049_);
    return v___f_1050_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__23,
    );
    v___f_1052_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1052_, 0, v___x_1051_);
    return v___f_1052_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26()
-> *mut leanh::LeanObject {
    let mut v___f_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1053_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__25,
    );
    v___f_1054_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__24,
    );
    v___x_1055_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1055_, 0, v___f_1054_);
    leanh::lean_ctor_set(v___x_1055_, 1, v___f_1053_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
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
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___x_1089_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_1090_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1090_, 0, v___x_1089_);
    leanh::lean_closure_set(v___f_1090_, 1, v___x_1088_);
    return v___f_1090_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39()
-> *mut leanh::LeanObject {
    let mut v___f_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1091_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1092_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__38,
    );
    v___f_1093_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1093_, 0, v___f_1092_);
    leanh::lean_closure_set(v___f_1093_, 1, v___f_1091_);
    return v___f_1093_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__30;
    v___f_1095_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__39,
    );
    v___f_1096_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1096_, 0, v___f_1095_);
    leanh::lean_closure_set(v___f_1096_, 1, v___x_1094_);
    return v___f_1096_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41()
-> *mut leanh::LeanObject {
    let mut v___f_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1097_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__40,
    );
    v___f_1099_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1099_, 0, v___f_1098_);
    leanh::lean_closure_set(v___f_1099_, 1, v___f_1097_);
    return v___f_1099_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42()
-> *mut leanh::LeanObject {
    let mut v___f_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1100_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__28;
    v___f_1101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41_once),
        _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__41,
    );
    v___f_1102_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1102_, 0, v___f_1101_);
    leanh::lean_closure_set(v___f_1102_, 1, v___f_1100_);
    return v___f_1102_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__43;
    v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instInhabitedSimpM(
    mut v_00_u03b1_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1127_: u8 = 0;
    let mut v_toFunctor_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___f_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1162_: u8 = 0;
    let mut v_unused_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v_unused_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1107_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__1,
                );
                v_toApplicative_1108_ = leanh::lean_ctor_get(v___x_1107_, 0);
                v_toFunctor_1109_ = leanh::lean_ctor_get(v_toApplicative_1108_, 0);
                v_toSeq_1110_ = leanh::lean_ctor_get(v_toApplicative_1108_, 2);
                v_toSeqLeft_1111_ = leanh::lean_ctor_get(v_toApplicative_1108_, 3);
                v_toSeqRight_1112_ = leanh::lean_ctor_get(v_toApplicative_1108_, 4);
                v___f_1113_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__2;
                v___f_1114_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_1109_, 2);
                v___f_1115_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1115_, 0, v_toFunctor_1109_);
                v___f_1116_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1116_, 0, v_toFunctor_1109_);
                v___x_1117_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1117_, 0, v___f_1115_);
                leanh::lean_ctor_set(v___x_1117_, 1, v___f_1116_);
                leanh::lean_inc(v_toSeqRight_1112_);
                v___f_1118_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1118_, 0, v_toSeqRight_1112_);
                leanh::lean_inc(v_toSeqLeft_1111_);
                v___f_1119_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1119_, 0, v_toSeqLeft_1111_);
                leanh::lean_inc(v_toSeq_1110_);
                v___f_1120_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1120_, 0, v_toSeq_1110_);
                v___x_1121_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1121_, 0, v___x_1117_);
                leanh::lean_ctor_set(v___x_1121_, 1, v___f_1113_);
                leanh::lean_ctor_set(v___x_1121_, 2, v___f_1120_);
                leanh::lean_ctor_set(v___x_1121_, 3, v___f_1119_);
                leanh::lean_ctor_set(v___x_1121_, 4, v___f_1118_);
                v___x_1122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                leanh::lean_ctor_set(v___x_1122_, 1, v___f_1114_);
                v___x_1123_ = l_StateRefT_x27_instMonad___redArg(v___x_1122_);
                v_toApplicative_1124_ = leanh::lean_ctor_get(v___x_1123_, 0);
                v_isSharedCheck_1164_ = (!leanh::lean_is_exclusive(v___x_1123_)) as u8;
                if v_isSharedCheck_1164_ == 0 {
                    v_unused_1165_ = leanh::lean_ctor_get(v___x_1123_, 1);
                    leanh::lean_dec(v_unused_1165_);
                    v___x_1126_ = v___x_1123_;
                    v_isShared_1127_ = v_isSharedCheck_1164_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1124_);
                    leanh::lean_dec(v___x_1123_);
                    v___x_1126_ = leanh::lean_box(0);
                    v_isShared_1127_ = v_isSharedCheck_1164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1128_ = leanh::lean_ctor_get(v_toApplicative_1124_, 0);
                v_toSeq_1129_ = leanh::lean_ctor_get(v_toApplicative_1124_, 2);
                v_toSeqLeft_1130_ = leanh::lean_ctor_get(v_toApplicative_1124_, 3);
                v_toSeqRight_1131_ = leanh::lean_ctor_get(v_toApplicative_1124_, 4);
                v_isSharedCheck_1162_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1124_)) as u8;
                if v_isSharedCheck_1162_ == 0 {
                    v_unused_1163_ = leanh::lean_ctor_get(v_toApplicative_1124_, 1);
                    leanh::lean_dec(v_unused_1163_);
                    v___x_1133_ = v_toApplicative_1124_;
                    v_isShared_1134_ = v_isSharedCheck_1162_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1131_);
                    leanh::lean_inc(v_toSeqLeft_1130_);
                    leanh::lean_inc(v_toSeq_1129_);
                    leanh::lean_inc(v_toFunctor_1128_);
                    leanh::lean_dec(v_toApplicative_1124_);
                    v___x_1133_ = leanh::lean_box(0);
                    v_isShared_1134_ = v_isSharedCheck_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1135_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__4;
                v___f_1136_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__5;
                leanh::lean_inc_ref(v_toFunctor_1128_);
                v___f_1137_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1137_, 0, v_toFunctor_1128_);
                v___f_1138_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1138_, 0, v_toFunctor_1128_);
                v___x_1139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1139_, 0, v___f_1137_);
                leanh::lean_ctor_set(v___x_1139_, 1, v___f_1138_);
                v___f_1140_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1140_, 0, v_toSeqRight_1131_);
                v___f_1141_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1141_, 0, v_toSeqLeft_1130_);
                v___f_1142_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1142_, 0, v_toSeq_1129_);
                if v_isShared_1134_ == 0 {
                    leanh::lean_ctor_set(v___x_1133_, 4, v___f_1140_);
                    leanh::lean_ctor_set(v___x_1133_, 3, v___f_1141_);
                    leanh::lean_ctor_set(v___x_1133_, 2, v___f_1142_);
                    leanh::lean_ctor_set(v___x_1133_, 1, v___f_1135_);
                    leanh::lean_ctor_set(v___x_1133_, 0, v___x_1139_);
                    v___x_1144_ = v___x_1133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1161_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___f_1135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 2, v___f_1142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 3, v___f_1141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 4, v___f_1140_);
                    v___x_1144_ = v_reuseFailAlloc_1161_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1127_ == 0 {
                    leanh::lean_ctor_set(v___x_1126_, 1, v___f_1136_);
                    leanh::lean_ctor_set(v___x_1126_, 0, v___x_1144_);
                    v___x_1146_ = v___x_1126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___f_1136_);
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
                v___x_1152_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__26,
                );
                v___x_1153_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__37,
                );
                v_toMonadRef_1154_ = leanh::lean_ctor_get(v___x_1153_, 0);
                v___f_1155_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_instInhabitedSimpM___closed__42,
                );
                leanh::lean_inc_ref(v___x_1151_);
                v___x_1156_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_1155_,
                    v___x_1151_,
                );
                leanh::lean_inc_ref(v_toMonadRef_1154_);
                v___x_1157_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1157_, 0, v___x_1152_);
                leanh::lean_ctor_set(v___x_1157_, 1, v_toMonadRef_1154_);
                leanh::lean_ctor_set(v___x_1157_, 2, v___x_1156_);
                v___x_1158_ = leanh::lean_obj_once(
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
    mut v_x_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Meta_Sym_Simp_instInhabitedResult_default___closed__0;
    v___x_1178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1178_, 0, v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instInhabitedMethods_default___lam__0___boxed(
    mut v_x_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
    mut v___y_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1188_);
    leanh::lean_dec_ref(v___y_1187_);
    leanh::lean_dec(v___y_1186_);
    leanh::lean_dec_ref(v___y_1185_);
    leanh::lean_dec(v___y_1184_);
    leanh::lean_dec_ref(v___y_1183_);
    leanh::lean_dec(v___y_1182_);
    leanh::lean_dec_ref(v___y_1181_);
    leanh::lean_dec(v___y_1180_);
    leanh::lean_dec_ref(v_x_1179_);
    return v_res_1190_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(
    mut v_m_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_m_1196_);
    return v_m_1196_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl___boxed(
    mut v_m_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Lean_Meta_Sym_Simp_Methods_toMethodsRefImpl(v_m_1197_);
    leanh::lean_dec_ref(v_m_1197_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(
    mut v_m_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_m_1199_);
    return v_m_1199_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl___boxed(
    mut v_m_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_Sym_Simp_MethodsRef_toMethodsImpl(v_m_1200_);
    leanh::lean_dec(v_m_1200_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___redArg(
    mut v_a_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1202_);
    v___x_1204_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1204_, 0, v_a_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___redArg___boxed(
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_a_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_Lean_Meta_Sym_Simp_getMethods___redArg(v_a_1205_);
    leanh::lean_dec(v_a_1205_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods(
    mut v_a_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
    mut v_a_1211_: *mut leanh::LeanObject,
    mut v_a_1212_: *mut leanh::LeanObject,
    mut v_a_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1208_);
    v___x_1218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1218_, 0, v_a_1208_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getMethods___boxed(
    mut v_a_1219_: *mut leanh::LeanObject,
    mut v_a_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
    mut v_a_1222_: *mut leanh::LeanObject,
    mut v_a_1223_: *mut leanh::LeanObject,
    mut v_a_1224_: *mut leanh::LeanObject,
    mut v_a_1225_: *mut leanh::LeanObject,
    mut v_a_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lean_Meta_Sym_Simp_getMethods(
        v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_,
        v_a_1227_,
    );
    leanh::lean_dec(v_a_1227_);
    leanh::lean_dec_ref(v_a_1226_);
    leanh::lean_dec(v_a_1225_);
    leanh::lean_dec_ref(v_a_1224_);
    leanh::lean_dec(v_a_1223_);
    leanh::lean_dec_ref(v_a_1222_);
    leanh::lean_dec(v_a_1221_);
    leanh::lean_dec_ref(v_a_1220_);
    leanh::lean_dec(v_a_1219_);
    return v_res_1229_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1230_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1230_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__0,
    );
    v___x_1232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1232_, 0, v___x_1231_);
    return v___x_1232_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
    mut v_x_1233_: *mut leanh::LeanObject,
    mut v_methods_1234_: *mut leanh::LeanObject,
    mut v_config_1235_: *mut leanh::LeanObject,
    mut v_s_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1268_: u8 = 0;
    let mut v_a_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v_reuseFailAlloc_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_unused_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1244_ = leanh::lean_ctor_get(v_a_1239_, 2);
                v_decls_1245_ = leanh::lean_ctor_get(v_lctx_1244_, 1);
                v_size_1246_ = leanh::lean_ctor_get(v_decls_1245_, 2);
                v_persistentCache_1247_ = leanh::lean_ctor_get(v_s_1236_, 1);
                v_funext_1248_ = leanh::lean_ctor_get(v_s_1236_, 3);
                v_isSharedCheck_1278_ = (!leanh::lean_is_exclusive(v_s_1236_)) as u8;
                if v_isSharedCheck_1278_ == 0 {
                    v_unused_1279_ = leanh::lean_ctor_get(v_s_1236_, 2);
                    leanh::lean_dec(v_unused_1279_);
                    v_unused_1280_ = leanh::lean_ctor_get(v_s_1236_, 0);
                    leanh::lean_dec(v_unused_1280_);
                    v___x_1250_ = v_s_1236_;
                    v_isShared_1251_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_funext_1248_);
                    leanh::lean_inc(v_persistentCache_1247_);
                    leanh::lean_dec(v_s_1236_);
                    v___x_1250_ = leanh::lean_box(0);
                    v_isShared_1251_ = v_isSharedCheck_1278_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1252_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v_size_1246_);
                v___x_1253_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1253_, 0, v_config_1235_);
                leanh::lean_ctor_set(v___x_1253_, 1, v_size_1246_);
                leanh::lean_ctor_set(v___x_1253_, 2, v___x_1252_);
                v___x_1254_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1,
                );
                if v_isShared_1251_ == 0 {
                    leanh::lean_ctor_set(v___x_1250_, 2, v___x_1254_);
                    leanh::lean_ctor_set(v___x_1250_, 0, v___x_1252_);
                    v___x_1256_ = v___x_1250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_persistentCache_1247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 2, v___x_1254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_funext_1248_);
                    v___x_1256_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1257_ = lean_st_mk_ref(v___x_1256_);
                leanh::lean_inc(v_a_1242_);
                leanh::lean_inc_ref(v_a_1241_);
                leanh::lean_inc(v_a_1240_);
                leanh::lean_inc_ref(v_a_1239_);
                leanh::lean_inc(v_a_1238_);
                leanh::lean_inc_ref(v_a_1237_);
                leanh::lean_inc(v___x_1257_);
                v___x_1258_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1258_) == 0 {
                    v_a_1259_ = leanh::lean_ctor_get(v___x_1258_, 0);
                    v_isSharedCheck_1268_ = (!leanh::lean_is_exclusive(v___x_1258_)) as u8;
                    if v_isSharedCheck_1268_ == 0 {
                        v___x_1261_ = v___x_1258_;
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1259_);
                        leanh::lean_dec(v___x_1258_);
                        v___x_1261_ = leanh::lean_box(0);
                        v_isShared_1262_ = v_isSharedCheck_1268_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1257_);
                    v_a_1269_ = leanh::lean_ctor_get(v___x_1258_, 0);
                    v_isSharedCheck_1276_ = (!leanh::lean_is_exclusive(v___x_1258_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1271_ = v___x_1258_;
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1269_);
                        leanh::lean_dec(v___x_1258_);
                        v___x_1271_ = leanh::lean_box(0);
                        v_isShared_1272_ = v_isSharedCheck_1276_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1263_ = lean_st_ref_get(v___x_1257_);
                leanh::lean_dec(v___x_1257_);
                v___x_1264_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1264_, 0, v_a_1259_);
                leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
                if v_isShared_1262_ == 0 {
                    leanh::lean_ctor_set(v___x_1261_, 0, v___x_1264_);
                    v___x_1266_ = v___x_1261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
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
                    v_reuseFailAlloc_1275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
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
    mut v_x_1281_: *mut leanh::LeanObject,
    mut v_methods_1282_: *mut leanh::LeanObject,
    mut v_config_1283_: *mut leanh::LeanObject,
    mut v_s_1284_: *mut leanh::LeanObject,
    mut v_a_1285_: *mut leanh::LeanObject,
    mut v_a_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1290_);
    leanh::lean_dec_ref(v_a_1289_);
    leanh::lean_dec(v_a_1288_);
    leanh::lean_dec_ref(v_a_1287_);
    leanh::lean_dec(v_a_1286_);
    leanh::lean_dec_ref(v_a_1285_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run(
    mut v_00_u03b1_1293_: *mut leanh::LeanObject,
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_methods_1295_: *mut leanh::LeanObject,
    mut v_config_1296_: *mut leanh::LeanObject,
    mut v_s_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_a_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1306_: *mut leanh::LeanObject,
    mut v_x_1307_: *mut leanh::LeanObject,
    mut v_methods_1308_: *mut leanh::LeanObject,
    mut v_config_1309_: *mut leanh::LeanObject,
    mut v_s_1310_: *mut leanh::LeanObject,
    mut v_a_1311_: *mut leanh::LeanObject,
    mut v_a_1312_: *mut leanh::LeanObject,
    mut v_a_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_a_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1316_);
    leanh::lean_dec_ref(v_a_1315_);
    leanh::lean_dec(v_a_1314_);
    leanh::lean_dec_ref(v_a_1313_);
    leanh::lean_dec(v_a_1312_);
    leanh::lean_dec_ref(v_a_1311_);
    return v_res_1318_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_Simp_SimpM_run___redArg___closed__1,
    );
    v___x_1320_ = leanh::lean_unsigned_to_nat(0);
    v___x_1321_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    leanh::lean_ctor_set(v___x_1321_, 1, v___x_1319_);
    leanh::lean_ctor_set(v___x_1321_, 2, v___x_1319_);
    leanh::lean_ctor_set(v___x_1321_, 3, v___x_1319_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(
    mut v_x_1322_: *mut leanh::LeanObject,
    mut v_methods_1323_: *mut leanh::LeanObject,
    mut v_config_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
    mut v_a_1328_: *mut leanh::LeanObject,
    mut v_a_1329_: *mut leanh::LeanObject,
    mut v_a_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1332_ = leanh::lean_ctor_get(v_a_1327_, 2);
                v_decls_1333_ = leanh::lean_ctor_get(v_lctx_1332_, 1);
                v_size_1334_ = leanh::lean_ctor_get(v_decls_1333_, 2);
                v___x_1335_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v_size_1334_);
                v___x_1336_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1336_, 0, v_config_1324_);
                leanh::lean_ctor_set(v___x_1336_, 1, v_size_1334_);
                leanh::lean_ctor_set(v___x_1336_, 2, v___x_1335_);
                v___x_1337_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg___closed__0,
                );
                v___x_1338_ = lean_st_mk_ref(v___x_1337_);
                leanh::lean_inc(v_a_1330_);
                leanh::lean_inc_ref(v_a_1329_);
                leanh::lean_inc(v_a_1328_);
                leanh::lean_inc_ref(v_a_1327_);
                leanh::lean_inc(v_a_1326_);
                leanh::lean_inc_ref(v_a_1325_);
                leanh::lean_inc(v___x_1338_);
                v___x_1339_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1339_) == 0 {
                    v_a_1340_ = leanh::lean_ctor_get(v___x_1339_, 0);
                    v_isSharedCheck_1348_ = (!leanh::lean_is_exclusive(v___x_1339_)) as u8;
                    if v_isSharedCheck_1348_ == 0 {
                        v___x_1342_ = v___x_1339_;
                        v_isShared_1343_ = v_isSharedCheck_1348_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1340_);
                        leanh::lean_dec(v___x_1339_);
                        v___x_1342_ = leanh::lean_box(0);
                        v_isShared_1343_ = v_isSharedCheck_1348_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1338_);
                    return v___x_1339_;
                }
            }
            1 => {
                v___x_1344_ = lean_st_ref_get(v___x_1338_);
                leanh::lean_dec(v___x_1338_);
                leanh::lean_dec(v___x_1344_);
                if v_isShared_1343_ == 0 {
                    v___x_1346_ = v___x_1342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1340_);
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
    mut v_x_1349_: *mut leanh::LeanObject,
    mut v_methods_1350_: *mut leanh::LeanObject,
    mut v_config_1351_: *mut leanh::LeanObject,
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
    mut v_a_1354_: *mut leanh::LeanObject,
    mut v_a_1355_: *mut leanh::LeanObject,
    mut v_a_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
    mut v_a_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1357_);
    leanh::lean_dec_ref(v_a_1356_);
    leanh::lean_dec(v_a_1355_);
    leanh::lean_dec_ref(v_a_1354_);
    leanh::lean_dec(v_a_1353_);
    leanh::lean_dec_ref(v_a_1352_);
    return v_res_1359_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_SimpM_run_x27(
    mut v_00_u03b1_1360_: *mut leanh::LeanObject,
    mut v_x_1361_: *mut leanh::LeanObject,
    mut v_methods_1362_: *mut leanh::LeanObject,
    mut v_config_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
    mut v_a_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1372_: *mut leanh::LeanObject,
    mut v_x_1373_: *mut leanh::LeanObject,
    mut v_methods_1374_: *mut leanh::LeanObject,
    mut v_config_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1381_);
    leanh::lean_dec_ref(v_a_1380_);
    leanh::lean_dec(v_a_1379_);
    leanh::lean_dec_ref(v_a_1378_);
    leanh::lean_dec(v_a_1377_);
    leanh::lean_dec_ref(v_a_1376_);
    return v_res_1383_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simp___boxed(
    mut v_a_00___x40___internal___hyg_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_1409_ = leanh::lean_ctor_get(v_a_1407_, 0);
    leanh::lean_inc_ref(v_config_1409_);
    v___x_1410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1410_, 0, v_config_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig___redArg___boxed(
    mut v_a_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1411_);
    leanh::lean_dec_ref(v_a_1411_);
    return v_res_1413_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig(
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1415_);
    return v___x_1424_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_getConfig___boxed(
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_a_1426_: *mut leanh::LeanObject,
    mut v_a_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
    mut v_a_1429_: *mut leanh::LeanObject,
    mut v_a_1430_: *mut leanh::LeanObject,
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_a_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1435_ = l_Lean_Meta_Sym_Simp_getConfig(
        v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_,
        v_a_1433_,
    );
    leanh::lean_dec(v_a_1433_);
    leanh::lean_dec_ref(v_a_1432_);
    leanh::lean_dec(v_a_1431_);
    leanh::lean_dec_ref(v_a_1430_);
    leanh::lean_dec(v_a_1429_);
    leanh::lean_dec_ref(v_a_1428_);
    leanh::lean_dec(v_a_1427_);
    leanh::lean_dec_ref(v_a_1426_);
    leanh::lean_dec(v_a_1425_);
    return v_res_1435_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_pre(
    mut v_e_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
    mut v_a_1442_: *mut leanh::LeanObject,
    mut v_a_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pre_1447_ = leanh::lean_ctor_get(v_a_1437_, 0);
    leanh::lean_inc_ref(v_pre_1447_);
    leanh::lean_inc(v_a_1445_);
    leanh::lean_inc_ref(v_a_1444_);
    leanh::lean_inc(v_a_1443_);
    leanh::lean_inc_ref(v_a_1442_);
    leanh::lean_inc(v_a_1441_);
    leanh::lean_inc_ref(v_a_1440_);
    leanh::lean_inc(v_a_1439_);
    leanh::lean_inc_ref(v_a_1438_);
    leanh::lean_inc(v_a_1437_);
    v___x_1448_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_1448_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_pre___boxed(
    mut v_e_1449_: *mut leanh::LeanObject,
    mut v_a_1450_: *mut leanh::LeanObject,
    mut v_a_1451_: *mut leanh::LeanObject,
    mut v_a_1452_: *mut leanh::LeanObject,
    mut v_a_1453_: *mut leanh::LeanObject,
    mut v_a_1454_: *mut leanh::LeanObject,
    mut v_a_1455_: *mut leanh::LeanObject,
    mut v_a_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Lean_Meta_Sym_Simp_pre(
        v_e_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_,
        v_a_1457_, v_a_1458_,
    );
    leanh::lean_dec(v_a_1458_);
    leanh::lean_dec_ref(v_a_1457_);
    leanh::lean_dec(v_a_1456_);
    leanh::lean_dec_ref(v_a_1455_);
    leanh::lean_dec(v_a_1454_);
    leanh::lean_dec_ref(v_a_1453_);
    leanh::lean_dec(v_a_1452_);
    leanh::lean_dec_ref(v_a_1451_);
    leanh::lean_dec(v_a_1450_);
    return v_res_1460_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_post(
    mut v_e_1461_: *mut leanh::LeanObject,
    mut v_a_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
    mut v_a_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_post_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_post_1472_ = leanh::lean_ctor_get(v_a_1462_, 1);
    leanh::lean_inc_ref(v_post_1472_);
    leanh::lean_inc(v_a_1470_);
    leanh::lean_inc_ref(v_a_1469_);
    leanh::lean_inc(v_a_1468_);
    leanh::lean_inc_ref(v_a_1467_);
    leanh::lean_inc(v_a_1466_);
    leanh::lean_inc_ref(v_a_1465_);
    leanh::lean_inc(v_a_1464_);
    leanh::lean_inc_ref(v_a_1463_);
    leanh::lean_inc(v_a_1462_);
    v___x_1473_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_1473_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_post___boxed(
    mut v_e_1474_: *mut leanh::LeanObject,
    mut v_a_1475_: *mut leanh::LeanObject,
    mut v_a_1476_: *mut leanh::LeanObject,
    mut v_a_1477_: *mut leanh::LeanObject,
    mut v_a_1478_: *mut leanh::LeanObject,
    mut v_a_1479_: *mut leanh::LeanObject,
    mut v_a_1480_: *mut leanh::LeanObject,
    mut v_a_1481_: *mut leanh::LeanObject,
    mut v_a_1482_: *mut leanh::LeanObject,
    mut v_a_1483_: *mut leanh::LeanObject,
    mut v_a_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_Meta_Sym_Simp_post(
        v_e_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_,
        v_a_1482_, v_a_1483_,
    );
    leanh::lean_dec(v_a_1483_);
    leanh::lean_dec_ref(v_a_1482_);
    leanh::lean_dec(v_a_1481_);
    leanh::lean_dec_ref(v_a_1480_);
    leanh::lean_dec(v_a_1479_);
    leanh::lean_dec_ref(v_a_1478_);
    leanh::lean_dec(v_a_1477_);
    leanh::lean_dec_ref(v_a_1476_);
    leanh::lean_dec(v_a_1475_);
    return v_res_1485_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
    mut v_a_1486_: *mut leanh::LeanObject,
    mut v_persistentCache_1487_: *mut leanh::LeanObject,
    mut v_transientCache_1488_: *mut leanh::LeanObject,
    mut v_funext_1489_: *mut leanh::LeanObject,
    mut v_a_x3f_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v_unused_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1492_ = lean_st_ref_take(v_a_1486_);
                v_numSteps_1493_ = leanh::lean_ctor_get(v___x_1492_, 0);
                v_isSharedCheck_1503_ = (!leanh::lean_is_exclusive(v___x_1492_)) as u8;
                if v_isSharedCheck_1503_ == 0 {
                    v_unused_1504_ = leanh::lean_ctor_get(v___x_1492_, 3);
                    leanh::lean_dec(v_unused_1504_);
                    v_unused_1505_ = leanh::lean_ctor_get(v___x_1492_, 2);
                    leanh::lean_dec(v_unused_1505_);
                    v_unused_1506_ = leanh::lean_ctor_get(v___x_1492_, 1);
                    leanh::lean_dec(v_unused_1506_);
                    v___x_1495_ = v___x_1492_;
                    v_isShared_1496_ = v_isSharedCheck_1503_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numSteps_1493_);
                    leanh::lean_dec(v___x_1492_);
                    v___x_1495_ = leanh::lean_box(0);
                    v_isShared_1496_ = v_isSharedCheck_1503_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1496_ == 0 {
                    leanh::lean_ctor_set(v___x_1495_, 3, v_funext_1489_);
                    leanh::lean_ctor_set(v___x_1495_, 2, v_transientCache_1488_);
                    leanh::lean_ctor_set(v___x_1495_, 1, v_persistentCache_1487_);
                    v___x_1498_ = v___x_1495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_numSteps_1493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_persistentCache_1487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_transientCache_1488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_funext_1489_);
                    v___x_1498_ = v_reuseFailAlloc_1502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1499_ = lean_st_ref_set(v_a_1486_, v___x_1498_);
                v___x_1500_ = leanh::lean_box(0);
                v___x_1501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
                return v___x_1501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0___boxed(
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_persistentCache_1508_: *mut leanh::LeanObject,
    mut v_transientCache_1509_: *mut leanh::LeanObject,
    mut v_funext_1510_: *mut leanh::LeanObject,
    mut v_a_x3f_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1513_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
        v_a_1507_,
        v_persistentCache_1508_,
        v_transientCache_1509_,
        v_funext_1510_,
        v_a_x3f_1511_,
    );
    leanh::lean_dec(v_a_x3f_1511_);
    leanh::lean_dec(v_a_1507_);
    return v_res_1513_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(
    mut v_k_1514_: *mut leanh::LeanObject,
    mut v_a_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
    mut v_a_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_a_1521_: *mut leanh::LeanObject,
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v_unused_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v_a_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1558_: u8 = 0;
    let mut v_unused_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1525_ = lean_st_ref_get(v_a_1517_);
                v___x_1526_ = lean_st_ref_get(v_a_1517_);
                v___x_1527_ = lean_st_ref_get(v_a_1517_);
                v_persistentCache_1528_ = leanh::lean_ctor_get(v___x_1525_, 1);
                leanh::lean_inc_ref(v_persistentCache_1528_);
                leanh::lean_dec(v___x_1525_);
                v_transientCache_1529_ = leanh::lean_ctor_get(v___x_1526_, 2);
                leanh::lean_inc_ref(v_transientCache_1529_);
                leanh::lean_dec(v___x_1526_);
                v_funext_1530_ = leanh::lean_ctor_get(v___x_1527_, 3);
                leanh::lean_inc_ref(v_funext_1530_);
                leanh::lean_dec(v___x_1527_);
                leanh::lean_inc(v_a_1523_);
                leanh::lean_inc_ref(v_a_1522_);
                leanh::lean_inc(v_a_1521_);
                leanh::lean_inc_ref(v_a_1520_);
                leanh::lean_inc(v_a_1519_);
                leanh::lean_inc_ref(v_a_1518_);
                leanh::lean_inc(v_a_1517_);
                leanh::lean_inc_ref(v_a_1516_);
                leanh::lean_inc(v_a_1515_);
                v_r_1531_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1531_) == 0 {
                    v_a_1532_ = leanh::lean_ctor_get(v_r_1531_, 0);
                    v_isSharedCheck_1548_ = (!leanh::lean_is_exclusive(v_r_1531_)) as u8;
                    if v_isSharedCheck_1548_ == 0 {
                        v___x_1534_ = v_r_1531_;
                        v_isShared_1535_ = v_isSharedCheck_1548_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1532_);
                        leanh::lean_dec(v_r_1531_);
                        v___x_1534_ = leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1548_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1549_ = leanh::lean_ctor_get(v_r_1531_, 0);
                    leanh::lean_inc(v_a_1549_);
                    leanh::lean_dec_ref_known(v_r_1531_, 1);
                    v___x_1550_ = leanh::lean_box(0);
                    v___x_1551_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                        v_a_1517_,
                        v_persistentCache_1528_,
                        v_transientCache_1529_,
                        v_funext_1530_,
                        v___x_1550_,
                    );
                    v_isSharedCheck_1558_ = (!leanh::lean_is_exclusive(v___x_1551_)) as u8;
                    if v_isSharedCheck_1558_ == 0 {
                        v_unused_1559_ = leanh::lean_ctor_get(v___x_1551_, 0);
                        leanh::lean_dec(v_unused_1559_);
                        v___x_1553_ = v___x_1551_;
                        v_isShared_1554_ = v_isSharedCheck_1558_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1551_);
                        v___x_1553_ = leanh::lean_box(0);
                        v_isShared_1554_ = v_isSharedCheck_1558_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1532_);
                if v_isShared_1535_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1534_, 1);
                    v___x_1537_ = v___x_1534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1532_);
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
                leanh::lean_dec_ref(v___x_1537_);
                v_isSharedCheck_1545_ = (!leanh::lean_is_exclusive(v___x_1538_)) as u8;
                if v_isSharedCheck_1545_ == 0 {
                    v_unused_1546_ = leanh::lean_ctor_get(v___x_1538_, 0);
                    leanh::lean_dec(v_unused_1546_);
                    v___x_1540_ = v___x_1538_;
                    v_isShared_1541_ = v_isSharedCheck_1545_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1538_);
                    v___x_1540_ = leanh::lean_box(0);
                    v_isShared_1541_ = v_isSharedCheck_1545_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1541_ == 0 {
                    leanh::lean_ctor_set(v___x_1540_, 0, v_a_1532_);
                    v___x_1543_ = v___x_1540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1532_);
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
                    leanh::lean_ctor_set_tag(v___x_1553_, 1);
                    leanh::lean_ctor_set(v___x_1553_, 0, v_a_1549_);
                    v___x_1556_ = v___x_1553_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1557_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1549_);
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
    mut v_k_1560_: *mut leanh::LeanObject,
    mut v_a_1561_: *mut leanh::LeanObject,
    mut v_a_1562_: *mut leanh::LeanObject,
    mut v_a_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
    mut v_a_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
    mut v_a_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_a_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg(
        v_k_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_,
        v_a_1568_, v_a_1569_,
    );
    leanh::lean_dec(v_a_1569_);
    leanh::lean_dec_ref(v_a_1568_);
    leanh::lean_dec(v_a_1567_);
    leanh::lean_dec_ref(v_a_1566_);
    leanh::lean_dec(v_a_1565_);
    leanh::lean_dec_ref(v_a_1564_);
    leanh::lean_dec(v_a_1563_);
    leanh::lean_dec_ref(v_a_1562_);
    leanh::lean_dec(v_a_1561_);
    return v_res_1571_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withoutModifyingCache(
    mut v_00_u03b1_1572_: *mut leanh::LeanObject,
    mut v_k_1573_: *mut leanh::LeanObject,
    mut v_a_1574_: *mut leanh::LeanObject,
    mut v_a_1575_: *mut leanh::LeanObject,
    mut v_a_1576_: *mut leanh::LeanObject,
    mut v_a_1577_: *mut leanh::LeanObject,
    mut v_a_1578_: *mut leanh::LeanObject,
    mut v_a_1579_: *mut leanh::LeanObject,
    mut v_a_1580_: *mut leanh::LeanObject,
    mut v_a_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_unused_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_a_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1617_: u8 = 0;
    let mut v_unused_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1584_ = lean_st_ref_get(v_a_1576_);
                v___x_1585_ = lean_st_ref_get(v_a_1576_);
                v___x_1586_ = lean_st_ref_get(v_a_1576_);
                v_persistentCache_1587_ = leanh::lean_ctor_get(v___x_1584_, 1);
                leanh::lean_inc_ref(v_persistentCache_1587_);
                leanh::lean_dec(v___x_1584_);
                v_transientCache_1588_ = leanh::lean_ctor_get(v___x_1585_, 2);
                leanh::lean_inc_ref(v_transientCache_1588_);
                leanh::lean_dec(v___x_1585_);
                v_funext_1589_ = leanh::lean_ctor_get(v___x_1586_, 3);
                leanh::lean_inc_ref(v_funext_1589_);
                leanh::lean_dec(v___x_1586_);
                leanh::lean_inc(v_a_1582_);
                leanh::lean_inc_ref(v_a_1581_);
                leanh::lean_inc(v_a_1580_);
                leanh::lean_inc_ref(v_a_1579_);
                leanh::lean_inc(v_a_1578_);
                leanh::lean_inc_ref(v_a_1577_);
                leanh::lean_inc(v_a_1576_);
                leanh::lean_inc_ref(v_a_1575_);
                leanh::lean_inc(v_a_1574_);
                v_r_1590_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1590_) == 0 {
                    v_a_1591_ = leanh::lean_ctor_get(v_r_1590_, 0);
                    v_isSharedCheck_1607_ = (!leanh::lean_is_exclusive(v_r_1590_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1593_ = v_r_1590_;
                        v_isShared_1594_ = v_isSharedCheck_1607_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1591_);
                        leanh::lean_dec(v_r_1590_);
                        v___x_1593_ = leanh::lean_box(0);
                        v_isShared_1594_ = v_isSharedCheck_1607_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1608_ = leanh::lean_ctor_get(v_r_1590_, 0);
                    leanh::lean_inc(v_a_1608_);
                    leanh::lean_dec_ref_known(v_r_1590_, 1);
                    v___x_1609_ = leanh::lean_box(0);
                    v___x_1610_ = l_Lean_Meta_Sym_Simp_withoutModifyingCache___redArg___lam__0(
                        v_a_1576_,
                        v_persistentCache_1587_,
                        v_transientCache_1588_,
                        v_funext_1589_,
                        v___x_1609_,
                    );
                    v_isSharedCheck_1617_ = (!leanh::lean_is_exclusive(v___x_1610_)) as u8;
                    if v_isSharedCheck_1617_ == 0 {
                        v_unused_1618_ = leanh::lean_ctor_get(v___x_1610_, 0);
                        leanh::lean_dec(v_unused_1618_);
                        v___x_1612_ = v___x_1610_;
                        v_isShared_1613_ = v_isSharedCheck_1617_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1610_);
                        v___x_1612_ = leanh::lean_box(0);
                        v_isShared_1613_ = v_isSharedCheck_1617_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1591_);
                if v_isShared_1594_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1593_, 1);
                    v___x_1596_ = v___x_1593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1591_);
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
                leanh::lean_dec_ref(v___x_1596_);
                v_isSharedCheck_1604_ = (!leanh::lean_is_exclusive(v___x_1597_)) as u8;
                if v_isSharedCheck_1604_ == 0 {
                    v_unused_1605_ = leanh::lean_ctor_get(v___x_1597_, 0);
                    leanh::lean_dec(v_unused_1605_);
                    v___x_1599_ = v___x_1597_;
                    v_isShared_1600_ = v_isSharedCheck_1604_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1597_);
                    v___x_1599_ = leanh::lean_box(0);
                    v_isShared_1600_ = v_isSharedCheck_1604_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1600_ == 0 {
                    leanh::lean_ctor_set(v___x_1599_, 0, v_a_1591_);
                    v___x_1602_ = v___x_1599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1591_);
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
                    leanh::lean_ctor_set_tag(v___x_1612_, 1);
                    leanh::lean_ctor_set(v___x_1612_, 0, v_a_1608_);
                    v___x_1615_ = v___x_1612_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1616_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1608_);
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
    mut v_00_u03b1_1619_: *mut leanh::LeanObject,
    mut v_k_1620_: *mut leanh::LeanObject,
    mut v_a_1621_: *mut leanh::LeanObject,
    mut v_a_1622_: *mut leanh::LeanObject,
    mut v_a_1623_: *mut leanh::LeanObject,
    mut v_a_1624_: *mut leanh::LeanObject,
    mut v_a_1625_: *mut leanh::LeanObject,
    mut v_a_1626_: *mut leanh::LeanObject,
    mut v_a_1627_: *mut leanh::LeanObject,
    mut v_a_1628_: *mut leanh::LeanObject,
    mut v_a_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1629_);
    leanh::lean_dec_ref(v_a_1628_);
    leanh::lean_dec(v_a_1627_);
    leanh::lean_dec_ref(v_a_1626_);
    leanh::lean_dec(v_a_1625_);
    leanh::lean_dec_ref(v_a_1624_);
    leanh::lean_dec(v_a_1623_);
    leanh::lean_dec_ref(v_a_1622_);
    leanh::lean_dec(v_a_1621_);
    return v_res_1631_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
    mut v_a_1632_: *mut leanh::LeanObject,
    mut v_transientCache_1633_: *mut leanh::LeanObject,
    mut v_funext_1634_: *mut leanh::LeanObject,
    mut v_a_x3f_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1649_: u8 = 0;
    let mut v_unused_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1637_ = lean_st_ref_take(v_a_1632_);
                v_numSteps_1638_ = leanh::lean_ctor_get(v___x_1637_, 0);
                v_persistentCache_1639_ = leanh::lean_ctor_get(v___x_1637_, 1);
                v_isSharedCheck_1649_ = (!leanh::lean_is_exclusive(v___x_1637_)) as u8;
                if v_isSharedCheck_1649_ == 0 {
                    v_unused_1650_ = leanh::lean_ctor_get(v___x_1637_, 3);
                    leanh::lean_dec(v_unused_1650_);
                    v_unused_1651_ = leanh::lean_ctor_get(v___x_1637_, 2);
                    leanh::lean_dec(v_unused_1651_);
                    v___x_1641_ = v___x_1637_;
                    v_isShared_1642_ = v_isSharedCheck_1649_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_persistentCache_1639_);
                    leanh::lean_inc(v_numSteps_1638_);
                    leanh::lean_dec(v___x_1637_);
                    v___x_1641_ = leanh::lean_box(0);
                    v_isShared_1642_ = v_isSharedCheck_1649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1642_ == 0 {
                    leanh::lean_ctor_set(v___x_1641_, 3, v_funext_1634_);
                    leanh::lean_ctor_set(v___x_1641_, 2, v_transientCache_1633_);
                    v___x_1644_ = v___x_1641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1648_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_numSteps_1638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_persistentCache_1639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_transientCache_1633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_funext_1634_);
                    v___x_1644_ = v_reuseFailAlloc_1648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1645_ = lean_st_ref_set(v_a_1632_, v___x_1644_);
                v___x_1646_ = leanh::lean_box(0);
                v___x_1647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1647_, 0, v___x_1646_);
                return v___x_1647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0___boxed(
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_transientCache_1653_: *mut leanh::LeanObject,
    mut v_funext_1654_: *mut leanh::LeanObject,
    mut v_a_x3f_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
        v_a_1652_,
        v_transientCache_1653_,
        v_funext_1654_,
        v_a_x3f_1655_,
    );
    leanh::lean_dec(v_a_x3f_1655_);
    leanh::lean_dec(v_a_1652_);
    return v_res_1657_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(
    mut v_k_1658_: *mut leanh::LeanObject,
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
    mut v_a_1662_: *mut leanh::LeanObject,
    mut v_a_1663_: *mut leanh::LeanObject,
    mut v_a_1664_: *mut leanh::LeanObject,
    mut v_a_1665_: *mut leanh::LeanObject,
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_a_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_unused_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut v_a_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1700_: u8 = 0;
    let mut v_unused_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_st_ref_get(v_a_1661_);
                v___x_1670_ = lean_st_ref_get(v_a_1661_);
                v_transientCache_1671_ = leanh::lean_ctor_get(v___x_1669_, 2);
                leanh::lean_inc_ref(v_transientCache_1671_);
                leanh::lean_dec(v___x_1669_);
                v_funext_1672_ = leanh::lean_ctor_get(v___x_1670_, 3);
                leanh::lean_inc_ref(v_funext_1672_);
                leanh::lean_dec(v___x_1670_);
                leanh::lean_inc(v_a_1667_);
                leanh::lean_inc_ref(v_a_1666_);
                leanh::lean_inc(v_a_1665_);
                leanh::lean_inc_ref(v_a_1664_);
                leanh::lean_inc(v_a_1663_);
                leanh::lean_inc_ref(v_a_1662_);
                leanh::lean_inc(v_a_1661_);
                leanh::lean_inc_ref(v_a_1660_);
                leanh::lean_inc(v_a_1659_);
                v_r_1673_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1673_) == 0 {
                    v_a_1674_ = leanh::lean_ctor_get(v_r_1673_, 0);
                    v_isSharedCheck_1690_ = (!leanh::lean_is_exclusive(v_r_1673_)) as u8;
                    if v_isSharedCheck_1690_ == 0 {
                        v___x_1676_ = v_r_1673_;
                        v_isShared_1677_ = v_isSharedCheck_1690_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1674_);
                        leanh::lean_dec(v_r_1673_);
                        v___x_1676_ = leanh::lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1691_ = leanh::lean_ctor_get(v_r_1673_, 0);
                    leanh::lean_inc(v_a_1691_);
                    leanh::lean_dec_ref_known(v_r_1673_, 1);
                    v___x_1692_ = leanh::lean_box(0);
                    v___x_1693_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                        v_a_1661_,
                        v_transientCache_1671_,
                        v_funext_1672_,
                        v___x_1692_,
                    );
                    v_isSharedCheck_1700_ = (!leanh::lean_is_exclusive(v___x_1693_)) as u8;
                    if v_isSharedCheck_1700_ == 0 {
                        v_unused_1701_ = leanh::lean_ctor_get(v___x_1693_, 0);
                        leanh::lean_dec(v_unused_1701_);
                        v___x_1695_ = v___x_1693_;
                        v_isShared_1696_ = v_isSharedCheck_1700_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1693_);
                        v___x_1695_ = leanh::lean_box(0);
                        v_isShared_1696_ = v_isSharedCheck_1700_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1674_);
                if v_isShared_1677_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1676_, 1);
                    v___x_1679_ = v___x_1676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1674_);
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
                leanh::lean_dec_ref(v___x_1679_);
                v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1687_ == 0 {
                    v_unused_1688_ = leanh::lean_ctor_get(v___x_1680_, 0);
                    leanh::lean_dec(v_unused_1688_);
                    v___x_1682_ = v___x_1680_;
                    v_isShared_1683_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1680_);
                    v___x_1682_ = leanh::lean_box(0);
                    v_isShared_1683_ = v_isSharedCheck_1687_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1683_ == 0 {
                    leanh::lean_ctor_set(v___x_1682_, 0, v_a_1674_);
                    v___x_1685_ = v___x_1682_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1674_);
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
                    leanh::lean_ctor_set_tag(v___x_1695_, 1);
                    leanh::lean_ctor_set(v___x_1695_, 0, v_a_1691_);
                    v___x_1698_ = v___x_1695_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1691_);
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
    mut v_k_1702_: *mut leanh::LeanObject,
    mut v_a_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
    mut v_a_1706_: *mut leanh::LeanObject,
    mut v_a_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v_a_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg(
        v_k_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
        v_a_1710_, v_a_1711_,
    );
    leanh::lean_dec(v_a_1711_);
    leanh::lean_dec_ref(v_a_1710_);
    leanh::lean_dec(v_a_1709_);
    leanh::lean_dec_ref(v_a_1708_);
    leanh::lean_dec(v_a_1707_);
    leanh::lean_dec_ref(v_a_1706_);
    leanh::lean_dec(v_a_1705_);
    leanh::lean_dec_ref(v_a_1704_);
    leanh::lean_dec(v_a_1703_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_withFreshTransientCache(
    mut v_00_u03b1_1714_: *mut leanh::LeanObject,
    mut v_k_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
    mut v_a_1720_: *mut leanh::LeanObject,
    mut v_a_1721_: *mut leanh::LeanObject,
    mut v_a_1722_: *mut leanh::LeanObject,
    mut v_a_1723_: *mut leanh::LeanObject,
    mut v_a_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut v_unused_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_unused_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1726_ = lean_st_ref_get(v_a_1718_);
                v___x_1727_ = lean_st_ref_get(v_a_1718_);
                v_transientCache_1728_ = leanh::lean_ctor_get(v___x_1726_, 2);
                leanh::lean_inc_ref(v_transientCache_1728_);
                leanh::lean_dec(v___x_1726_);
                v_funext_1729_ = leanh::lean_ctor_get(v___x_1727_, 3);
                leanh::lean_inc_ref(v_funext_1729_);
                leanh::lean_dec(v___x_1727_);
                leanh::lean_inc(v_a_1724_);
                leanh::lean_inc_ref(v_a_1723_);
                leanh::lean_inc(v_a_1722_);
                leanh::lean_inc_ref(v_a_1721_);
                leanh::lean_inc(v_a_1720_);
                leanh::lean_inc_ref(v_a_1719_);
                leanh::lean_inc(v_a_1718_);
                leanh::lean_inc_ref(v_a_1717_);
                leanh::lean_inc(v_a_1716_);
                v_r_1730_ = leanh::lean_apply_10(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_1730_) == 0 {
                    v_a_1731_ = leanh::lean_ctor_get(v_r_1730_, 0);
                    v_isSharedCheck_1747_ = (!leanh::lean_is_exclusive(v_r_1730_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1733_ = v_r_1730_;
                        v_isShared_1734_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1731_);
                        leanh::lean_dec(v_r_1730_);
                        v___x_1733_ = leanh::lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1748_ = leanh::lean_ctor_get(v_r_1730_, 0);
                    leanh::lean_inc(v_a_1748_);
                    leanh::lean_dec_ref_known(v_r_1730_, 1);
                    v___x_1749_ = leanh::lean_box(0);
                    v___x_1750_ = l_Lean_Meta_Sym_Simp_withFreshTransientCache___redArg___lam__0(
                        v_a_1718_,
                        v_transientCache_1728_,
                        v_funext_1729_,
                        v___x_1749_,
                    );
                    v_isSharedCheck_1757_ = (!leanh::lean_is_exclusive(v___x_1750_)) as u8;
                    if v_isSharedCheck_1757_ == 0 {
                        v_unused_1758_ = leanh::lean_ctor_get(v___x_1750_, 0);
                        leanh::lean_dec(v_unused_1758_);
                        v___x_1752_ = v___x_1750_;
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1750_);
                        v___x_1752_ = leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1757_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1731_);
                if v_isShared_1734_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1733_, 1);
                    v___x_1736_ = v___x_1733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1731_);
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
                leanh::lean_dec_ref(v___x_1736_);
                v_isSharedCheck_1744_ = (!leanh::lean_is_exclusive(v___x_1737_)) as u8;
                if v_isSharedCheck_1744_ == 0 {
                    v_unused_1745_ = leanh::lean_ctor_get(v___x_1737_, 0);
                    leanh::lean_dec(v_unused_1745_);
                    v___x_1739_ = v___x_1737_;
                    v_isShared_1740_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1737_);
                    v___x_1739_ = leanh::lean_box(0);
                    v_isShared_1740_ = v_isSharedCheck_1744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1740_ == 0 {
                    leanh::lean_ctor_set(v___x_1739_, 0, v_a_1731_);
                    v___x_1742_ = v___x_1739_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1731_);
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
                    leanh::lean_ctor_set_tag(v___x_1752_, 1);
                    leanh::lean_ctor_set(v___x_1752_, 0, v_a_1748_);
                    v___x_1755_ = v___x_1752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1748_);
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
    mut v_00_u03b1_1759_: *mut leanh::LeanObject,
    mut v_k_1760_: *mut leanh::LeanObject,
    mut v_a_1761_: *mut leanh::LeanObject,
    mut v_a_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
    mut v_a_1769_: *mut leanh::LeanObject,
    mut v_a_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1769_);
    leanh::lean_dec_ref(v_a_1768_);
    leanh::lean_dec(v_a_1767_);
    leanh::lean_dec_ref(v_a_1766_);
    leanh::lean_dec(v_a_1765_);
    leanh::lean_dec_ref(v_a_1764_);
    leanh::lean_dec(v_a_1763_);
    leanh::lean_dec_ref(v_a_1762_);
    leanh::lean_dec(v_a_1761_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Meta_Sym_simp(
    mut v_e_1772_: *mut leanh::LeanObject,
    mut v_methods_1773_: *mut leanh::LeanObject,
    mut v_config_1774_: *mut leanh::LeanObject,
    mut v_a_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Simp_simp___boxed as *mut core::ffi::c_void,
        11,
        1,
    );
    leanh::lean_closure_set(v___x_1782_, 0, v_e_1772_);
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
    mut v_e_1784_: *mut leanh::LeanObject,
    mut v_methods_1785_: *mut leanh::LeanObject,
    mut v_config_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1792_);
    leanh::lean_dec_ref(v_a_1791_);
    leanh::lean_dec(v_a_1790_);
    leanh::lean_dec_ref(v_a_1789_);
    leanh::lean_dec(v_a_1788_);
    leanh::lean_dec_ref(v_a_1787_);
    return v_res_1794_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_SimpM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed =
        _init_l___private_Lean_Meta_Sym_Simp_SimpM_0__Lean_Meta_Sym_Simp_MethodsRefPointed();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_SimpM(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_SimpM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
}