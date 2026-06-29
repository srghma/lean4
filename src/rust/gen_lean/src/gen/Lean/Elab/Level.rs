// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Lean.Elab.AutoBound
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_uget_borrowed, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNatLit_x3f, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_EStateM_bind, l_EStateM_instMonad___lam__0, l_EStateM_instMonad___lam__1,
    l_EStateM_instMonad___lam__2, l_EStateM_map, l_EStateM_pure, l_EStateM_seqRight,
    l_Lean_Name_num___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId,
    l_Lean_Syntax_getKind, l_Lean_replaceRef, l_ReaderT_bind___boxed, l_ReaderT_read___boxed,
};
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueNat;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Option_get___redArg, lean_register_option};
use crate::r#gen::Lean::Elab::AutoBound::{
    initialize_Lean_Elab_AutoBound, l_Lean_Elab_isValidAutoBoundLevelName,
    l_Lean_Elab_relaxedAutoImplicit, runtime_initialize_Lean_Elab_AutoBound,
};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Level::{
    l_Lean_Level_addOffset, l_Lean_Level_ofNat, l_Lean_mkLevelIMax_x27, l_Lean_mkLevelMVar,
    l_Lean_mkLevelMax_x27, l_Lean_mkLevelParam,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_MetavarContext_addLevelMVarDecl;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value:
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
    m_fun: l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value:
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
    m_fun: l_EStateM_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value:
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
    m_fun: l_EStateM_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value:
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
    m_fun: l_EStateM_instMonad___lam__2 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_map as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_pure as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_seqRight as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_bind as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value:
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
    m_fun: l_ReaderT_read___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value:
    crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_bind___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Level_instMonadOptionsLevelElabM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value:
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
    m_fun: l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value:
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
    m_fun: l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value:
    crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_bind___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Level_instMonadRefLevelElabM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value:
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
    m_fun: l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Level_instAddMessageContextLevelElabM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instAddMessageContextLevelElabM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value:
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
    m_fun: l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value:
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
    m_fun: l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value:
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
    m_fun: l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value:
    crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_bind___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 97, 120, 85, 110, 105, 118, 101, 114, 115, 101, 79, 102, 102, 115, 101, 116, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,567086787768948975 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 111, 102, 102, 115, 101, 116, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [76, 101, 118, 101, 108, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15105846377774697951 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11104077691307262051 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Level_maxUniverseOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [85, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 111, 102, 102, 115, 101, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 101, 120, 99, 101, 101, 100, 115, 32, 109, 97, 120, 105, 109, 117, 109, 32, 111, 102, 102, 115, 101, 116, 32, 96, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<209> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 209, m_capacity: 209, m_length: 208, m_data: [84, 104, 105, 115, 32, 99, 111, 100, 101, 32, 105, 115, 32, 112, 114, 111, 98, 97, 98, 108, 121, 32, 109, 105, 115, 117, 115, 105, 110, 103, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115, 44, 32, 115, 105, 110, 99, 101, 32, 116, 104, 101, 121, 32, 97, 114, 101, 32, 117, 115, 117, 97, 108, 108, 121, 32, 115, 109, 97, 108, 108, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 115, 46, 32, 73, 102, 32, 121, 111, 117, 32, 97, 114, 101, 32, 99, 111, 110, 102, 105, 100, 101, 110, 116, 32, 116, 104, 105, 115, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 99, 97, 115, 101, 44, 32, 121, 111, 117, 32, 99, 97, 110, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 116, 104, 101, 32, 108, 105, 109, 105, 116, 32, 117, 115, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 85, 110, 105, 118, 101, 114, 115, 101, 79, 102, 102, 115, 101, 116, 32, 60, 108, 105, 109, 105, 116, 62, 96, 0]};
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Level_elabLevel___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11423656342444823216 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Level_elabLevel___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16533827001853265987 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [109, 97, 120, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11423656342444823216 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Level_elabLevel___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__3_value)
                as *mut crate::leanh::LeanObject,
            7017890982578468202 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [105, 109, 97, 120, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11423656342444823216 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Level_elabLevel___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__5_value)
                as *mut crate::leanh::LeanObject,
            2051294913818044796 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__7_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [104, 111, 108, 101, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Level_elabLevel___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11423656342444823216 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Level_elabLevel___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__7_value)
                as *mut crate::leanh::LeanObject,
            1315703591728338576 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__9_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__9_value)
                as *mut crate::leanh::LeanObject,
            6110315075117401315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__11_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__11_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__13_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 100, 100, 76, 105, 116, 0],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Level_elabLevel___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11423656342444823216 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Level_elabLevel___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__14_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__13_value)
                as *mut crate::leanh::LeanObject,
            12560806670959244085 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Level_elabLevel___closed__15_value: crate::leanh::LeanStringObject<38> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115,
            101, 32, 108, 101, 118, 101, 108, 32, 115, 121, 110, 116, 97, 120, 32, 107, 105, 110,
            100, 0,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Level_elabLevel___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Level_elabLevel___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Level_elabLevel___closed__17_value: crate::leanh::LeanStringObject<25> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108,
            101, 118, 101, 108, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_Level_elabLevel___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Level_elabLevel___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Level_elabLevel___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Level_elabLevel___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(
    mut v_____do__lift_701_: *mut crate::leanh::LeanObject,
    mut v___y_702_: *mut crate::leanh::LeanObject,
    mut v___y_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_704_ = crate::leanh::lean_ctor_get(v_____do__lift_701_, 0);
    crate::leanh::lean_inc_ref(v_options_704_);
    v___x_705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_705_, 0, v_options_704_);
    crate::leanh::lean_ctor_set(v___x_705_, 1, v___y_703_);
    return v___x_705_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(
    mut v_____do__lift_706_: *mut crate::leanh::LeanObject,
    mut v___y_707_: *mut crate::leanh::LeanObject,
    mut v___y_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(
        v_____do__lift_706_,
        v___y_707_,
        v___y_708_,
    );
    crate::leanh::lean_dec_ref(v___y_707_);
    crate::leanh::lean_dec_ref(v_____do__lift_706_);
    return v_res_709_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(
    mut v_____do__lift_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
    mut v___y_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_740_ = crate::leanh::lean_ctor_get(v_____do__lift_737_, 1);
    crate::leanh::lean_inc(v_ref_740_);
    v___x_741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_741_, 0, v_ref_740_);
    crate::leanh::lean_ctor_set(v___x_741_, 1, v___y_739_);
    return v___x_741_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(
    mut v_____do__lift_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(
        v_____do__lift_742_,
        v___y_743_,
        v___y_744_,
    );
    crate::leanh::lean_dec_ref(v___y_743_);
    crate::leanh::lean_dec_ref(v_____do__lift_742_);
    return v_res_745_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(
    mut v_00_u03b1_746_: *mut crate::leanh::LeanObject,
    mut v_ref_747_: *mut crate::leanh::LeanObject,
    mut v_x_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicit_752_: u8 = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_751_ = crate::leanh::lean_ctor_get(v___y_749_, 0);
    v_autoBoundImplicit_752_ = crate::leanh::lean_ctor_get_uint8(
        v___y_749_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_inc_ref(v_options_751_);
    v___x_753_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_753_, 0, v_options_751_);
    crate::leanh::lean_ctor_set(v___x_753_, 1, v_ref_747_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_753_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_autoBoundImplicit_752_,
    );
    v___x_754_ = crate::leanh::lean_apply_2(v_x_748_, v___x_753_, v___y_750_);
    return v___x_754_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1___boxed(
    mut v_00_u03b1_755_: *mut crate::leanh::LeanObject,
    mut v_ref_756_: *mut crate::leanh::LeanObject,
    mut v_x_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v___y_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(
        v_00_u03b1_755_,
        v_ref_756_,
        v_x_757_,
        v___y_758_,
        v___y_759_,
    );
    crate::leanh::lean_dec_ref(v___y_758_);
    return v_res_760_;
}
pub unsafe fn l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(
    mut v_msg_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
    mut v___y_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_774_, 0, v_msg_771_);
    crate::leanh::lean_ctor_set(v___x_774_, 1, v___y_773_);
    return v___x_774_;
}
pub unsafe fn l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(
    mut v_msg_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
    mut v___y_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(
        v_msg_775_, v___y_776_, v___y_777_,
    );
    crate::leanh::lean_dec_ref(v___y_776_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(
    mut v___y_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_782_);
    v___x_783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_783_, 0, v___y_782_);
    crate::leanh::lean_ctor_set(v___x_783_, 1, v___y_782_);
    return v___x_783_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ =
        l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(v___y_784_, v___y_785_);
    crate::leanh::lean_dec_ref(v___y_784_);
    return v_res_786_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(
    mut v_____do__lift_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ngen_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ngen_790_ = crate::leanh::lean_ctor_get(v_____do__lift_787_, 0);
    crate::leanh::lean_inc_ref(v_ngen_790_);
    v___x_791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_791_, 0, v_ngen_790_);
    crate::leanh::lean_ctor_set(v___x_791_, 1, v___y_789_);
    return v___x_791_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(
    mut v_____do__lift_792_: *mut crate::leanh::LeanObject,
    mut v___y_793_: *mut crate::leanh::LeanObject,
    mut v___y_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(
        v_____do__lift_792_,
        v___y_793_,
        v___y_794_,
    );
    crate::leanh::lean_dec_ref(v___y_793_);
    crate::leanh::lean_dec_ref(v_____do__lift_792_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(
    mut v_ngen_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
    mut v___y_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mctx_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_unused_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mctx_799_ = crate::leanh::lean_ctor_get(v___y_798_, 1);
                v_levelNames_800_ = crate::leanh::lean_ctor_get(v___y_798_, 2);
                v_isSharedCheck_809_ = (!crate::leanh::lean_is_exclusive(v___y_798_)) as u8;
                if v_isSharedCheck_809_ == 0 {
                    v_unused_810_ = crate::leanh::lean_ctor_get(v___y_798_, 0);
                    crate::leanh::lean_dec(v_unused_810_);
                    v___x_802_ = v___y_798_;
                    v_isShared_803_ = v_isSharedCheck_809_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_levelNames_800_);
                    crate::leanh::lean_inc(v_mctx_799_);
                    crate::leanh::lean_dec(v___y_798_);
                    v___x_802_ = crate::leanh::lean_box(0);
                    v_isShared_803_ = v_isSharedCheck_809_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_804_ = crate::leanh::lean_box(0);
                if v_isShared_803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_802_, 0, v_ngen_796_);
                    v___x_806_ = v___x_802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_808_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 0, v_ngen_796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 1, v_mctx_799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_808_, 2, v_levelNames_800_);
                    v___x_806_ = v_reuseFailAlloc_808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_804_);
                crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_806_);
                return v___x_807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(
    mut v_ngen_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(
        v_ngen_811_,
        v___y_812_,
        v___y_813_,
    );
    crate::leanh::lean_dec_ref(v___y_812_);
    return v_res_814_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(
    mut v___y_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ngen_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v_namePrefix_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v_r_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut v_isSharedCheck_849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ngen_827_ = crate::leanh::lean_ctor_get(v___y_826_, 0);
                v_mctx_828_ = crate::leanh::lean_ctor_get(v___y_826_, 1);
                v_levelNames_829_ = crate::leanh::lean_ctor_get(v___y_826_, 2);
                v_isSharedCheck_849_ = (!crate::leanh::lean_is_exclusive(v___y_826_)) as u8;
                if v_isSharedCheck_849_ == 0 {
                    v___x_831_ = v___y_826_;
                    v_isShared_832_ = v_isSharedCheck_849_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_levelNames_829_);
                    crate::leanh::lean_inc(v_mctx_828_);
                    crate::leanh::lean_inc(v_ngen_827_);
                    crate::leanh::lean_dec(v___y_826_);
                    v___x_831_ = crate::leanh::lean_box(0);
                    v_isShared_832_ = v_isSharedCheck_849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_namePrefix_833_ = crate::leanh::lean_ctor_get(v_ngen_827_, 0);
                v_idx_834_ = crate::leanh::lean_ctor_get(v_ngen_827_, 1);
                v_isSharedCheck_848_ = (!crate::leanh::lean_is_exclusive(v_ngen_827_)) as u8;
                if v_isSharedCheck_848_ == 0 {
                    v___x_836_ = v_ngen_827_;
                    v_isShared_837_ = v_isSharedCheck_848_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_834_);
                    crate::leanh::lean_inc(v_namePrefix_833_);
                    crate::leanh::lean_dec(v_ngen_827_);
                    v___x_836_ = crate::leanh::lean_box(0);
                    v_isShared_837_ = v_isSharedCheck_848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_834_);
                crate::leanh::lean_inc(v_namePrefix_833_);
                v_r_838_ = l_Lean_Name_num___override(v_namePrefix_833_, v_idx_834_);
                v___x_839_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_840_ = lean_nat_add(v_idx_834_, v___x_839_);
                crate::leanh::lean_dec(v_idx_834_);
                if v_isShared_837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_836_, 1, v___x_840_);
                    v___x_842_ = v___x_836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_847_, 0, v_namePrefix_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_840_);
                    v___x_842_ = v_reuseFailAlloc_847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_832_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_842_);
                    v___x_844_ = v___x_831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_846_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_846_, 1, v_mctx_828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_846_, 2, v_levelNames_829_);
                    v___x_844_ = v_reuseFailAlloc_846_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_845_, 0, v_r_838_);
                crate::leanh::lean_ctor_set(v___x_845_, 1, v___x_844_);
                return v___x_845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_857_: u8 = 0;
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_852_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_851_);
                v_a_853_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                v_a_854_ = crate::leanh::lean_ctor_get(v___x_852_, 1);
                v_isSharedCheck_861_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                if v_isSharedCheck_861_ == 0 {
                    v___x_856_ = v___x_852_;
                    v_isShared_857_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_854_);
                    crate::leanh::lean_inc(v_a_853_);
                    crate::leanh::lean_dec(v___x_852_);
                    v___x_856_ = crate::leanh::lean_box(0);
                    v_isShared_857_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_857_ == 0 {
                    v___x_859_ = v___x_856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_860_, 1, v_a_854_);
                    v___x_859_ = v_reuseFailAlloc_860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(
        v___y_862_, v___y_863_,
    );
    crate::leanh::lean_dec_ref(v___y_862_);
    return v_res_864_;
}
pub unsafe fn l_Lean_Elab_Level_mkFreshLevelMVar(
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v_ngen_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v_a_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_867_ =
                    l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(
                        v_a_865_, v_a_866_,
                    );
                if crate::leanh::lean_obj_tag(v___x_867_) == 0 {
                    v_a_868_ = crate::leanh::lean_ctor_get(v___x_867_, 1);
                    v_a_869_ = crate::leanh::lean_ctor_get(v___x_867_, 0);
                    v_isSharedCheck_888_ = (!crate::leanh::lean_is_exclusive(v___x_867_)) as u8;
                    if v_isSharedCheck_888_ == 0 {
                        v___x_871_ = v___x_867_;
                        v_isShared_872_ = v_isSharedCheck_888_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_868_);
                        crate::leanh::lean_inc(v_a_869_);
                        crate::leanh::lean_dec(v___x_867_);
                        v___x_871_ = crate::leanh::lean_box(0);
                        v_isShared_872_ = v_isSharedCheck_888_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_889_ = crate::leanh::lean_ctor_get(v___x_867_, 0);
                    v_a_890_ = crate::leanh::lean_ctor_get(v___x_867_, 1);
                    v_isSharedCheck_897_ = (!crate::leanh::lean_is_exclusive(v___x_867_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_892_ = v___x_867_;
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_890_);
                        crate::leanh::lean_inc(v_a_889_);
                        crate::leanh::lean_dec(v___x_867_);
                        v___x_892_ = crate::leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ngen_873_ = crate::leanh::lean_ctor_get(v_a_868_, 0);
                v_mctx_874_ = crate::leanh::lean_ctor_get(v_a_868_, 1);
                v_levelNames_875_ = crate::leanh::lean_ctor_get(v_a_868_, 2);
                v_isSharedCheck_887_ = (!crate::leanh::lean_is_exclusive(v_a_868_)) as u8;
                if v_isSharedCheck_887_ == 0 {
                    v___x_877_ = v_a_868_;
                    v_isShared_878_ = v_isSharedCheck_887_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_levelNames_875_);
                    crate::leanh::lean_inc(v_mctx_874_);
                    crate::leanh::lean_inc(v_ngen_873_);
                    crate::leanh::lean_dec(v_a_868_);
                    v___x_877_ = crate::leanh::lean_box(0);
                    v_isShared_878_ = v_isSharedCheck_887_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_869_);
                v___x_879_ = l_Lean_MetavarContext_addLevelMVarDecl(v_mctx_874_, v_a_869_);
                if v_isShared_878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_877_, 1, v___x_879_);
                    v___x_881_ = v___x_877_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_886_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 0, v_ngen_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 2, v_levelNames_875_);
                    v___x_881_ = v_reuseFailAlloc_886_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_882_ = l_Lean_mkLevelMVar(v_a_869_);
                if v_isShared_872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_871_, 1, v___x_881_);
                    crate::leanh::lean_ctor_set(v___x_871_, 0, v___x_882_);
                    v___x_884_ = v___x_871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_881_);
                    v___x_884_ = v_reuseFailAlloc_885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_884_;
            }
            5 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Level_mkFreshLevelMVar___boxed(
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l_Lean_Elab_Level_mkFreshLevelMVar(v_a_898_, v_a_899_);
    crate::leanh::lean_dec_ref(v_a_898_);
    return v_res_900_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(v___y_902_);
    return v___x_903_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(
    mut v___y_904_: *mut crate::leanh::LeanObject,
    mut v___y_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(v___y_904_, v___y_905_);
    crate::leanh::lean_dec_ref(v___y_904_);
    return v_res_906_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(
    mut v_name_907_: *mut crate::leanh::LeanObject,
    mut v_decl_908_: *mut crate::leanh::LeanObject,
    mut v_ref_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_924_: u8 = 0;
    let mut v_unused_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_911_ = crate::leanh::lean_ctor_get(v_decl_908_, 0);
                v_descr_912_ = crate::leanh::lean_ctor_get(v_decl_908_, 1);
                v_deprecation_x3f_913_ = crate::leanh::lean_ctor_get(v_decl_908_, 2);
                crate::leanh::lean_inc(v_defValue_911_);
                v___x_914_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_914_, 0, v_defValue_911_);
                crate::leanh::lean_inc(v_deprecation_x3f_913_);
                crate::leanh::lean_inc_ref(v_descr_912_);
                crate::leanh::lean_inc_n(v_name_907_, 2);
                v___x_915_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_915_, 0, v_name_907_);
                crate::leanh::lean_ctor_set(v___x_915_, 1, v_ref_909_);
                crate::leanh::lean_ctor_set(v___x_915_, 2, v___x_914_);
                crate::leanh::lean_ctor_set(v___x_915_, 3, v_descr_912_);
                crate::leanh::lean_ctor_set(v___x_915_, 4, v_deprecation_x3f_913_);
                v___x_916_ = lean_register_option(v_name_907_, v___x_915_);
                if crate::leanh::lean_obj_tag(v___x_916_) == 0 {
                    v_isSharedCheck_924_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                    if v_isSharedCheck_924_ == 0 {
                        v_unused_925_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                        crate::leanh::lean_dec(v_unused_925_);
                        v___x_918_ = v___x_916_;
                        v_isShared_919_ = v_isSharedCheck_924_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_916_);
                        v___x_918_ = crate::leanh::lean_box(0);
                        v_isShared_919_ = v_isSharedCheck_924_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_907_);
                    v_a_926_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                    v_isSharedCheck_933_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_928_ = v___x_916_;
                        v_isShared_929_ = v_isSharedCheck_933_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_926_);
                        crate::leanh::lean_dec(v___x_916_);
                        v___x_928_ = crate::leanh::lean_box(0);
                        v_isShared_929_ = v_isSharedCheck_933_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_911_);
                v___x_920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_920_, 0, v_name_907_);
                crate::leanh::lean_ctor_set(v___x_920_, 1, v_defValue_911_);
                if v_isShared_919_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_920_);
                    v___x_922_ = v___x_918_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
                    v___x_922_ = v_reuseFailAlloc_923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_922_;
            }
            3 => {
                if v_isShared_929_ == 0 {
                    v___x_931_ = v___x_928_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_934_: *mut crate::leanh::LeanObject,
    mut v_decl_935_: *mut crate::leanh::LeanObject,
    mut v_ref_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v_name_934_, v_decl_935_, v_ref_936_);
    crate::leanh::lean_dec_ref(v_decl_935_);
    return v_res_938_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
    v___x_957_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
    v___x_958_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
    v___x_959_ = l_Lean_Option_register___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(v___x_956_, v___x_957_, v___x_958_);
    return v___x_959_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(
    mut v_a_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_961_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
    return v_res_961_;
}
pub unsafe fn _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
    v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
    return v___x_964_;
}
pub unsafe fn _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
    v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
    return v___x_967_;
}
pub unsafe fn _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
    v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
    return v___x_970_;
}
pub unsafe fn _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
    v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
    return v___x_973_;
}
pub unsafe fn _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7);
    v___x_975_ = l_Lean_MessageData_note(v___x_974_);
    return v___x_975_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(
    mut v___x_976_: *mut crate::leanh::LeanObject,
    mut v_n_977_: *mut crate::leanh::LeanObject,
    mut v_inst_978_: *mut crate::leanh::LeanObject,
    mut v_inst_979_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_980_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_max_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    v___x_982_ = l_Lean_Elab_Level_maxUniverseOffset;
    v_max_983_ = l_Lean_Option_get___redArg(v___x_976_, v_____do__lift_981_, v___x_982_);
    v___x_984_ = lean_nat_dec_le(v_n_977_, v_max_983_);
    if v___x_984_ == 0 {
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_980_);
        v___x_985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
        v___x_986_ = l_Nat_reprFast(v_n_977_);
        v___x_987_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
        v___x_988_ = l_Lean_MessageData_ofFormat(v___x_987_);
        v___x_989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_985_);
        crate::leanh::lean_ctor_set(v___x_989_, 1, v___x_988_);
        v___x_990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
        v___x_991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_989_);
        crate::leanh::lean_ctor_set(v___x_991_, 1, v___x_990_);
        v___x_992_ = l_Nat_reprFast(v_max_983_);
        v___x_993_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_993_, 0, v___x_992_);
        v___x_994_ = l_Lean_MessageData_ofFormat(v___x_993_);
        v___x_995_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_991_);
        crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
        v___x_996_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
        v___x_997_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_997_, 0, v___x_995_);
        crate::leanh::lean_ctor_set(v___x_997_, 1, v___x_996_);
        v___x_998_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
        v___x_999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_997_);
        crate::leanh::lean_ctor_set(v___x_999_, 1, v___x_998_);
        v___x_1000_ = l_Lean_throwError___redArg(v_inst_978_, v_inst_979_, v___x_999_);
        return v___x_1000_;
    } else {
        let mut v_toPure_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_max_983_);
        crate::leanh::lean_dec_ref(v_inst_979_);
        crate::leanh::lean_dec_ref(v_inst_978_);
        crate::leanh::lean_dec(v_n_977_);
        v_toPure_1001_ = crate::leanh::lean_ctor_get(v_toApplicative_980_, 1);
        crate::leanh::lean_inc(v_toPure_1001_);
        crate::leanh::lean_dec_ref(v_toApplicative_980_);
        v___x_1002_ = crate::leanh::lean_box(0);
        v___x_1003_ =
            crate::leanh::lean_apply_2(v_toPure_1001_, crate::leanh::lean_box(0), v___x_1002_);
        return v___x_1003_;
    }
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(
    mut v___x_1004_: *mut crate::leanh::LeanObject,
    mut v_n_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_inst_1007_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1008_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ =
        l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(
            v___x_1004_,
            v_n_1005_,
            v_inst_1006_,
            v_inst_1007_,
            v_toApplicative_1008_,
            v_____do__lift_1009_,
        );
    crate::leanh::lean_dec_ref(v_____do__lift_1009_);
    return v_res_1010_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(
    mut v_inst_1011_: *mut crate::leanh::LeanObject,
    mut v_inst_1012_: *mut crate::leanh::LeanObject,
    mut v_inst_1013_: *mut crate::leanh::LeanObject,
    mut v_n_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = l_Lean_KVMap_instValueNat;
    v_toApplicative_1016_ = crate::leanh::lean_ctor_get(v_inst_1011_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1016_);
    v_toBind_1017_ = crate::leanh::lean_ctor_get(v_inst_1011_, 1);
    crate::leanh::lean_inc(v_toBind_1017_);
    v___f_1018_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1018_, 0, v___x_1015_);
    crate::leanh::lean_closure_set(v___f_1018_, 1, v_n_1014_);
    crate::leanh::lean_closure_set(v___f_1018_, 2, v_inst_1011_);
    crate::leanh::lean_closure_set(v___f_1018_, 3, v_inst_1012_);
    crate::leanh::lean_closure_set(v___f_1018_, 4, v_toApplicative_1016_);
    v___x_1019_ = crate::leanh::lean_apply_4(
        v_toBind_1017_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1013_,
        v___f_1018_,
    );
    return v___x_1019_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(
    mut v_m_1020_: *mut crate::leanh::LeanObject,
    mut v_inst_1021_: *mut crate::leanh::LeanObject,
    mut v_inst_1022_: *mut crate::leanh::LeanObject,
    mut v_inst_1023_: *mut crate::leanh::LeanObject,
    mut v_n_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(
        v_inst_1021_,
        v_inst_1022_,
        v_inst_1023_,
        v_n_1024_,
    );
    return v___x_1025_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
    mut v_msg_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1029_ = crate::leanh::lean_ctor_get(v___y_1027_, 1);
    crate::leanh::lean_inc(v_ref_1029_);
    v___x_1030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1030_, 0, v_ref_1029_);
    crate::leanh::lean_ctor_set(v___x_1030_, 1, v_msg_1026_);
    v___x_1031_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
    crate::leanh::lean_ctor_set(v___x_1031_, 1, v___y_1028_);
    return v___x_1031_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(
    mut v_msg_1032_: *mut crate::leanh::LeanObject,
    mut v___y_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
        v_msg_1032_,
        v___y_1033_,
        v___y_1034_,
    );
    crate::leanh::lean_dec_ref(v___y_1033_);
    return v_res_1035_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(
    mut v_00_u03b1_1036_: *mut crate::leanh::LeanObject,
    mut v_msg_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
        v_msg_1037_,
        v___y_1038_,
        v___y_1039_,
    );
    return v___x_1040_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(
    mut v_00_u03b1_1041_: *mut crate::leanh::LeanObject,
    mut v_msg_1042_: *mut crate::leanh::LeanObject,
    mut v___y_1043_: *mut crate::leanh::LeanObject,
    mut v___y_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(
        v_00_u03b1_1041_,
        v_msg_1042_,
        v___y_1043_,
        v___y_1044_,
    );
    crate::leanh::lean_dec_ref(v___y_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(
    mut v_opts_1046_: *mut crate::leanh::LeanObject,
    mut v_opt_1047_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1048_ = crate::leanh::lean_ctor_get(v_opt_1047_, 0);
    v_defValue_1049_ = crate::leanh::lean_ctor_get(v_opt_1047_, 1);
    v_map_1050_ = crate::leanh::lean_ctor_get(v_opts_1046_, 0);
    v___x_1051_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1050_,
            v_name_1048_,
        );
    if crate::leanh::lean_obj_tag(v___x_1051_) == 0 {
        let mut v___x_1052_: u8 = 0;
        v___x_1052_ = (crate::leanh::lean_unbox(v_defValue_1049_) as u8);
        return v___x_1052_;
    } else {
        let mut v_val_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1053_ = crate::leanh::lean_ctor_get(v___x_1051_, 0);
        crate::leanh::lean_inc(v_val_1053_);
        crate::leanh::lean_dec_ref_known(v___x_1051_, 1);
        if crate::leanh::lean_obj_tag(v_val_1053_) == 1 {
            let mut v_v_1054_: u8 = 0;
            v_v_1054_ = crate::leanh::lean_ctor_get_uint8(v_val_1053_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1053_, 0);
            return v_v_1054_;
        } else {
            let mut v___x_1055_: u8 = 0;
            crate::leanh::lean_dec(v_val_1053_);
            v___x_1055_ = (crate::leanh::lean_unbox(v_defValue_1049_) as u8);
            return v___x_1055_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(
    mut v_opts_1056_: *mut crate::leanh::LeanObject,
    mut v_opt_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1058_: u8 = 0;
    let mut v_r_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1058_ =
        l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_opts_1056_, v_opt_1057_);
    crate::leanh::lean_dec_ref(v_opt_1057_);
    crate::leanh::lean_dec_ref(v_opts_1056_);
    v_r_1059_ = crate::leanh::lean_box((v_res_1058_) as usize);
    return v_r_1059_;
}
pub unsafe fn _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
    v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1065_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1_once), _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
    v___x_1066_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
        v___x_1065_,
        v___y_1063_,
        v___y_1064_,
    );
    return v___x_1066_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(
    mut v___y_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1069_ =
        l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(
            v___y_1067_,
            v___y_1068_,
        );
    crate::leanh::lean_dec_ref(v___y_1067_);
    return v_res_1069_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_x_1071_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1072_: u8 = 0;
    let mut v_head_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1071_) == 0 {
                    v___x_1072_ = 0;
                    return v___x_1072_;
                } else {
                    v_head_1073_ = crate::leanh::lean_ctor_get(v_x_1071_, 0);
                    v_tail_1074_ = crate::leanh::lean_ctor_get(v_x_1071_, 1);
                    v___x_1075_ = lean_name_eq(v_a_1070_, v_head_1073_);
                    if v___x_1075_ == 0 {
                        v_x_1071_ = v_tail_1074_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1075_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3___boxed(
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_x_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1079_: u8 = 0;
    let mut v_r_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1079_ = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(v_a_1077_, v_x_1078_);
    crate::leanh::lean_dec(v_x_1078_);
    crate::leanh::lean_dec(v_a_1077_);
    v_r_1080_ = crate::leanh::lean_box((v_res_1079_) as usize);
    return v_r_1080_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(
    mut v_opts_1081_: *mut crate::leanh::LeanObject,
    mut v_opt_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1083_ = crate::leanh::lean_ctor_get(v_opt_1082_, 0);
    v_defValue_1084_ = crate::leanh::lean_ctor_get(v_opt_1082_, 1);
    v_map_1085_ = crate::leanh::lean_ctor_get(v_opts_1081_, 0);
    v___x_1086_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1085_,
            v_name_1083_,
        );
    if crate::leanh::lean_obj_tag(v___x_1086_) == 0 {
        crate::leanh::lean_inc(v_defValue_1084_);
        return v_defValue_1084_;
    } else {
        let mut v_val_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1087_ = crate::leanh::lean_ctor_get(v___x_1086_, 0);
        crate::leanh::lean_inc(v_val_1087_);
        crate::leanh::lean_dec_ref_known(v___x_1086_, 1);
        if crate::leanh::lean_obj_tag(v_val_1087_) == 3 {
            let mut v_v_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1088_ = crate::leanh::lean_ctor_get(v_val_1087_, 0);
            crate::leanh::lean_inc(v_v_1088_);
            crate::leanh::lean_dec_ref_known(v_val_1087_, 1);
            return v_v_1088_;
        } else {
            crate::leanh::lean_dec(v_val_1087_);
            crate::leanh::lean_inc(v_defValue_1084_);
            return v_defValue_1084_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(
    mut v_opts_1089_: *mut crate::leanh::LeanObject,
    mut v_opt_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_opts_1089_, v_opt_1090_);
    crate::leanh::lean_dec_ref(v_opt_1090_);
    crate::leanh::lean_dec_ref(v_opts_1089_);
    return v_res_1091_;
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(
    mut v_n_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_max_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    v_options_1095_ = crate::leanh::lean_ctor_get(v___y_1093_, 0);
    v___x_1096_ = l_Lean_Elab_Level_maxUniverseOffset;
    v_max_1097_ = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(v_options_1095_, v___x_1096_);
    v___x_1098_ = lean_nat_dec_le(v_n_1092_, v_max_1097_);
    if v___x_1098_ == 0 {
        let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1099_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
        v___x_1100_ = l_Nat_reprFast(v_n_1092_);
        v___x_1101_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1101_, 0, v___x_1100_);
        v___x_1102_ = l_Lean_MessageData_ofFormat(v___x_1101_);
        v___x_1103_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1103_, 0, v___x_1099_);
        crate::leanh::lean_ctor_set(v___x_1103_, 1, v___x_1102_);
        v___x_1104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
        v___x_1105_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1103_);
        crate::leanh::lean_ctor_set(v___x_1105_, 1, v___x_1104_);
        v___x_1106_ = l_Nat_reprFast(v_max_1097_);
        v___x_1107_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1106_);
        v___x_1108_ = l_Lean_MessageData_ofFormat(v___x_1107_);
        v___x_1109_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1105_);
        crate::leanh::lean_ctor_set(v___x_1109_, 1, v___x_1108_);
        v___x_1110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
        v___x_1111_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1111_, 0, v___x_1109_);
        crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1110_);
        v___x_1112_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
        v___x_1113_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1111_);
        crate::leanh::lean_ctor_set(v___x_1113_, 1, v___x_1112_);
        v___x_1114_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
            v___x_1113_,
            v___y_1093_,
            v___y_1094_,
        );
        return v___x_1114_;
    } else {
        let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_max_1097_);
        crate::leanh::lean_dec(v_n_1092_);
        v___x_1115_ = crate::leanh::lean_box(0);
        v___x_1116_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
        crate::leanh::lean_ctor_set(v___x_1116_, 1, v___y_1094_);
        return v___x_1116_;
    }
}
pub unsafe fn l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(
    mut v_n_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_n_1117_, v___y_1118_, v___y_1119_);
    crate::leanh::lean_dec_ref(v___y_1118_);
    return v_res_1120_;
}
pub unsafe fn _init_l_Lean_Elab_Level_elabLevel___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Lean_Elab_Level_elabLevel___closed__15;
    v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
    return v___x_1160_;
}
pub unsafe fn _init_l_Lean_Elab_Level_elabLevel___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_Lean_Elab_Level_elabLevel___closed__17;
    v___x_1163_ = l_Lean_stringToMessageData(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(
    mut v_as_1164_: *mut crate::leanh::LeanObject,
    mut v_i_1165_: usize,
    mut v_stop_1166_: usize,
    mut v_b_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1170_ = lean_usize_dec_eq(v_i_1165_, v_stop_1166_);
                if v___x_1170_ == 0 {
                    v___x_1171_ = 1usize;
                    v___x_1172_ = lean_usize_sub(v_i_1165_, v___x_1171_);
                    v___x_1173_ = lean_array_uget_borrowed(v_as_1164_, v___x_1172_);
                    crate::leanh::lean_inc_ref(v___y_1168_);
                    crate::leanh::lean_inc(v___x_1173_);
                    v___x_1174_ =
                        l_Lean_Elab_Level_elabLevel(v___x_1173_, v___y_1168_, v___y_1169_);
                    if crate::leanh::lean_obj_tag(v___x_1174_) == 0 {
                        v_a_1175_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                        crate::leanh::lean_inc(v_a_1175_);
                        v_a_1176_ = crate::leanh::lean_ctor_get(v___x_1174_, 1);
                        crate::leanh::lean_inc(v_a_1176_);
                        crate::leanh::lean_dec_ref_known(v___x_1174_, 2);
                        v___x_1177_ = l_Lean_mkLevelMax_x27(v_a_1175_, v_b_1167_);
                        v_i_1165_ = v___x_1172_;
                        v_b_1167_ = v___x_1177_;
                        v___y_1169_ = v_a_1176_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_1167_);
                        if crate::leanh::lean_obj_tag(v___x_1174_) == 0 {
                            v_a_1179_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                            crate::leanh::lean_inc(v_a_1179_);
                            v_a_1180_ = crate::leanh::lean_ctor_get(v___x_1174_, 1);
                            crate::leanh::lean_inc(v_a_1180_);
                            crate::leanh::lean_dec_ref_known(v___x_1174_, 2);
                            v_i_1165_ = v___x_1172_;
                            v_b_1167_ = v_a_1179_;
                            v___y_1169_ = v_a_1180_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1174_;
                        }
                    }
                } else {
                    v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1182_, 0, v_b_1167_);
                    crate::leanh::lean_ctor_set(v___x_1182_, 1, v___y_1169_);
                    return v___x_1182_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Level_elabLevel(
    mut v_stx_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicit_1188_: u8 = 0;
    let mut v_kind_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v_ref_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut v_unused_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_ngen_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramName_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut v_unused_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v_unused_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: usize = 0;
    let mut v___x_1322_: usize = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: usize = 0;
    let mut v___x_1326_: usize = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: u8 = 0;
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: usize = 0;
    let mut v___x_1347_: usize = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: usize = 0;
    let mut v___x_1351_: usize = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1186_ = crate::leanh::lean_ctor_get(v_a_1184_, 0);
                crate::leanh::lean_inc_ref_n(v_options_1186_, 2);
                v_ref_1187_ = crate::leanh::lean_ctor_get(v_a_1184_, 1);
                crate::leanh::lean_inc(v_ref_1187_);
                v_autoBoundImplicit_1188_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1184_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec_ref(v_a_1184_);
                crate::leanh::lean_inc(v_stx_1183_);
                v_kind_1189_ = l_Lean_Syntax_getKind(v_stx_1183_);
                v___x_1190_ = l_Lean_Elab_Level_elabLevel___closed__2;
                v___x_1191_ = lean_name_eq(v_kind_1189_, v___x_1190_);
                v_ref_1192_ = l_Lean_replaceRef(v_stx_1183_, v_ref_1187_);
                crate::leanh::lean_dec(v_ref_1187_);
                v___x_1193_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1193_, 0, v_options_1186_);
                crate::leanh::lean_ctor_set(v___x_1193_, 1, v_ref_1192_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1193_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_autoBoundImplicit_1188_,
                );
                if v___x_1191_ == 0 {
                    v___x_1194_ = l_Lean_Elab_Level_elabLevel___closed__4;
                    v___x_1195_ = lean_name_eq(v_kind_1189_, v___x_1194_);
                    if v___x_1195_ == 0 {
                        v___x_1196_ = l_Lean_Elab_Level_elabLevel___closed__6;
                        v___x_1197_ = lean_name_eq(v_kind_1189_, v___x_1196_);
                        if v___x_1197_ == 0 {
                            v___x_1198_ = l_Lean_Elab_Level_elabLevel___closed__8;
                            v___x_1199_ = lean_name_eq(v_kind_1189_, v___x_1198_);
                            if v___x_1199_ == 0 {
                                v___x_1200_ = l_Lean_Elab_Level_elabLevel___closed__10;
                                v___x_1201_ = lean_name_eq(v_kind_1189_, v___x_1200_);
                                if v___x_1201_ == 0 {
                                    v___x_1202_ = l_Lean_Elab_Level_elabLevel___closed__12;
                                    v___x_1203_ = lean_name_eq(v_kind_1189_, v___x_1202_);
                                    if v___x_1203_ == 0 {
                                        crate::leanh::lean_dec_ref(v_options_1186_);
                                        v___x_1204_ = l_Lean_Elab_Level_elabLevel___closed__14;
                                        v___x_1205_ = lean_name_eq(v_kind_1189_, v___x_1204_);
                                        crate::leanh::lean_dec(v_kind_1189_);
                                        if v___x_1205_ == 0 {
                                            crate::leanh::lean_dec(v_stx_1183_);
                                            v___x_1206_ = crate::leanh::lean_obj_once(
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Elab_Level_elabLevel___closed__16
                                                ),
                                                core::ptr::addr_of_mut!(
                                                    l_Lean_Elab_Level_elabLevel___closed__16_once
                                                ),
                                                _init_l_Lean_Elab_Level_elabLevel___closed__16,
                                            );
                                            v___x_1207_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(v___x_1206_, v___x_1193_, v_a_1185_);
                                            crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                            return v___x_1207_;
                                        } else {
                                            v___x_1208_ = crate::leanh::lean_unsigned_to_nat(0);
                                            v___x_1209_ =
                                                l_Lean_Syntax_getArg(v_stx_1183_, v___x_1208_);
                                            crate::leanh::lean_inc_ref(v___x_1193_);
                                            v___x_1210_ = l_Lean_Elab_Level_elabLevel(
                                                v___x_1209_,
                                                v___x_1193_,
                                                v_a_1185_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_1210_) == 0 {
                                                v_a_1211_ =
                                                    crate::leanh::lean_ctor_get(v___x_1210_, 0);
                                                crate::leanh::lean_inc(v_a_1211_);
                                                v_a_1212_ =
                                                    crate::leanh::lean_ctor_get(v___x_1210_, 1);
                                                crate::leanh::lean_inc(v_a_1212_);
                                                crate::leanh::lean_dec_ref_known(v___x_1210_, 2);
                                                v___x_1213_ = crate::leanh::lean_unsigned_to_nat(2);
                                                v___x_1214_ =
                                                    l_Lean_Syntax_getArg(v_stx_1183_, v___x_1213_);
                                                crate::leanh::lean_dec(v_stx_1183_);
                                                v___x_1215_ =
                                                    l_Lean_Syntax_isNatLit_x3f(v___x_1214_);
                                                crate::leanh::lean_dec(v___x_1214_);
                                                if crate::leanh::lean_obj_tag(v___x_1215_) == 0 {
                                                    crate::leanh::lean_dec(v_a_1211_);
                                                    v___x_1216_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_1193_, v_a_1212_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1193_,
                                                        2,
                                                    );
                                                    return v___x_1216_;
                                                } else {
                                                    v_val_1217_ =
                                                        crate::leanh::lean_ctor_get(v___x_1215_, 0);
                                                    crate::leanh::lean_inc_n(v_val_1217_, 2);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1215_,
                                                        1,
                                                    );
                                                    v___x_1218_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_1217_, v___x_1193_, v_a_1212_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1193_,
                                                        2,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_1218_) == 0
                                                    {
                                                        v_a_1219_ = crate::leanh::lean_ctor_get(
                                                            v___x_1218_,
                                                            1,
                                                        );
                                                        v_isSharedCheck_1227_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1218_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1227_ == 0 {
                                                            v_unused_1228_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_1218_,
                                                                    0,
                                                                );
                                                            crate::leanh::lean_dec(v_unused_1228_);
                                                            v___x_1221_ = v___x_1218_;
                                                            v_isShared_1222_ =
                                                                v_isSharedCheck_1227_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1219_);
                                                            crate::leanh::lean_dec(v___x_1218_);
                                                            v___x_1221_ = crate::leanh::lean_box(0);
                                                            v_isShared_1222_ =
                                                                v_isSharedCheck_1227_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_val_1217_);
                                                        crate::leanh::lean_dec(v_a_1211_);
                                                        v_a_1229_ = crate::leanh::lean_ctor_get(
                                                            v___x_1218_,
                                                            0,
                                                        );
                                                        v_a_1230_ = crate::leanh::lean_ctor_get(
                                                            v___x_1218_,
                                                            1,
                                                        );
                                                        v_isSharedCheck_1237_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1218_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1237_ == 0 {
                                                            v___x_1232_ = v___x_1218_;
                                                            v_isShared_1233_ =
                                                                v_isSharedCheck_1237_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1230_);
                                                            crate::leanh::lean_inc(v_a_1229_);
                                                            crate::leanh::lean_dec(v___x_1218_);
                                                            v___x_1232_ = crate::leanh::lean_box(0);
                                                            v_isShared_1233_ =
                                                                v_isSharedCheck_1237_;
                                                            state = 3;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                                crate::leanh::lean_dec(v_stx_1183_);
                                                return v___x_1210_;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_kind_1189_);
                                        v_ngen_1238_ = crate::leanh::lean_ctor_get(v_a_1185_, 0);
                                        v_mctx_1239_ = crate::leanh::lean_ctor_get(v_a_1185_, 1);
                                        v_levelNames_1240_ =
                                            crate::leanh::lean_ctor_get(v_a_1185_, 2);
                                        v_paramName_1241_ = l_Lean_Syntax_getId(v_stx_1183_);
                                        crate::leanh::lean_dec(v_stx_1183_);
                                        v___x_1264_ =
                                            l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__3(
                                                v_paramName_1241_,
                                                v_levelNames_1240_,
                                            );
                                        if v___x_1264_ == 0 {
                                            if v_autoBoundImplicit_1188_ == 0 {
                                                crate::leanh::lean_dec_ref(v_options_1186_);
                                                state = 6;
                                                continue;
                                            } else {
                                                v___x_1265_ = l_Lean_Elab_relaxedAutoImplicit;
                                                v___x_1266_ = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__4(v_options_1186_, v___x_1265_);
                                                crate::leanh::lean_dec_ref(v_options_1186_);
                                                crate::leanh::lean_inc(v_paramName_1241_);
                                                v___x_1267_ = l_Lean_Elab_isValidAutoBoundLevelName(
                                                    v_paramName_1241_,
                                                    v___x_1266_,
                                                );
                                                if v___x_1267_ == 0 {
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_levelNames_1240_);
                                                    crate::leanh::lean_inc_ref(v_mctx_1239_);
                                                    crate::leanh::lean_inc_ref(v_ngen_1238_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1193_,
                                                        2,
                                                    );
                                                    v_isSharedCheck_1275_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v_a_1185_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1275_ == 0 {
                                                        v_unused_1276_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_1185_, 2,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_1276_);
                                                        v_unused_1277_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_1185_, 1,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_1277_);
                                                        v_unused_1278_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_1185_, 0,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_1278_);
                                                        v___x_1269_ = v_a_1185_;
                                                        v_isShared_1270_ = v_isSharedCheck_1275_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1185_);
                                                        v___x_1269_ = crate::leanh::lean_box(0);
                                                        v_isShared_1270_ = v_isSharedCheck_1275_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                            crate::leanh::lean_dec_ref(v_options_1186_);
                                            v___y_1243_ = v_a_1185_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_kind_1189_);
                                    crate::leanh::lean_dec_ref(v_options_1186_);
                                    v___x_1279_ = l_Lean_Syntax_isNatLit_x3f(v_stx_1183_);
                                    crate::leanh::lean_dec(v_stx_1183_);
                                    if crate::leanh::lean_obj_tag(v___x_1279_) == 0 {
                                        v___x_1280_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(v___x_1193_, v_a_1185_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        return v___x_1280_;
                                    } else {
                                        v_val_1281_ = crate::leanh::lean_ctor_get(v___x_1279_, 0);
                                        crate::leanh::lean_inc_n(v_val_1281_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_1279_, 1);
                                        v___x_1282_ = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(v_val_1281_, v___x_1193_, v_a_1185_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        if crate::leanh::lean_obj_tag(v___x_1282_) == 0 {
                                            v_a_1283_ = crate::leanh::lean_ctor_get(v___x_1282_, 1);
                                            v_isSharedCheck_1291_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1282_))
                                                    as u8;
                                            if v_isSharedCheck_1291_ == 0 {
                                                v_unused_1292_ =
                                                    crate::leanh::lean_ctor_get(v___x_1282_, 0);
                                                crate::leanh::lean_dec(v_unused_1292_);
                                                v___x_1285_ = v___x_1282_;
                                                v_isShared_1286_ = v_isSharedCheck_1291_;
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1283_);
                                                crate::leanh::lean_dec(v___x_1282_);
                                                v___x_1285_ = crate::leanh::lean_box(0);
                                                v_isShared_1286_ = v_isSharedCheck_1291_;
                                                state = 11;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_val_1281_);
                                            v_a_1293_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                                            v_a_1294_ = crate::leanh::lean_ctor_get(v___x_1282_, 1);
                                            v_isSharedCheck_1301_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1282_))
                                                    as u8;
                                            if v_isSharedCheck_1301_ == 0 {
                                                v___x_1296_ = v___x_1282_;
                                                v_isShared_1297_ = v_isSharedCheck_1301_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1294_);
                                                crate::leanh::lean_inc(v_a_1293_);
                                                crate::leanh::lean_dec(v___x_1282_);
                                                v___x_1296_ = crate::leanh::lean_box(0);
                                                v_isShared_1297_ = v_isSharedCheck_1301_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_kind_1189_);
                                crate::leanh::lean_dec_ref(v_options_1186_);
                                crate::leanh::lean_dec(v_stx_1183_);
                                v___x_1302_ =
                                    l_Lean_Elab_Level_mkFreshLevelMVar(v___x_1193_, v_a_1185_);
                                crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                return v___x_1302_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_kind_1189_);
                            crate::leanh::lean_dec_ref(v_options_1186_);
                            v___x_1303_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1304_ = l_Lean_Syntax_getArg(v_stx_1183_, v___x_1303_);
                            crate::leanh::lean_dec(v_stx_1183_);
                            v_args_1305_ = l_Lean_Syntax_getArgs(v___x_1304_);
                            crate::leanh::lean_dec(v___x_1304_);
                            v___x_1306_ = crate::leanh::lean_box(0);
                            v___x_1307_ = lean_array_get_size(v_args_1305_);
                            v___x_1308_ = lean_nat_sub(v___x_1307_, v___x_1303_);
                            v___x_1309_ = lean_array_get(v___x_1306_, v_args_1305_, v___x_1308_);
                            crate::leanh::lean_inc_ref(v___x_1193_);
                            v___x_1310_ =
                                l_Lean_Elab_Level_elabLevel(v___x_1309_, v___x_1193_, v_a_1185_);
                            if crate::leanh::lean_obj_tag(v___x_1310_) == 0 {
                                v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                                crate::leanh::lean_inc(v_a_1311_);
                                v_a_1312_ = crate::leanh::lean_ctor_get(v___x_1310_, 1);
                                crate::leanh::lean_inc(v_a_1312_);
                                v___x_1313_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_1314_ = l_Array_toSubarray___redArg(
                                    v_args_1305_,
                                    v___x_1313_,
                                    v___x_1308_,
                                );
                                v_array_1315_ = crate::leanh::lean_ctor_get(v___x_1314_, 0);
                                crate::leanh::lean_inc_ref(v_array_1315_);
                                v_start_1316_ = crate::leanh::lean_ctor_get(v___x_1314_, 1);
                                crate::leanh::lean_inc(v_start_1316_);
                                v_stop_1317_ = crate::leanh::lean_ctor_get(v___x_1314_, 2);
                                crate::leanh::lean_inc(v_stop_1317_);
                                crate::leanh::lean_dec_ref(v___x_1314_);
                                v___x_1318_ = lean_array_get_size(v_array_1315_);
                                v___x_1319_ = lean_nat_dec_le(v_stop_1317_, v___x_1318_);
                                if v___x_1319_ == 0 {
                                    crate::leanh::lean_dec(v_stop_1317_);
                                    v___x_1320_ = lean_nat_dec_lt(v_start_1316_, v___x_1318_);
                                    if v___x_1320_ == 0 {
                                        crate::leanh::lean_dec(v_start_1316_);
                                        crate::leanh::lean_dec_ref(v_array_1315_);
                                        crate::leanh::lean_dec(v_a_1312_);
                                        crate::leanh::lean_dec(v_a_1311_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        return v___x_1310_;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_1310_, 2);
                                        v___x_1321_ = lean_usize_of_nat(v___x_1318_);
                                        v___x_1322_ = lean_usize_of_nat(v_start_1316_);
                                        crate::leanh::lean_dec(v_start_1316_);
                                        v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_1315_, v___x_1321_, v___x_1322_, v_a_1311_, v___x_1193_, v_a_1312_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        crate::leanh::lean_dec_ref(v_array_1315_);
                                        return v___x_1323_;
                                    }
                                } else {
                                    v___x_1324_ = lean_nat_dec_lt(v_start_1316_, v_stop_1317_);
                                    if v___x_1324_ == 0 {
                                        crate::leanh::lean_dec(v_stop_1317_);
                                        crate::leanh::lean_dec(v_start_1316_);
                                        crate::leanh::lean_dec_ref(v_array_1315_);
                                        crate::leanh::lean_dec(v_a_1312_);
                                        crate::leanh::lean_dec(v_a_1311_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        return v___x_1310_;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_1310_, 2);
                                        v___x_1325_ = lean_usize_of_nat(v_stop_1317_);
                                        crate::leanh::lean_dec(v_stop_1317_);
                                        v___x_1326_ = lean_usize_of_nat(v_start_1316_);
                                        crate::leanh::lean_dec(v_start_1316_);
                                        v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_array_1315_, v___x_1325_, v___x_1326_, v_a_1311_, v___x_1193_, v_a_1312_);
                                        crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                        crate::leanh::lean_dec_ref(v_array_1315_);
                                        return v___x_1327_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1308_);
                                crate::leanh::lean_dec_ref(v_args_1305_);
                                crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                return v___x_1310_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_kind_1189_);
                        crate::leanh::lean_dec_ref(v_options_1186_);
                        v___x_1328_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1329_ = l_Lean_Syntax_getArg(v_stx_1183_, v___x_1328_);
                        crate::leanh::lean_dec(v_stx_1183_);
                        v_args_1330_ = l_Lean_Syntax_getArgs(v___x_1329_);
                        crate::leanh::lean_dec(v___x_1329_);
                        v___x_1331_ = crate::leanh::lean_box(0);
                        v___x_1332_ = lean_array_get_size(v_args_1330_);
                        v___x_1333_ = lean_nat_sub(v___x_1332_, v___x_1328_);
                        v___x_1334_ = lean_array_get(v___x_1331_, v_args_1330_, v___x_1333_);
                        crate::leanh::lean_inc_ref(v___x_1193_);
                        v___x_1335_ =
                            l_Lean_Elab_Level_elabLevel(v___x_1334_, v___x_1193_, v_a_1185_);
                        if crate::leanh::lean_obj_tag(v___x_1335_) == 0 {
                            v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                            crate::leanh::lean_inc(v_a_1336_);
                            v_a_1337_ = crate::leanh::lean_ctor_get(v___x_1335_, 1);
                            crate::leanh::lean_inc(v_a_1337_);
                            v___x_1338_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1339_ =
                                l_Array_toSubarray___redArg(v_args_1330_, v___x_1338_, v___x_1333_);
                            v_array_1340_ = crate::leanh::lean_ctor_get(v___x_1339_, 0);
                            crate::leanh::lean_inc_ref(v_array_1340_);
                            v_start_1341_ = crate::leanh::lean_ctor_get(v___x_1339_, 1);
                            crate::leanh::lean_inc(v_start_1341_);
                            v_stop_1342_ = crate::leanh::lean_ctor_get(v___x_1339_, 2);
                            crate::leanh::lean_inc(v_stop_1342_);
                            crate::leanh::lean_dec_ref(v___x_1339_);
                            v___x_1343_ = lean_array_get_size(v_array_1340_);
                            v___x_1344_ = lean_nat_dec_le(v_stop_1342_, v___x_1343_);
                            if v___x_1344_ == 0 {
                                crate::leanh::lean_dec(v_stop_1342_);
                                v___x_1345_ = lean_nat_dec_lt(v_start_1341_, v___x_1343_);
                                if v___x_1345_ == 0 {
                                    crate::leanh::lean_dec(v_start_1341_);
                                    crate::leanh::lean_dec_ref(v_array_1340_);
                                    crate::leanh::lean_dec(v_a_1337_);
                                    crate::leanh::lean_dec(v_a_1336_);
                                    crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                    return v___x_1335_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_1335_, 2);
                                    v___x_1346_ = lean_usize_of_nat(v___x_1343_);
                                    v___x_1347_ = lean_usize_of_nat(v_start_1341_);
                                    crate::leanh::lean_dec(v_start_1341_);
                                    v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_1340_, v___x_1346_, v___x_1347_, v_a_1336_, v___x_1193_, v_a_1337_);
                                    crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                    crate::leanh::lean_dec_ref(v_array_1340_);
                                    return v___x_1348_;
                                }
                            } else {
                                v___x_1349_ = lean_nat_dec_lt(v_start_1341_, v_stop_1342_);
                                if v___x_1349_ == 0 {
                                    crate::leanh::lean_dec(v_stop_1342_);
                                    crate::leanh::lean_dec(v_start_1341_);
                                    crate::leanh::lean_dec_ref(v_array_1340_);
                                    crate::leanh::lean_dec(v_a_1337_);
                                    crate::leanh::lean_dec(v_a_1336_);
                                    crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                    return v___x_1335_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_1335_, 2);
                                    v___x_1350_ = lean_usize_of_nat(v_stop_1342_);
                                    crate::leanh::lean_dec(v_stop_1342_);
                                    v___x_1351_ = lean_usize_of_nat(v_start_1341_);
                                    crate::leanh::lean_dec(v_start_1341_);
                                    v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_array_1340_, v___x_1350_, v___x_1351_, v_a_1336_, v___x_1193_, v_a_1337_);
                                    crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                                    crate::leanh::lean_dec_ref(v_array_1340_);
                                    return v___x_1352_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1333_);
                            crate::leanh::lean_dec_ref(v_args_1330_);
                            crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                            return v___x_1335_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_kind_1189_);
                    crate::leanh::lean_dec_ref(v_options_1186_);
                    v___x_1353_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1354_ = l_Lean_Syntax_getArg(v_stx_1183_, v___x_1353_);
                    crate::leanh::lean_dec(v_stx_1183_);
                    v_stx_1183_ = v___x_1354_;
                    v_a_1184_ = v___x_1193_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_1223_ = l_Lean_Level_addOffset(v_a_1211_, v_val_1217_);
                if v_isShared_1222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1221_, 0, v___x_1223_);
                    v___x_1225_ = v___x_1221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1219_);
                    v___x_1225_ = v_reuseFailAlloc_1226_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1225_;
            }
            3 => {
                if v_isShared_1233_ == 0 {
                    v___x_1235_ = v___x_1232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_a_1230_);
                    v___x_1235_ = v_reuseFailAlloc_1236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1235_;
            }
            5 => {
                v___x_1244_ = l_Lean_mkLevelParam(v_paramName_1241_);
                v___x_1245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1244_);
                crate::leanh::lean_ctor_set(v___x_1245_, 1, v___y_1243_);
                return v___x_1245_;
            }
            6 => {
                v___x_1247_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Level_elabLevel___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Level_elabLevel___closed__18_once),
                    _init_l_Lean_Elab_Level_elabLevel___closed__18,
                );
                crate::leanh::lean_inc(v_paramName_1241_);
                v___x_1248_ = lean_mk_syntax_ident(v_paramName_1241_);
                v___x_1249_ = l_Lean_MessageData_ofSyntax(v___x_1248_);
                v___x_1250_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1247_);
                crate::leanh::lean_ctor_set(v___x_1250_, 1, v___x_1249_);
                v___x_1251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5_once), _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
                v___x_1252_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1250_);
                crate::leanh::lean_ctor_set(v___x_1252_, 1, v___x_1251_);
                v___x_1253_ = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(
                    v___x_1252_,
                    v___x_1193_,
                    v_a_1185_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1193_, 2);
                if crate::leanh::lean_obj_tag(v___x_1253_) == 0 {
                    v_a_1254_ = crate::leanh::lean_ctor_get(v___x_1253_, 1);
                    crate::leanh::lean_inc(v_a_1254_);
                    crate::leanh::lean_dec_ref_known(v___x_1253_, 2);
                    v___y_1243_ = v_a_1254_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_paramName_1241_);
                    v_a_1255_ = crate::leanh::lean_ctor_get(v___x_1253_, 0);
                    v_a_1256_ = crate::leanh::lean_ctor_get(v___x_1253_, 1);
                    v_isSharedCheck_1263_ = (!crate::leanh::lean_is_exclusive(v___x_1253_)) as u8;
                    if v_isSharedCheck_1263_ == 0 {
                        v___x_1258_ = v___x_1253_;
                        v_isShared_1259_ = v_isSharedCheck_1263_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1256_);
                        crate::leanh::lean_inc(v_a_1255_);
                        crate::leanh::lean_dec(v___x_1253_);
                        v___x_1258_ = crate::leanh::lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1263_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1259_ == 0 {
                    v___x_1261_ = v___x_1258_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_a_1256_);
                    v___x_1261_ = v_reuseFailAlloc_1262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1261_;
            }
            9 => {
                crate::leanh::lean_inc(v_paramName_1241_);
                v___x_1271_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1271_, 0, v_paramName_1241_);
                crate::leanh::lean_ctor_set(v___x_1271_, 1, v_levelNames_1240_);
                if v_isShared_1270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1269_, 2, v___x_1271_);
                    v___x_1273_ = v___x_1269_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_ngen_1238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_mctx_1239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1243_ = v___x_1273_;
                state = 5;
                continue;
            }
            11 => {
                v___x_1287_ = l_Lean_Level_ofNat(v_val_1281_);
                crate::leanh::lean_dec(v_val_1281_);
                if v_isShared_1286_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1287_);
                    v___x_1289_ = v___x_1285_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1283_);
                    v___x_1289_ = v_reuseFailAlloc_1290_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1289_;
            }
            13 => {
                if v_isShared_1297_ == 0 {
                    v___x_1299_ = v___x_1296_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1300_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_a_1294_);
                    v___x_1299_ = v_reuseFailAlloc_1300_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(
    mut v_as_1356_: *mut crate::leanh::LeanObject,
    mut v_i_1357_: usize,
    mut v_stop_1358_: usize,
    mut v_b_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: usize = 0;
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = lean_usize_dec_eq(v_i_1357_, v_stop_1358_);
                if v___x_1362_ == 0 {
                    v___x_1363_ = 1usize;
                    v___x_1364_ = lean_usize_sub(v_i_1357_, v___x_1363_);
                    v___x_1365_ = lean_array_uget_borrowed(v_as_1356_, v___x_1364_);
                    crate::leanh::lean_inc_ref(v___y_1360_);
                    crate::leanh::lean_inc(v___x_1365_);
                    v___x_1366_ =
                        l_Lean_Elab_Level_elabLevel(v___x_1365_, v___y_1360_, v___y_1361_);
                    if crate::leanh::lean_obj_tag(v___x_1366_) == 0 {
                        v_a_1367_ = crate::leanh::lean_ctor_get(v___x_1366_, 0);
                        crate::leanh::lean_inc(v_a_1367_);
                        v_a_1368_ = crate::leanh::lean_ctor_get(v___x_1366_, 1);
                        crate::leanh::lean_inc(v_a_1368_);
                        crate::leanh::lean_dec_ref_known(v___x_1366_, 2);
                        v___x_1369_ = l_Lean_mkLevelIMax_x27(v_a_1367_, v_b_1359_);
                        v_i_1357_ = v___x_1364_;
                        v_b_1359_ = v___x_1369_;
                        v___y_1361_ = v_a_1368_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_1359_);
                        if crate::leanh::lean_obj_tag(v___x_1366_) == 0 {
                            v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1366_, 0);
                            crate::leanh::lean_inc(v_a_1371_);
                            v_a_1372_ = crate::leanh::lean_ctor_get(v___x_1366_, 1);
                            crate::leanh::lean_inc(v_a_1372_);
                            crate::leanh::lean_dec_ref_known(v___x_1366_, 2);
                            v_i_1357_ = v___x_1364_;
                            v_b_1359_ = v_a_1371_;
                            v___y_1361_ = v_a_1372_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1366_;
                        }
                    }
                } else {
                    v___x_1374_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1374_, 0, v_b_1359_);
                    crate::leanh::lean_ctor_set(v___x_1374_, 1, v___y_1361_);
                    return v___x_1374_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(
    mut v_as_1375_: *mut crate::leanh::LeanObject,
    mut v_i_1376_: *mut crate::leanh::LeanObject,
    mut v_stop_1377_: *mut crate::leanh::LeanObject,
    mut v_b_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1381_: usize = 0;
    let mut v_stop_boxed_1382_: usize = 0;
    let mut v_res_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1381_ = crate::leanh::lean_unbox_usize(v_i_1376_);
    crate::leanh::lean_dec(v_i_1376_);
    v_stop_boxed_1382_ = crate::leanh::lean_unbox_usize(v_stop_1377_);
    crate::leanh::lean_dec(v_stop_1377_);
    v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__5(v_as_1375_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1378_, v___y_1379_, v___y_1380_);
    crate::leanh::lean_dec_ref(v___y_1379_);
    crate::leanh::lean_dec_ref(v_as_1375_);
    return v_res_1383_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(
    mut v_as_1384_: *mut crate::leanh::LeanObject,
    mut v_i_1385_: *mut crate::leanh::LeanObject,
    mut v_stop_1386_: *mut crate::leanh::LeanObject,
    mut v_b_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1390_: usize = 0;
    let mut v_stop_boxed_1391_: usize = 0;
    let mut v_res_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1390_ = crate::leanh::lean_unbox_usize(v_i_1385_);
    crate::leanh::lean_dec(v_i_1385_);
    v_stop_boxed_1391_ = crate::leanh::lean_unbox_usize(v_stop_1386_);
    crate::leanh::lean_dec(v_stop_1386_);
    v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(v_as_1384_, v_i_boxed_1390_, v_stop_boxed_1391_, v_b_1387_, v___y_1388_, v___y_1389_);
    crate::leanh::lean_dec_ref(v___y_1388_);
    crate::leanh::lean_dec_ref(v_as_1384_);
    return v_res_1392_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(
    mut v_00_u03b1_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ =
        l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(
            v___y_1394_,
            v___y_1395_,
        );
    return v___x_1396_;
}
pub unsafe fn l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(
    mut v_00_u03b1_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(
        v_00_u03b1_1397_,
        v___y_1398_,
        v___y_1399_,
    );
    crate::leanh::lean_dec_ref(v___y_1398_);
    return v_res_1400_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_AutoBound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Level_0__Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Level_maxUniverseOffset = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_AutoBound(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Level(builtin);
}
