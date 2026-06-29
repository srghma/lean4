// Lean compiler output
// Module: Lean.Hygiene
// Imports: Lean.Data.Format
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Repr::l_Nat_toSuperscriptString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_mkIdentFrom, lean_name_append_after};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_num___override,
    l_Lean_firstFrontendMacroScope, l_ReaderT_bind___boxed, l_ReaderT_pure___boxed,
    l_ReaderT_read___boxed, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, l_Std_Format_getUnicode, runtime_initialize_Lean_Data_Format,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{lean_nat_add, lean_nat_dec_eq};
pub static l_Lean_Unhygienic_instMonadQuotation___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Unhygienic_instMonadQuotation___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Unhygienic_instMonadQuotation___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Unhygienic_instMonadQuotation___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Unhygienic_instMonadQuotation___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__4_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__5_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__6_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__7_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__8_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__9_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__10_value:
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
static mut l_Lean_Unhygienic_instMonadQuotation___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__12_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__13_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__14_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__15_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__16_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__17_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__18_value:
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
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__19_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__20_value:
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
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__21_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__22_value:
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
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__23_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__21_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__23_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__23_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__26_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__25_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__23_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__28_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        85, 110, 104, 121, 103, 105, 101, 110, 105, 99, 77, 97, 105, 110, 0,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__29_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__28_value)
            as *mut crate::leanh::LeanObject,
        5644479884357183868 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__30_value:
    crate::leanh::LeanClosureObject<5> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_pure___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__23_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__29_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Unhygienic_instMonadQuotation___closed__31_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__26_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__27_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__30_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Unhygienic_instMonadQuotation___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Unhygienic_instMonadQuotation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Unhygienic_instMonadQuotation___closed__31_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Unhygienic_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Unhygienic_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Unhygienic_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Unhygienic_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
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
        95, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 0,
    ],
};
static mut l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        2917153259425111314 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 156, 157, 0],
};
static mut l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 129, 187, 0],
};
static mut l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 97, 110, 105, 116, 105, 122, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6746591144584426489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7454035352779329427 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [97, 100, 100, 32, 115, 117, 102, 102, 105, 120, 32, 116, 111, 32, 115, 104, 97, 100, 111, 119, 101, 100, 47, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 119, 104, 101, 110, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 105, 110, 103, 0]};
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__3_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__5_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__0_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16537735520416696136 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__1_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12743890379625876334 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_pp_sanitizeNames: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__0(
    mut v_____do__lift_397_: *mut crate::leanh::LeanObject,
    mut v___y_398_: *mut crate::leanh::LeanObject,
    mut v___y_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_403_: u8 = 0;
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut v_unused_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_400_ = crate::leanh::lean_ctor_get(v_____do__lift_397_, 0);
                v_isSharedCheck_407_ =
                    (!crate::leanh::lean_is_exclusive(v_____do__lift_397_)) as u8;
                if v_isSharedCheck_407_ == 0 {
                    v_unused_408_ = crate::leanh::lean_ctor_get(v_____do__lift_397_, 1);
                    crate::leanh::lean_dec(v_unused_408_);
                    v___x_402_ = v_____do__lift_397_;
                    v_isShared_403_ = v_isSharedCheck_407_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_400_);
                    crate::leanh::lean_dec(v_____do__lift_397_);
                    v___x_402_ = crate::leanh::lean_box(0);
                    v_isShared_403_ = v_isSharedCheck_407_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_402_, 1, v___y_399_);
                    v___x_405_ = v___x_402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_406_, 0, v_ref_400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_406_, 1, v___y_399_);
                    v___x_405_ = v_reuseFailAlloc_406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__0___boxed(
    mut v_____do__lift_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_412_ =
        l_Lean_Unhygienic_instMonadQuotation___lam__0(v_____do__lift_409_, v___y_410_, v___y_411_);
    crate::leanh::lean_dec_ref(v___y_410_);
    return v_res_412_;
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__1(
    mut v_00_u03b1_413_: *mut crate::leanh::LeanObject,
    mut v_ref_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
    mut v___y_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_scope_418_ = crate::leanh::lean_ctor_get(v___y_416_, 1);
    crate::leanh::lean_inc(v_scope_418_);
    v___x_419_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_419_, 0, v_ref_414_);
    crate::leanh::lean_ctor_set(v___x_419_, 1, v_scope_418_);
    v___x_420_ = crate::leanh::lean_apply_2(v___y_415_, v___x_419_, v___y_417_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__1___boxed(
    mut v_00_u03b1_421_: *mut crate::leanh::LeanObject,
    mut v_ref_422_: *mut crate::leanh::LeanObject,
    mut v___y_423_: *mut crate::leanh::LeanObject,
    mut v___y_424_: *mut crate::leanh::LeanObject,
    mut v___y_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_426_ = l_Lean_Unhygienic_instMonadQuotation___lam__1(
        v_00_u03b1_421_,
        v_ref_422_,
        v___y_423_,
        v___y_424_,
        v___y_425_,
    );
    crate::leanh::lean_dec_ref(v___y_424_);
    return v_res_426_;
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__2(
    mut v_____do__lift_427_: *mut crate::leanh::LeanObject,
    mut v___y_428_: *mut crate::leanh::LeanObject,
    mut v___y_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_433_: u8 = 0;
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v_unused_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_scope_430_ = crate::leanh::lean_ctor_get(v_____do__lift_427_, 1);
                v_isSharedCheck_437_ =
                    (!crate::leanh::lean_is_exclusive(v_____do__lift_427_)) as u8;
                if v_isSharedCheck_437_ == 0 {
                    v_unused_438_ = crate::leanh::lean_ctor_get(v_____do__lift_427_, 0);
                    crate::leanh::lean_dec(v_unused_438_);
                    v___x_432_ = v_____do__lift_427_;
                    v_isShared_433_ = v_isSharedCheck_437_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_scope_430_);
                    crate::leanh::lean_dec(v_____do__lift_427_);
                    v___x_432_ = crate::leanh::lean_box(0);
                    v_isShared_433_ = v_isSharedCheck_437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_432_, 1, v___y_429_);
                    crate::leanh::lean_ctor_set(v___x_432_, 0, v_scope_430_);
                    v___x_435_ = v___x_432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_436_, 0, v_scope_430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_436_, 1, v___y_429_);
                    v___x_435_ = v_reuseFailAlloc_436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__2___boxed(
    mut v_____do__lift_439_: *mut crate::leanh::LeanObject,
    mut v___y_440_: *mut crate::leanh::LeanObject,
    mut v___y_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ =
        l_Lean_Unhygienic_instMonadQuotation___lam__2(v_____do__lift_439_, v___y_440_, v___y_441_);
    crate::leanh::lean_dec_ref(v___y_440_);
    return v_res_442_;
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__3(
    mut v_00_u03b1_443_: *mut crate::leanh::LeanObject,
    mut v_x_444_: *mut crate::leanh::LeanObject,
    mut v___y_445_: *mut crate::leanh::LeanObject,
    mut v___y_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_447_ = crate::leanh::lean_ctor_get(v___y_445_, 0);
    v___x_448_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_449_ = lean_nat_add(v___y_446_, v___x_448_);
    crate::leanh::lean_inc(v_ref_447_);
    v___x_450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_450_, 0, v_ref_447_);
    crate::leanh::lean_ctor_set(v___x_450_, 1, v___y_446_);
    v___x_451_ = crate::leanh::lean_apply_2(v_x_444_, v___x_450_, v___x_449_);
    return v___x_451_;
}
pub unsafe fn l_Lean_Unhygienic_instMonadQuotation___lam__3___boxed(
    mut v_00_u03b1_452_: *mut crate::leanh::LeanObject,
    mut v_x_453_: *mut crate::leanh::LeanObject,
    mut v___y_454_: *mut crate::leanh::LeanObject,
    mut v___y_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Lean_Unhygienic_instMonadQuotation___lam__3(
        v_00_u03b1_452_,
        v_x_453_,
        v___y_454_,
        v___y_455_,
    );
    crate::leanh::lean_dec_ref(v___y_454_);
    return v_res_456_;
}
pub unsafe fn _init_l_Lean_Unhygienic_run___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = l_Lean_firstFrontendMacroScope;
    v___x_532_ = crate::leanh::lean_box(0);
    v___x_533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_533_, 0, v___x_532_);
    crate::leanh::lean_ctor_set(v___x_533_, 1, v___x_531_);
    return v___x_533_;
}
pub unsafe fn _init_l_Lean_Unhygienic_run___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_535_ = l_Lean_firstFrontendMacroScope;
    v___x_536_ = lean_nat_add(v___x_535_, v___x_534_);
    return v___x_536_;
}
pub unsafe fn l_Lean_Unhygienic_run___redArg(
    mut v_x_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__0_once),
        _init_l_Lean_Unhygienic_run___redArg___closed__0,
    );
    v___x_539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__1_once),
        _init_l_Lean_Unhygienic_run___redArg___closed__1,
    );
    v___x_540_ = crate::leanh::lean_apply_2(v_x_537_, v___x_538_, v___x_539_);
    v_fst_541_ = crate::leanh::lean_ctor_get(v___x_540_, 0);
    crate::leanh::lean_inc(v_fst_541_);
    crate::leanh::lean_dec_ref(v___x_540_);
    return v_fst_541_;
}
pub unsafe fn l_Lean_Unhygienic_run(
    mut v_00_u03b1_542_: *mut crate::leanh::LeanObject,
    mut v_x_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__0_once),
        _init_l_Lean_Unhygienic_run___redArg___closed__0,
    );
    v___x_545_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Unhygienic_run___redArg___closed__1_once),
        _init_l_Lean_Unhygienic_run___redArg___closed__1,
    );
    v___x_546_ = crate::leanh::lean_apply_2(v_x_543_, v___x_544_, v___x_545_);
    v_fst_547_ = crate::leanh::lean_ctor_get(v___x_546_, 0);
    crate::leanh::lean_inc(v_fst_547_);
    crate::leanh::lean_dec_ref(v___x_546_);
    return v_fst_547_;
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(
    mut v_unicode_552_: u8,
    mut v_name_553_: *mut crate::leanh::LeanObject,
    mut v_idx_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_unicode_552_ == 0 {
        let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_555_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1;
        v___x_556_ = l_Lean_Name_num___override(v___x_555_, v_idx_554_);
        v___x_557_ = l_Lean_Name_append(v_name_553_, v___x_556_);
        return v___x_557_;
    } else {
        let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_559_: u8 = 0;
        v___x_558_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_559_ = lean_nat_dec_eq(v_idx_554_, v___x_558_);
        if v___x_559_ == 0 {
            let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_560_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
            v___x_561_ = l_Nat_toSuperscriptString(v_idx_554_);
            v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
            crate::leanh::lean_dec_ref(v___x_561_);
            v___x_563_ = lean_name_append_after(v_name_553_, v___x_562_);
            return v___x_563_;
        } else {
            let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_idx_554_);
            v___x_564_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
            v___x_565_ = lean_name_append_after(v_name_553_, v___x_564_);
            return v___x_565_;
        }
    }
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(
    mut v_unicode_566_: *mut crate::leanh::LeanObject,
    mut v_name_567_: *mut crate::leanh::LeanObject,
    mut v_idx_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_unicode_boxed_569_: u8 = 0;
    let mut v_res_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_unicode_boxed_569_ = (crate::leanh::lean_unbox(v_unicode_566_) as u8);
    v_res_570_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(
        v_unicode_boxed_569_,
        v_name_567_,
        v_idx_568_,
    );
    return v_res_570_;
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(
    mut v_unicode_572_: u8,
    mut v_x_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_573_) == 2 {
        let mut v_pre_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_574_ = crate::leanh::lean_ctor_get(v_x_573_, 0);
        crate::leanh::lean_inc(v_pre_574_);
        match crate::leanh::lean_obj_tag(v_pre_574_) {
            1 => {
                let mut v_i_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_i_575_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                crate::leanh::lean_inc(v_i_575_);
                crate::leanh::lean_dec_ref_known(v_x_573_, 2);
                v___x_576_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(
                    v_unicode_572_,
                    v_pre_574_,
                    v_i_575_,
                );
                return v___x_576_;
            }
            0 => {
                let mut v_i_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_i_577_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                crate::leanh::lean_inc(v_i_577_);
                crate::leanh::lean_dec_ref_known(v_x_573_, 2);
                v___x_578_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(
                    v_unicode_572_,
                    v_pre_574_,
                    v_i_577_,
                );
                return v___x_578_;
            }
            _ => {
                if v_unicode_572_ == 0 {
                    let mut v_i_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_i_579_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                    crate::leanh::lean_inc(v_i_579_);
                    crate::leanh::lean_dec_ref_known(v_x_573_, 2);
                    v___x_580_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(
                        v_unicode_572_,
                        v_pre_574_,
                    );
                    v___x_581_ = l_Lean_Name_num___override(v___x_580_, v_i_579_);
                    return v___x_581_;
                } else {
                    let mut v_i_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_i_582_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                    crate::leanh::lean_inc(v_i_582_);
                    crate::leanh::lean_dec_ref_known(v_x_573_, 2);
                    v___x_583_ = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(
                        v_unicode_572_,
                        v_pre_574_,
                    );
                    v___x_584_ =
                        l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__0;
                    v___x_585_ = l_Nat_toSuperscriptString(v_i_582_);
                    v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
                    crate::leanh::lean_dec_ref(v___x_585_);
                    v___x_587_ = lean_name_append_after(v___x_583_, v___x_586_);
                    return v___x_587_;
                }
            }
        }
    } else {
        return v_x_573_;
    }
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(
    mut v_unicode_588_: *mut crate::leanh::LeanObject,
    mut v_x_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_unicode_boxed_590_: u8 = 0;
    let mut v_res_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_unicode_boxed_590_ = (crate::leanh::lean_unbox(v_unicode_588_) as u8);
    v_res_591_ =
        l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v_unicode_boxed_590_, v_x_589_);
    return v_res_591_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(
    mut v_name_592_: *mut crate::leanh::LeanObject,
    mut v_decl_593_: *mut crate::leanh::LeanObject,
    mut v_ref_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_605_: u8 = 0;
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_610_: u8 = 0;
    let mut v_unused_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_596_ = crate::leanh::lean_ctor_get(v_decl_593_, 0);
                v_descr_597_ = crate::leanh::lean_ctor_get(v_decl_593_, 1);
                v_deprecation_x3f_598_ = crate::leanh::lean_ctor_get(v_decl_593_, 2);
                v___x_599_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_600_ = (crate::leanh::lean_unbox(v_defValue_596_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_599_, 0 as u32, v___x_600_);
                crate::leanh::lean_inc(v_deprecation_x3f_598_);
                crate::leanh::lean_inc_ref(v_descr_597_);
                crate::leanh::lean_inc_n(v_name_592_, 2);
                v___x_601_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_601_, 0, v_name_592_);
                crate::leanh::lean_ctor_set(v___x_601_, 1, v_ref_594_);
                crate::leanh::lean_ctor_set(v___x_601_, 2, v___x_599_);
                crate::leanh::lean_ctor_set(v___x_601_, 3, v_descr_597_);
                crate::leanh::lean_ctor_set(v___x_601_, 4, v_deprecation_x3f_598_);
                v___x_602_ = lean_register_option(v_name_592_, v___x_601_);
                if crate::leanh::lean_obj_tag(v___x_602_) == 0 {
                    v_isSharedCheck_610_ = (!crate::leanh::lean_is_exclusive(v___x_602_)) as u8;
                    if v_isSharedCheck_610_ == 0 {
                        v_unused_611_ = crate::leanh::lean_ctor_get(v___x_602_, 0);
                        crate::leanh::lean_dec(v_unused_611_);
                        v___x_604_ = v___x_602_;
                        v_isShared_605_ = v_isSharedCheck_610_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_602_);
                        v___x_604_ = crate::leanh::lean_box(0);
                        v_isShared_605_ = v_isSharedCheck_610_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_592_);
                    v_a_612_ = crate::leanh::lean_ctor_get(v___x_602_, 0);
                    v_isSharedCheck_619_ = (!crate::leanh::lean_is_exclusive(v___x_602_)) as u8;
                    if v_isSharedCheck_619_ == 0 {
                        v___x_614_ = v___x_602_;
                        v_isShared_615_ = v_isSharedCheck_619_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_612_);
                        crate::leanh::lean_dec(v___x_602_);
                        v___x_614_ = crate::leanh::lean_box(0);
                        v_isShared_615_ = v_isSharedCheck_619_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_596_);
                v___x_606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_606_, 0, v_name_592_);
                crate::leanh::lean_ctor_set(v___x_606_, 1, v_defValue_596_);
                if v_isShared_605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_604_, 0, v___x_606_);
                    v___x_608_ = v___x_604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
                    v___x_608_ = v_reuseFailAlloc_609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_608_;
            }
            3 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_620_: *mut crate::leanh::LeanObject,
    mut v_decl_621_: *mut crate::leanh::LeanObject,
    mut v_ref_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v_name_620_, v_decl_621_, v_ref_622_);
    crate::leanh::lean_dec_ref(v_decl_621_);
    return v_res_624_;
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = l___private_Lean_Hygiene_0__Lean_initFn___closed__2_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_;
    v___x_643_ = l___private_Lean_Hygiene_0__Lean_initFn___closed__4_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_;
    v___x_644_ = l___private_Lean_Hygiene_0__Lean_initFn___closed__6_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_;
    v___x_645_ = l_Lean_Option_register___at___00__private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4__spec__0(v___x_642_, v___x_643_, v___x_644_);
    return v___x_645_;
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4____boxed(
    mut v_a_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_647_ =
        l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_(
        );
    return v_res_647_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(
    mut v_opts_648_: *mut crate::leanh::LeanObject,
    mut v_opt_649_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_650_ = crate::leanh::lean_ctor_get(v_opt_649_, 0);
    v_defValue_651_ = crate::leanh::lean_ctor_get(v_opt_649_, 1);
    v_map_652_ = crate::leanh::lean_ctor_get(v_opts_648_, 0);
    v___x_653_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_652_,
            v_name_650_,
        );
    if crate::leanh::lean_obj_tag(v___x_653_) == 0 {
        let mut v___x_654_: u8 = 0;
        v___x_654_ = (crate::leanh::lean_unbox(v_defValue_651_) as u8);
        return v___x_654_;
    } else {
        let mut v_val_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_655_ = crate::leanh::lean_ctor_get(v___x_653_, 0);
        crate::leanh::lean_inc(v_val_655_);
        crate::leanh::lean_dec_ref_known(v___x_653_, 1);
        if crate::leanh::lean_obj_tag(v_val_655_) == 1 {
            let mut v_v_656_: u8 = 0;
            v_v_656_ = crate::leanh::lean_ctor_get_uint8(v_val_655_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_655_, 0);
            return v_v_656_;
        } else {
            let mut v___x_657_: u8 = 0;
            crate::leanh::lean_dec(v_val_655_);
            v___x_657_ = (crate::leanh::lean_unbox(v_defValue_651_) as u8);
            return v___x_657_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0___boxed(
    mut v_opts_658_: *mut crate::leanh::LeanObject,
    mut v_opt_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: u8 = 0;
    let mut v_r_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_opts_658_, v_opt_659_);
    crate::leanh::lean_dec_ref(v_opt_659_);
    crate::leanh::lean_dec_ref(v_opts_658_);
    v_r_661_ = crate::leanh::lean_box((v_res_660_) as usize);
    return v_r_661_;
}
pub unsafe fn l_Lean_getSanitizeNames(mut v_o_662_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    v___x_663_ = l_Lean_pp_sanitizeNames;
    v___x_664_ = l_Lean_Option_get___at___00Lean_getSanitizeNames_spec__0(v_o_662_, v___x_663_);
    return v___x_664_;
}
pub unsafe fn l_Lean_getSanitizeNames___boxed(
    mut v_o_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_666_: u8 = 0;
    let mut v_r_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_getSanitizeNames(v_o_665_);
    crate::leanh::lean_dec_ref(v_o_665_);
    v_r_667_ = crate::leanh::lean_box((v_res_666_) as usize);
    return v_r_667_;
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(
    mut v_userName_668_: *mut crate::leanh::LeanObject,
    mut v_idx_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nameStem2Idx_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName2Sanitized_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_688_: u8 = 0;
    let mut v_unused_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_671_ = crate::leanh::lean_ctor_get(v_a_670_, 0);
                v_nameStem2Idx_672_ = crate::leanh::lean_ctor_get(v_a_670_, 1);
                v_userName2Sanitized_673_ = crate::leanh::lean_ctor_get(v_a_670_, 2);
                v___x_674_ = l_Std_Format_getUnicode(v_options_671_);
                crate::leanh::lean_inc(v_idx_669_);
                crate::leanh::lean_inc(v_userName_668_);
                v___x_675_ = l_Lean_Name_num___override(v_userName_668_, v_idx_669_);
                v___x_676_ =
                    l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(v___x_674_, v___x_675_);
                v___x_677_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___x_676_, v_nameStem2Idx_672_);
                if v___x_677_ == 0 {
                    crate::leanh::lean_inc(v_userName2Sanitized_673_);
                    crate::leanh::lean_inc(v_nameStem2Idx_672_);
                    crate::leanh::lean_inc_ref(v_options_671_);
                    v_isSharedCheck_688_ = (!crate::leanh::lean_is_exclusive(v_a_670_)) as u8;
                    if v_isSharedCheck_688_ == 0 {
                        v_unused_689_ = crate::leanh::lean_ctor_get(v_a_670_, 2);
                        crate::leanh::lean_dec(v_unused_689_);
                        v_unused_690_ = crate::leanh::lean_ctor_get(v_a_670_, 1);
                        crate::leanh::lean_dec(v_unused_690_);
                        v_unused_691_ = crate::leanh::lean_ctor_get(v_a_670_, 0);
                        crate::leanh::lean_dec(v_unused_691_);
                        v___x_679_ = v_a_670_;
                        v_isShared_680_ = v_isSharedCheck_688_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_670_);
                        v___x_679_ = crate::leanh::lean_box(0);
                        v_isShared_680_ = v_isSharedCheck_688_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_676_);
                    v___x_692_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_693_ = lean_nat_add(v_idx_669_, v___x_692_);
                    crate::leanh::lean_dec(v_idx_669_);
                    v_idx_669_ = v___x_693_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_681_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_682_ = lean_nat_add(v_idx_669_, v___x_681_);
                crate::leanh::lean_dec(v_idx_669_);
                v___x_683_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_668_, v___x_682_, v_nameStem2Idx_672_);
                if v_isShared_680_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_679_, 1, v___x_683_);
                    v___x_685_ = v___x_679_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_687_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_687_, 0, v_options_671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_683_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_687_,
                        2,
                        v_userName2Sanitized_673_,
                    );
                    v___x_685_ = v_reuseFailAlloc_687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_676_);
                crate::leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
                return v___x_686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_sanitizeName(
    mut v_userName_695_: *mut crate::leanh::LeanObject,
    mut v_a_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nameStem2Idx_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stem_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_706_: u8 = 0;
    let mut v_options_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nameStem2Idx_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName2Sanitized_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_720_: u8 = 0;
    let mut v_isSharedCheck_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_nameStem2Idx_697_ = crate::leanh::lean_ctor_get(v_a_696_, 1);
                crate::leanh::lean_inc(v_userName_695_);
                v_stem_698_ = lean_erase_macro_scopes(v_userName_695_);
                v___x_722_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_nameStem2Idx_697_, v_stem_698_);
                if crate::leanh::lean_obj_tag(v___x_722_) == 0 {
                    v___x_723_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_700_ = v___x_723_;
                    state = 1;
                    continue;
                } else {
                    v_val_724_ = crate::leanh::lean_ctor_get(v___x_722_, 0);
                    crate::leanh::lean_inc(v_val_724_);
                    crate::leanh::lean_dec_ref_known(v___x_722_, 1);
                    v___y_700_ = v_val_724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_701_ = l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(
                    v_stem_698_,
                    v___y_700_,
                    v_a_696_,
                );
                v_snd_702_ = crate::leanh::lean_ctor_get(v___x_701_, 1);
                v_fst_703_ = crate::leanh::lean_ctor_get(v___x_701_, 0);
                v_isSharedCheck_721_ = (!crate::leanh::lean_is_exclusive(v___x_701_)) as u8;
                if v_isSharedCheck_721_ == 0 {
                    v___x_705_ = v___x_701_;
                    v_isShared_706_ = v_isSharedCheck_721_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_702_);
                    crate::leanh::lean_inc(v_fst_703_);
                    crate::leanh::lean_dec(v___x_701_);
                    v___x_705_ = crate::leanh::lean_box(0);
                    v_isShared_706_ = v_isSharedCheck_721_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_options_707_ = crate::leanh::lean_ctor_get(v_snd_702_, 0);
                v_nameStem2Idx_708_ = crate::leanh::lean_ctor_get(v_snd_702_, 1);
                v_userName2Sanitized_709_ = crate::leanh::lean_ctor_get(v_snd_702_, 2);
                v_isSharedCheck_720_ = (!crate::leanh::lean_is_exclusive(v_snd_702_)) as u8;
                if v_isSharedCheck_720_ == 0 {
                    v___x_711_ = v_snd_702_;
                    v_isShared_712_ = v_isSharedCheck_720_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_userName2Sanitized_709_);
                    crate::leanh::lean_inc(v_nameStem2Idx_708_);
                    crate::leanh::lean_inc(v_options_707_);
                    crate::leanh::lean_dec(v_snd_702_);
                    v___x_711_ = crate::leanh::lean_box(0);
                    v_isShared_712_ = v_isSharedCheck_720_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_fst_703_);
                v___x_713_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_userName_695_, v_fst_703_, v_userName2Sanitized_709_);
                if v_isShared_712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_711_, 2, v___x_713_);
                    v___x_715_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_719_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 0, v_options_707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 1, v_nameStem2Idx_708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_713_);
                    v___x_715_ = v_reuseFailAlloc_719_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_715_);
                    v___x_717_ = v___x_705_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
                    v___x_717_ = v_reuseFailAlloc_718_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(
    mut v_x_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName2Sanitized_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v_sz_747_: usize = 0;
    let mut v___x_748_: usize = 0;
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_725_) {
                3 => {
                    v_val_733_ = crate::leanh::lean_ctor_get(v_x_725_, 2);
                    v_userName2Sanitized_734_ = crate::leanh::lean_ctor_get(v_a_726_, 2);
                    v___x_735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_userName2Sanitized_734_, v_val_733_);
                    if crate::leanh::lean_obj_tag(v___x_735_) == 0 {
                        v___x_736_ = l_Lean_Name_hasMacroScopes(v_val_733_);
                        if v___x_736_ == 0 {
                            crate::leanh::lean_inc(v_val_733_);
                            v_n_728_ = v_val_733_;
                            v___y_729_ = v_a_726_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_733_);
                            v___x_737_ = l_Lean_sanitizeName(v_val_733_, v_a_726_);
                            v_fst_738_ = crate::leanh::lean_ctor_get(v___x_737_, 0);
                            crate::leanh::lean_inc(v_fst_738_);
                            v_snd_739_ = crate::leanh::lean_ctor_get(v___x_737_, 1);
                            crate::leanh::lean_inc(v_snd_739_);
                            crate::leanh::lean_dec_ref(v___x_737_);
                            v_n_728_ = v_fst_738_;
                            v___y_729_ = v_snd_739_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_740_ = crate::leanh::lean_ctor_get(v___x_735_, 0);
                        crate::leanh::lean_inc(v_val_740_);
                        crate::leanh::lean_dec_ref_known(v___x_735_, 1);
                        v_n_728_ = v_val_740_;
                        v___y_729_ = v_a_726_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_info_741_ = crate::leanh::lean_ctor_get(v_x_725_, 0);
                    v_kind_742_ = crate::leanh::lean_ctor_get(v_x_725_, 1);
                    v_args_743_ = crate::leanh::lean_ctor_get(v_x_725_, 2);
                    v_isSharedCheck_762_ = (!crate::leanh::lean_is_exclusive(v_x_725_)) as u8;
                    if v_isSharedCheck_762_ == 0 {
                        v___x_745_ = v_x_725_;
                        v_isShared_746_ = v_isSharedCheck_762_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_743_);
                        crate::leanh::lean_inc(v_kind_742_);
                        crate::leanh::lean_inc(v_info_741_);
                        crate::leanh::lean_dec(v_x_725_);
                        v___x_745_ = crate::leanh::lean_box(0);
                        v_isShared_746_ = v_isSharedCheck_762_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_763_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_763_, 0, v_x_725_);
                    crate::leanh::lean_ctor_set(v___x_763_, 1, v_a_726_);
                    return v___x_763_;
                }
            },
            1 => {
                v___x_730_ = 0;
                v___x_731_ = l_Lean_mkIdentFrom(v_x_725_, v_n_728_, v___x_730_);
                crate::leanh::lean_dec(v_x_725_);
                v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_731_);
                crate::leanh::lean_ctor_set(v___x_732_, 1, v___y_729_);
                return v___x_732_;
            }
            2 => {
                v_sz_747_ = lean_array_size(v_args_743_);
                v___x_748_ = 0usize;
                v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_747_, v___x_748_, v_args_743_, v_a_726_);
                v_fst_750_ = crate::leanh::lean_ctor_get(v___x_749_, 0);
                v_snd_751_ = crate::leanh::lean_ctor_get(v___x_749_, 1);
                v_isSharedCheck_761_ = (!crate::leanh::lean_is_exclusive(v___x_749_)) as u8;
                if v_isSharedCheck_761_ == 0 {
                    v___x_753_ = v___x_749_;
                    v_isShared_754_ = v_isSharedCheck_761_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_751_);
                    crate::leanh::lean_inc(v_fst_750_);
                    crate::leanh::lean_dec(v___x_749_);
                    v___x_753_ = crate::leanh::lean_box(0);
                    v_isShared_754_ = v_isSharedCheck_761_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_745_, 2, v_fst_750_);
                    v___x_756_ = v___x_745_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_info_741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 1, v_kind_742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 2, v_fst_750_);
                    v___x_756_ = v_reuseFailAlloc_760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_753_, 0, v___x_756_);
                    v___x_758_ = v___x_753_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_751_);
                    v___x_758_ = v_reuseFailAlloc_759_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(
    mut v_sz_764_: usize,
    mut v_i_765_: usize,
    mut v_bs_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_768_: u8 = 0;
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: usize = 0;
    let mut v___x_777_: usize = 0;
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_768_ = lean_usize_dec_lt(v_i_765_, v_sz_764_);
                if v___x_768_ == 0 {
                    v___x_769_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_769_, 0, v_bs_766_);
                    crate::leanh::lean_ctor_set(v___x_769_, 1, v___y_767_);
                    return v___x_769_;
                } else {
                    v_v_770_ = lean_array_uget_borrowed(v_bs_766_, v_i_765_);
                    crate::leanh::lean_inc(v_v_770_);
                    v___x_771_ =
                        l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_v_770_, v___y_767_);
                    v_fst_772_ = crate::leanh::lean_ctor_get(v___x_771_, 0);
                    crate::leanh::lean_inc(v_fst_772_);
                    v_snd_773_ = crate::leanh::lean_ctor_get(v___x_771_, 1);
                    crate::leanh::lean_inc(v_snd_773_);
                    crate::leanh::lean_dec_ref(v___x_771_);
                    v___x_774_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_775_ = lean_array_uset(v_bs_766_, v_i_765_, v___x_774_);
                    v___x_776_ = 1usize;
                    v___x_777_ = lean_usize_add(v_i_765_, v___x_776_);
                    v___x_778_ = lean_array_uset(v_bs_x27_775_, v_i_765_, v_fst_772_);
                    v_i_765_ = v___x_777_;
                    v_bs_766_ = v___x_778_;
                    v___y_767_ = v_snd_773_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0___boxed(
    mut v_sz_780_: *mut crate::leanh::LeanObject,
    mut v_i_781_: *mut crate::leanh::LeanObject,
    mut v_bs_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_784_: usize = 0;
    let mut v_i_boxed_785_: usize = 0;
    let mut v_res_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_784_ = crate::leanh::lean_unbox_usize(v_sz_780_);
    crate::leanh::lean_dec(v_sz_780_);
    v_i_boxed_785_ = crate::leanh::lean_unbox_usize(v_i_781_);
    crate::leanh::lean_dec(v_i_781_);
    v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux_spec__0(v_sz_boxed_784_, v_i_boxed_785_, v_bs_782_, v___y_783_);
    return v_res_786_;
}
pub unsafe fn l_Lean_sanitizeSyntax(
    mut v_stx_787_: *mut crate::leanh::LeanObject,
    mut v_a_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    v_options_789_ = crate::leanh::lean_ctor_get(v_a_788_, 0);
    v___x_790_ = l_Lean_getSanitizeNames(v_options_789_);
    if v___x_790_ == 0 {
        let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_791_, 0, v_stx_787_);
        crate::leanh::lean_ctor_set(v___x_791_, 1, v_a_788_);
        return v___x_791_;
    } else {
        let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_792_ = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(v_stx_787_, v_a_788_);
        return v___x_792_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Hygiene(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        l___private_Lean_Hygiene_0__Lean_initFn_00___x40_Lean_Hygiene_3990390237____hygCtx___hyg_4_(
        );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_pp_sanitizeNames = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_pp_sanitizeNames);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Hygiene(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Hygiene(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Hygiene(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Hygiene(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Hygiene(builtin);
}
