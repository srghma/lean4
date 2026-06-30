// Lean compiler output
// Module: Lean.Util.SCC
// Imports: Std.Data.HashMap.Basic Init.Data.Option.Coe
use crate::ffi::{lean_mk_array, lean_nat_add, lean_nat_dec_lt};
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
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Control::l_List_forM___redArg;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Prelude::{
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqNat___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
pub static l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value:
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
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value:
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
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value:
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
    m_fun: l_StateT_bind as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value:
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
    m_fun: l_StateT_pure as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value:
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
    m_fun: l_StateT_map as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__14_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__10_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__15_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__16_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__11_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__12_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__13_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__17_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__18_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SCC_scc___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SCC_scc___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SCC_scc___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SCC_scc___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_SCC_scc___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SCC_scc___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_a_388_: *mut leanh::LeanObject,
    mut v_a_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_data_390_ = leanh::lean_ctor_get(v_a_389_, 2);
    v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v_inst_386_,
        v_inst_387_,
        v_data_390_,
        v_a_388_,
    );
    if leanh::lean_obj_tag(v___x_391_) == 0 {
        let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_392_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg___closed__0;
        v___x_393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_393_, 0, v___x_392_);
        leanh::lean_ctor_set(v___x_393_, 1, v_a_389_);
        return v___x_393_;
    } else {
        let mut v_val_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_394_ = leanh::lean_ctor_get(v___x_391_, 0);
        leanh::lean_inc(v_val_394_);
        leanh::lean_dec_ref_known(v___x_391_, 1);
        v___x_395_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_395_, 0, v_val_394_);
        leanh::lean_ctor_set(v___x_395_, 1, v_a_389_);
        return v___x_395_;
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf(
    mut v_00_u03b1_396_: *mut leanh::LeanObject,
    mut v_inst_397_: *mut leanh::LeanObject,
    mut v_inst_398_: *mut leanh::LeanObject,
    mut v_a_399_: *mut leanh::LeanObject,
    mut v_a_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
        v_inst_397_,
        v_inst_398_,
        v_a_399_,
        v_a_400_,
    );
    return v___x_401_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(
    mut v_inst_402_: *mut leanh::LeanObject,
    mut v_inst_403_: *mut leanh::LeanObject,
    mut v_a_404_: *mut leanh::LeanObject,
    mut v_a_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stack_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIndex_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sccs_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: u8 = 0;
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stack_406_ = leanh::lean_ctor_get(v_a_405_, 0);
                v_nextIndex_407_ = leanh::lean_ctor_get(v_a_405_, 1);
                v_data_408_ = leanh::lean_ctor_get(v_a_405_, 2);
                v_sccs_409_ = leanh::lean_ctor_get(v_a_405_, 3);
                v_isSharedCheck_425_ = (!leanh::lean_is_exclusive(v_a_405_)) as u8;
                if v_isSharedCheck_425_ == 0 {
                    v___x_411_ = v_a_405_;
                    v_isShared_412_ = v_isSharedCheck_425_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_sccs_409_);
                    leanh::lean_inc(v_data_408_);
                    leanh::lean_inc(v_nextIndex_407_);
                    leanh::lean_inc(v_stack_406_);
                    leanh::lean_dec(v_a_405_);
                    v___x_411_ = leanh::lean_box(0);
                    v_isShared_412_ = v_isSharedCheck_425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_413_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_404_);
                v___x_414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_414_, 0, v_a_404_);
                leanh::lean_ctor_set(v___x_414_, 1, v_stack_406_);
                v___x_415_ = leanh::lean_unsigned_to_nat(1);
                v___x_416_ = lean_nat_add(v_nextIndex_407_, v___x_415_);
                v___x_417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_417_, 0, v_nextIndex_407_);
                v___x_418_ = 1;
                leanh::lean_inc_ref(v___x_417_);
                v___x_419_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_419_, 0, v___x_417_);
                leanh::lean_ctor_set(v___x_419_, 1, v___x_417_);
                leanh::lean_ctor_set_uint8(
                    v___x_419_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_418_,
                );
                v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_402_,
                    v_inst_403_,
                    v_data_408_,
                    v_a_404_,
                    v___x_419_,
                );
                if v_isShared_412_ == 0 {
                    leanh::lean_ctor_set(v___x_411_, 2, v___x_420_);
                    leanh::lean_ctor_set(v___x_411_, 1, v___x_416_);
                    leanh::lean_ctor_set(v___x_411_, 0, v___x_414_);
                    v___x_422_ = v___x_411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_424_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_424_, 2, v___x_420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_424_, 3, v_sccs_409_);
                    v___x_422_ = v_reuseFailAlloc_424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_423_, 0, v___x_413_);
                leanh::lean_ctor_set(v___x_423_, 1, v___x_422_);
                return v___x_423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_push(
    mut v_00_u03b1_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_inst_428_: *mut leanh::LeanObject,
    mut v_a_429_: *mut leanh::LeanObject,
    mut v_a_430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(
        v_inst_427_,
        v_inst_428_,
        v_a_429_,
        v_a_430_,
    );
    return v___x_431_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(
    mut v_inst_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_a_434_: *mut leanh::LeanObject,
    mut v_f_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stack_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIndex_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sccs_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_443_: u8 = 0;
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stack_437_ = leanh::lean_ctor_get(v_a_436_, 0);
                v_nextIndex_438_ = leanh::lean_ctor_get(v_a_436_, 1);
                v_data_439_ = leanh::lean_ctor_get(v_a_436_, 2);
                v_sccs_440_ = leanh::lean_ctor_get(v_a_436_, 3);
                v_isSharedCheck_455_ = (!leanh::lean_is_exclusive(v_a_436_)) as u8;
                if v_isSharedCheck_455_ == 0 {
                    v___x_442_ = v_a_436_;
                    v_isShared_443_ = v_isSharedCheck_455_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_sccs_440_);
                    leanh::lean_inc(v_data_439_);
                    leanh::lean_inc(v_nextIndex_438_);
                    leanh::lean_inc(v_stack_437_);
                    leanh::lean_dec(v_a_436_);
                    v___x_442_ = leanh::lean_box(0);
                    v_isShared_443_ = v_isSharedCheck_455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_444_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_434_);
                leanh::lean_inc_ref(v_inst_433_);
                leanh::lean_inc_ref(v_inst_432_);
                v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_432_,
                    v_inst_433_,
                    v_data_439_,
                    v_a_434_,
                );
                if leanh::lean_obj_tag(v___x_451_) == 0 {
                    leanh::lean_dec_ref(v_f_435_);
                    leanh::lean_dec(v_a_434_);
                    leanh::lean_dec_ref(v_inst_433_);
                    leanh::lean_dec_ref(v_inst_432_);
                    v___y_446_ = v_data_439_;
                    state = 2;
                    continue;
                } else {
                    v_val_452_ = leanh::lean_ctor_get(v___x_451_, 0);
                    leanh::lean_inc(v_val_452_);
                    leanh::lean_dec_ref_known(v___x_451_, 1);
                    v___x_453_ = leanh::lean_apply_1(v_f_435_, v_val_452_);
                    v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_432_,
                        v_inst_433_,
                        v_data_439_,
                        v_a_434_,
                        v___x_453_,
                    );
                    v___y_446_ = v___x_454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_443_ == 0 {
                    leanh::lean_ctor_set(v___x_442_, 2, v___y_446_);
                    v___x_448_ = v___x_442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_450_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 0, v_stack_437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 1, v_nextIndex_438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 2, v___y_446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 3, v_sccs_440_);
                    v___x_448_ = v_reuseFailAlloc_450_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_449_, 0, v___x_444_);
                leanh::lean_ctor_set(v___x_449_, 1, v___x_448_);
                return v___x_449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf(
    mut v_00_u03b1_456_: *mut leanh::LeanObject,
    mut v_inst_457_: *mut leanh::LeanObject,
    mut v_inst_458_: *mut leanh::LeanObject,
    mut v_a_459_: *mut leanh::LeanObject,
    mut v_f_460_: *mut leanh::LeanObject,
    mut v_a_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(
        v_inst_457_,
        v_inst_458_,
        v_a_459_,
        v_f_460_,
        v_a_461_,
    );
    return v___x_462_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___lam__0(
    mut v_d_463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_index_x3f_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_468_: u8 = 0;
    let mut v___x_469_: u8 = 0;
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_index_x3f_464_ = leanh::lean_ctor_get(v_d_463_, 0);
                v_lowlink_x3f_465_ = leanh::lean_ctor_get(v_d_463_, 1);
                v_isSharedCheck_473_ = (!leanh::lean_is_exclusive(v_d_463_)) as u8;
                if v_isSharedCheck_473_ == 0 {
                    v___x_467_ = v_d_463_;
                    v_isShared_468_ = v_isSharedCheck_473_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_lowlink_x3f_465_);
                    leanh::lean_inc(v_index_x3f_464_);
                    leanh::lean_dec(v_d_463_);
                    v___x_467_ = leanh::lean_box(0);
                    v_isShared_468_ = v_isSharedCheck_473_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_469_ = 0;
                if v_isShared_468_ == 0 {
                    v___x_471_ = v___x_467_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_472_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_472_, 0, v_index_x3f_464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_472_, 1, v_lowlink_x3f_465_);
                    v___x_471_ = v_reuseFailAlloc_472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_471_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_469_,
                );
                return v___x_471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_a_477_: *mut leanh::LeanObject,
    mut v_a_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_479_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg___closed__0;
    v___x_480_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(
        v_inst_475_,
        v_inst_476_,
        v_a_477_,
        v___f_479_,
        v_a_478_,
    );
    return v___x_480_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack(
    mut v_00_u03b1_481_: *mut leanh::LeanObject,
    mut v_inst_482_: *mut leanh::LeanObject,
    mut v_inst_483_: *mut leanh::LeanObject,
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(
        v_inst_482_,
        v_inst_483_,
        v_a_484_,
        v_a_485_,
    );
    return v___x_486_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0(
    mut v_v_487_: *mut leanh::LeanObject,
    mut v_d_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lowlink_x3f_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onStack_491_: u8 = 0;
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_498_: u8 = 0;
    let mut v_unused_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onStack_501_: u8 = 0;
    let mut v_val_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_507_: u8 = 0;
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_511_: u8 = 0;
    let mut v_unused_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_v_487_) == 0 {
                    return v_d_488_;
                } else {
                    v_lowlink_x3f_489_ = leanh::lean_ctor_get(v_d_488_, 1);
                    if leanh::lean_obj_tag(v_lowlink_x3f_489_) == 0 {
                        v_index_x3f_490_ = leanh::lean_ctor_get(v_d_488_, 0);
                        v_onStack_491_ = leanh::lean_ctor_get_uint8(
                            v_d_488_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_498_ = (!leanh::lean_is_exclusive(v_d_488_)) as u8;
                        if v_isSharedCheck_498_ == 0 {
                            v_unused_499_ = leanh::lean_ctor_get(v_d_488_, 1);
                            leanh::lean_dec(v_unused_499_);
                            v___x_493_ = v_d_488_;
                            v_isShared_494_ = v_isSharedCheck_498_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_index_x3f_490_);
                            leanh::lean_dec(v_d_488_);
                            v___x_493_ = leanh::lean_box(0);
                            v_isShared_494_ = v_isSharedCheck_498_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_index_x3f_500_ = leanh::lean_ctor_get(v_d_488_, 0);
                        v_onStack_501_ = leanh::lean_ctor_get_uint8(
                            v_d_488_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_val_502_ = leanh::lean_ctor_get(v_v_487_, 0);
                        v_val_503_ = leanh::lean_ctor_get(v_lowlink_x3f_489_, 0);
                        v___x_504_ = lean_nat_dec_lt(v_val_503_, v_val_502_);
                        if v___x_504_ == 0 {
                            leanh::lean_inc(v_index_x3f_500_);
                            v_isSharedCheck_511_ =
                                (!leanh::lean_is_exclusive(v_d_488_)) as u8;
                            if v_isSharedCheck_511_ == 0 {
                                v_unused_512_ = leanh::lean_ctor_get(v_d_488_, 1);
                                leanh::lean_dec(v_unused_512_);
                                v_unused_513_ = leanh::lean_ctor_get(v_d_488_, 0);
                                leanh::lean_dec(v_unused_513_);
                                v___x_506_ = v_d_488_;
                                v_isShared_507_ = v_isSharedCheck_511_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_d_488_);
                                v___x_506_ = leanh::lean_box(0);
                                v_isShared_507_ = v_isSharedCheck_511_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_v_487_, 1);
                            return v_d_488_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_494_ == 0 {
                    leanh::lean_ctor_set(v___x_493_, 1, v_v_487_);
                    v___x_496_ = v___x_493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_497_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 0, v_index_x3f_490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 1, v_v_487_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_497_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_onStack_491_,
                    );
                    v___x_496_ = v_reuseFailAlloc_497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_496_;
            }
            3 => {
                if v_isShared_507_ == 0 {
                    leanh::lean_ctor_set(v___x_506_, 1, v_v_487_);
                    v___x_509_ = v___x_506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_510_, 0, v_index_x3f_500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_510_, 1, v_v_487_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_510_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_onStack_501_,
                    );
                    v___x_509_ = v_reuseFailAlloc_510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(
    mut v_inst_514_: *mut leanh::LeanObject,
    mut v_inst_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_v_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_519_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_519_, 0, v_v_517_);
    v___x_520_ = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___redArg(
        v_inst_514_,
        v_inst_515_,
        v_a_516_,
        v___f_519_,
        v_a_518_,
    );
    return v___x_520_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf(
    mut v_00_u03b1_521_: *mut leanh::LeanObject,
    mut v_inst_522_: *mut leanh::LeanObject,
    mut v_inst_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
    mut v_v_525_: *mut leanh::LeanObject,
    mut v_a_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(
        v_inst_522_,
        v_inst_523_,
        v_a_524_,
        v_v_525_,
        v_a_526_,
    );
    return v___x_527_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(
    mut v_inst_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_x_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nextIndex_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sccs_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut v_unused_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_552_: u8 = 0;
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_557_: u8 = 0;
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    let mut v_nextIndex_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sccs_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_568_: u8 = 0;
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_unused_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut v_unused_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_531_) == 0 {
                    leanh::lean_dec(v_a_530_);
                    leanh::lean_dec_ref(v_inst_529_);
                    leanh::lean_dec_ref(v_inst_528_);
                    v_nextIndex_534_ = leanh::lean_ctor_get(v_a_533_, 1);
                    v_data_535_ = leanh::lean_ctor_get(v_a_533_, 2);
                    v_sccs_536_ = leanh::lean_ctor_get(v_a_533_, 3);
                    v_isSharedCheck_546_ = (!leanh::lean_is_exclusive(v_a_533_)) as u8;
                    if v_isSharedCheck_546_ == 0 {
                        v_unused_547_ = leanh::lean_ctor_get(v_a_533_, 0);
                        leanh::lean_dec(v_unused_547_);
                        v___x_538_ = v_a_533_;
                        v_isShared_539_ = v_isSharedCheck_546_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_sccs_536_);
                        leanh::lean_inc(v_data_535_);
                        leanh::lean_inc(v_nextIndex_534_);
                        leanh::lean_dec(v_a_533_);
                        v___x_538_ = leanh::lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_548_ = leanh::lean_ctor_get(v_x_531_, 0);
                    v_tail_549_ = leanh::lean_ctor_get(v_x_531_, 1);
                    v_isSharedCheck_582_ = (!leanh::lean_is_exclusive(v_x_531_)) as u8;
                    if v_isSharedCheck_582_ == 0 {
                        v___x_551_ = v_x_531_;
                        v_isShared_552_ = v_isSharedCheck_582_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_549_);
                        leanh::lean_inc(v_head_548_);
                        leanh::lean_dec(v_x_531_);
                        v___x_551_ = leanh::lean_box(0);
                        v_isShared_552_ = v_isSharedCheck_582_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_540_ = leanh::lean_box(0);
                v___x_541_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_541_, 0, v_x_532_);
                leanh::lean_ctor_set(v___x_541_, 1, v_sccs_536_);
                if v_isShared_539_ == 0 {
                    leanh::lean_ctor_set(v___x_538_, 3, v___x_541_);
                    leanh::lean_ctor_set(v___x_538_, 0, v_x_531_);
                    v___x_543_ = v___x_538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_545_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_545_, 0, v_x_531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextIndex_534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_545_, 2, v_data_535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_545_, 3, v___x_541_);
                    v___x_543_ = v_reuseFailAlloc_545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_544_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_544_, 0, v___x_540_);
                leanh::lean_ctor_set(v___x_544_, 1, v___x_543_);
                return v___x_544_;
            }
            3 => {
                leanh::lean_inc(v_head_548_);
                leanh::lean_inc_ref(v_inst_529_);
                leanh::lean_inc_ref(v_inst_528_);
                v___x_553_ = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___redArg(
                    v_inst_528_,
                    v_inst_529_,
                    v_head_548_,
                    v_a_533_,
                );
                v_snd_554_ = leanh::lean_ctor_get(v___x_553_, 1);
                v_isSharedCheck_580_ = (!leanh::lean_is_exclusive(v___x_553_)) as u8;
                if v_isSharedCheck_580_ == 0 {
                    v_unused_581_ = leanh::lean_ctor_get(v___x_553_, 0);
                    leanh::lean_dec(v_unused_581_);
                    v___x_556_ = v___x_553_;
                    v_isShared_557_ = v_isSharedCheck_580_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_554_);
                    leanh::lean_dec(v___x_553_);
                    v___x_556_ = leanh::lean_box(0);
                    v_isShared_557_ = v_isSharedCheck_580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_head_548_);
                if v_isShared_552_ == 0 {
                    leanh::lean_ctor_set(v___x_551_, 1, v_x_532_);
                    v___x_559_ = v___x_551_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_head_548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_579_, 1, v_x_532_);
                    v___x_559_ = v_reuseFailAlloc_579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v_inst_528_);
                leanh::lean_inc(v_a_530_);
                v___x_560_ = leanh::lean_apply_2(v_inst_528_, v_a_530_, v_head_548_);
                v___x_561_ = (leanh::lean_unbox(v___x_560_) as u8);
                if v___x_561_ == 0 {
                    leanh::lean_del_object(v___x_556_);
                    v_x_531_ = v_tail_549_;
                    v_x_532_ = v___x_559_;
                    v_a_533_ = v_snd_554_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_530_);
                    leanh::lean_dec_ref(v_inst_529_);
                    leanh::lean_dec_ref(v_inst_528_);
                    v_nextIndex_563_ = leanh::lean_ctor_get(v_snd_554_, 1);
                    v_data_564_ = leanh::lean_ctor_get(v_snd_554_, 2);
                    v_sccs_565_ = leanh::lean_ctor_get(v_snd_554_, 3);
                    v_isSharedCheck_577_ = (!leanh::lean_is_exclusive(v_snd_554_)) as u8;
                    if v_isSharedCheck_577_ == 0 {
                        v_unused_578_ = leanh::lean_ctor_get(v_snd_554_, 0);
                        leanh::lean_dec(v_unused_578_);
                        v___x_567_ = v_snd_554_;
                        v_isShared_568_ = v_isSharedCheck_577_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_sccs_565_);
                        leanh::lean_inc(v_data_564_);
                        leanh::lean_inc(v_nextIndex_563_);
                        leanh::lean_dec(v_snd_554_);
                        v___x_567_ = leanh::lean_box(0);
                        v_isShared_568_ = v_isSharedCheck_577_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_569_ = leanh::lean_box(0);
                v___x_570_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_570_, 0, v___x_559_);
                leanh::lean_ctor_set(v___x_570_, 1, v_sccs_565_);
                if v_isShared_568_ == 0 {
                    leanh::lean_ctor_set(v___x_567_, 3, v___x_570_);
                    leanh::lean_ctor_set(v___x_567_, 0, v_tail_549_);
                    v___x_572_ = v___x_567_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_tail_549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 1, v_nextIndex_563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 2, v_data_564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 3, v___x_570_);
                    v___x_572_ = v_reuseFailAlloc_576_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_557_ == 0 {
                    leanh::lean_ctor_set(v___x_556_, 1, v___x_572_);
                    leanh::lean_ctor_set(v___x_556_, 0, v___x_569_);
                    v___x_574_ = v___x_556_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
                    v___x_574_ = v_reuseFailAlloc_575_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add(
    mut v_00_u03b1_583_: *mut leanh::LeanObject,
    mut v_inst_584_: *mut leanh::LeanObject,
    mut v_inst_585_: *mut leanh::LeanObject,
    mut v_a_586_: *mut leanh::LeanObject,
    mut v_x_587_: *mut leanh::LeanObject,
    mut v_x_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(
        v_inst_584_,
        v_inst_585_,
        v_a_586_,
        v_x_587_,
        v_x_588_,
        v_a_589_,
    );
    return v___x_590_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(
    mut v_inst_591_: *mut leanh::LeanObject,
    mut v_inst_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
    mut v_a_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stack_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stack_595_ = leanh::lean_ctor_get(v_a_594_, 0);
    leanh::lean_inc(v_stack_595_);
    v___x_596_ = leanh::lean_box(0);
    v___x_597_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___redArg(
        v_inst_591_,
        v_inst_592_,
        v_a_593_,
        v_stack_595_,
        v___x_596_,
        v_a_594_,
    );
    return v___x_597_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_addSCC(
    mut v_00_u03b1_598_: *mut leanh::LeanObject,
    mut v_inst_599_: *mut leanh::LeanObject,
    mut v_inst_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(
        v_inst_599_,
        v_inst_600_,
        v_a_601_,
        v_a_602_,
    );
    return v___x_603_;
}
pub unsafe fn _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = leanh::lean_alloc_closure(
        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_650_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_650_, 0, v___x_649_);
    return v___f_650_;
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_inst_652_: *mut leanh::LeanObject,
    mut v_successorsOf_653_: *mut leanh::LeanObject,
    mut v_a_654_: *mut leanh::LeanObject,
    mut v_a_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010__overap_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v_index_x3f_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: u8 = 0;
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_656_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19;
                leanh::lean_inc_n(v_a_654_, 4);
                leanh::lean_inc_ref_n(v_inst_652_, 3);
                leanh::lean_inc_ref_n(v_inst_651_, 3);
                v___x_657_ = l___private_Lean_Util_SCC_0__Lean_SCC_push___redArg(
                    v_inst_651_,
                    v_inst_652_,
                    v_a_654_,
                    v_a_655_,
                );
                v_snd_658_ = leanh::lean_ctor_get(v___x_657_, 1);
                leanh::lean_inc(v_snd_658_);
                leanh::lean_dec_ref(v___x_657_);
                leanh::lean_inc_ref(v_successorsOf_653_);
                v___f_659_ = leanh::lean_alloc_closure(
                    l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_659_, 0, v_inst_651_);
                leanh::lean_closure_set(v___f_659_, 1, v_inst_652_);
                leanh::lean_closure_set(v___f_659_, 2, v_successorsOf_653_);
                leanh::lean_closure_set(v___f_659_, 3, v_a_654_);
                v___x_660_ = leanh::lean_apply_1(v_successorsOf_653_, v_a_654_);
                v___x_1010__overap_661_ = l_List_forM___redArg(v___x_656_, v___x_660_, v___f_659_);
                v___x_662_ = leanh::lean_apply_1(v___x_1010__overap_661_, v_snd_658_);
                v_snd_663_ = leanh::lean_ctor_get(v___x_662_, 1);
                leanh::lean_inc(v_snd_663_);
                leanh::lean_dec_ref(v___x_662_);
                v___x_664_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
                    v_inst_651_,
                    v_inst_652_,
                    v_a_654_,
                    v_snd_663_,
                );
                v_fst_665_ = leanh::lean_ctor_get(v___x_664_, 0);
                v_snd_666_ = leanh::lean_ctor_get(v___x_664_, 1);
                v_isSharedCheck_679_ = (!leanh::lean_is_exclusive(v___x_664_)) as u8;
                if v_isSharedCheck_679_ == 0 {
                    v___x_668_ = v___x_664_;
                    v_isShared_669_ = v_isSharedCheck_679_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_666_);
                    leanh::lean_inc(v_fst_665_);
                    leanh::lean_dec(v___x_664_);
                    v___x_668_ = leanh::lean_box(0);
                    v_isShared_669_ = v_isSharedCheck_679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_index_x3f_670_ = leanh::lean_ctor_get(v_fst_665_, 0);
                leanh::lean_inc(v_index_x3f_670_);
                v_lowlink_x3f_671_ = leanh::lean_ctor_get(v_fst_665_, 1);
                leanh::lean_inc(v_lowlink_x3f_671_);
                leanh::lean_dec(v_fst_665_);
                v___f_672_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20_once
                    ),
                    _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__20,
                );
                v___x_673_ =
                    l_Option_instBEq_beq___redArg(v___f_672_, v_lowlink_x3f_671_, v_index_x3f_670_);
                if v___x_673_ == 0 {
                    leanh::lean_dec(v_a_654_);
                    leanh::lean_dec_ref(v_inst_652_);
                    leanh::lean_dec_ref(v_inst_651_);
                    v___x_674_ = leanh::lean_box(0);
                    if v_isShared_669_ == 0 {
                        leanh::lean_ctor_set(v___x_668_, 0, v___x_674_);
                        v___x_676_ = v___x_668_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_677_, 1, v_snd_666_);
                        v___x_676_ = v_reuseFailAlloc_677_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_668_);
                    v___x_678_ = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___redArg(
                        v_inst_651_,
                        v_inst_652_,
                        v_a_654_,
                        v_snd_666_,
                    );
                    return v___x_678_;
                }
            }
            2 => {
                return v___x_676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___lam__0(
    mut v_inst_680_: *mut leanh::LeanObject,
    mut v_inst_681_: *mut leanh::LeanObject,
    mut v_successorsOf_682_: *mut leanh::LeanObject,
    mut v_a_683_: *mut leanh::LeanObject,
    mut v_b_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowlink_x3f_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onStack_697_: u8 = 0;
    let mut v_snd_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_701_: u8 = 0;
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut v_unused_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_b_684_);
                leanh::lean_inc_ref(v_inst_681_);
                leanh::lean_inc_ref(v_inst_680_);
                v___x_686_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
                    v_inst_680_,
                    v_inst_681_,
                    v_b_684_,
                    v___y_685_,
                );
                v_fst_687_ = leanh::lean_ctor_get(v___x_686_, 0);
                leanh::lean_inc(v_fst_687_);
                v_index_x3f_688_ = leanh::lean_ctor_get(v_fst_687_, 0);
                leanh::lean_inc(v_index_x3f_688_);
                if leanh::lean_obj_tag(v_index_x3f_688_) == 0 {
                    leanh::lean_dec(v_fst_687_);
                    v_snd_689_ = leanh::lean_ctor_get(v___x_686_, 1);
                    leanh::lean_inc(v_snd_689_);
                    leanh::lean_dec_ref(v___x_686_);
                    leanh::lean_inc(v_b_684_);
                    leanh::lean_inc_ref_n(v_inst_681_, 2);
                    leanh::lean_inc_ref_n(v_inst_680_, 2);
                    v___x_690_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(
                        v_inst_680_,
                        v_inst_681_,
                        v_successorsOf_682_,
                        v_b_684_,
                        v_snd_689_,
                    );
                    v_snd_691_ = leanh::lean_ctor_get(v___x_690_, 1);
                    leanh::lean_inc(v_snd_691_);
                    leanh::lean_dec_ref(v___x_690_);
                    v___x_692_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
                        v_inst_680_,
                        v_inst_681_,
                        v_b_684_,
                        v_snd_691_,
                    );
                    v_fst_693_ = leanh::lean_ctor_get(v___x_692_, 0);
                    leanh::lean_inc(v_fst_693_);
                    v_snd_694_ = leanh::lean_ctor_get(v___x_692_, 1);
                    leanh::lean_inc(v_snd_694_);
                    leanh::lean_dec_ref(v___x_692_);
                    v_lowlink_x3f_695_ = leanh::lean_ctor_get(v_fst_693_, 1);
                    leanh::lean_inc(v_lowlink_x3f_695_);
                    leanh::lean_dec(v_fst_693_);
                    v___x_696_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(
                        v_inst_680_,
                        v_inst_681_,
                        v_a_683_,
                        v_lowlink_x3f_695_,
                        v_snd_694_,
                    );
                    return v___x_696_;
                } else {
                    leanh::lean_dec(v_b_684_);
                    leanh::lean_dec_ref(v_successorsOf_682_);
                    v_onStack_697_ = leanh::lean_ctor_get_uint8(
                        v_fst_687_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v_fst_687_);
                    if v_onStack_697_ == 0 {
                        leanh::lean_dec_ref_known(v_index_x3f_688_, 1);
                        leanh::lean_dec(v_a_683_);
                        leanh::lean_dec_ref(v_inst_681_);
                        leanh::lean_dec_ref(v_inst_680_);
                        v_snd_698_ = leanh::lean_ctor_get(v___x_686_, 1);
                        v_isSharedCheck_706_ = (!leanh::lean_is_exclusive(v___x_686_)) as u8;
                        if v_isSharedCheck_706_ == 0 {
                            v_unused_707_ = leanh::lean_ctor_get(v___x_686_, 0);
                            leanh::lean_dec(v_unused_707_);
                            v___x_700_ = v___x_686_;
                            v_isShared_701_ = v_isSharedCheck_706_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_698_);
                            leanh::lean_dec(v___x_686_);
                            v___x_700_ = leanh::lean_box(0);
                            v_isShared_701_ = v_isSharedCheck_706_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_snd_708_ = leanh::lean_ctor_get(v___x_686_, 1);
                        leanh::lean_inc(v_snd_708_);
                        leanh::lean_dec_ref(v___x_686_);
                        v___x_709_ = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___redArg(
                            v_inst_680_,
                            v_inst_681_,
                            v_a_683_,
                            v_index_x3f_688_,
                            v_snd_708_,
                        );
                        return v___x_709_;
                    }
                }
            }
            1 => {
                v___x_702_ = leanh::lean_box(0);
                if v_isShared_701_ == 0 {
                    leanh::lean_ctor_set(v___x_700_, 0, v___x_702_);
                    v___x_704_ = v___x_700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_705_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_705_, 1, v_snd_698_);
                    v___x_704_ = v_reuseFailAlloc_705_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_SCC_0__Lean_SCC_sccAux(
    mut v_00_u03b1_710_: *mut leanh::LeanObject,
    mut v_inst_711_: *mut leanh::LeanObject,
    mut v_inst_712_: *mut leanh::LeanObject,
    mut v_successorsOf_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(
        v_inst_711_,
        v_inst_712_,
        v_successorsOf_713_,
        v_a_714_,
        v_a_715_,
    );
    return v___x_716_;
}
pub unsafe fn l_Lean_SCC_scc___redArg___lam__0(
    mut v_inst_717_: *mut leanh::LeanObject,
    mut v_inst_718_: *mut leanh::LeanObject,
    mut v_successorsOf_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v___y_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_x3f_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut v_unused_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_720_);
                leanh::lean_inc_ref(v_inst_718_);
                leanh::lean_inc_ref(v_inst_717_);
                v___x_722_ = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___redArg(
                    v_inst_717_,
                    v_inst_718_,
                    v_a_720_,
                    v___y_721_,
                );
                v_fst_723_ = leanh::lean_ctor_get(v___x_722_, 0);
                leanh::lean_inc(v_fst_723_);
                v_index_x3f_724_ = leanh::lean_ctor_get(v_fst_723_, 0);
                leanh::lean_inc(v_index_x3f_724_);
                leanh::lean_dec(v_fst_723_);
                if leanh::lean_obj_tag(v_index_x3f_724_) == 0 {
                    v_snd_725_ = leanh::lean_ctor_get(v___x_722_, 1);
                    leanh::lean_inc(v_snd_725_);
                    leanh::lean_dec_ref(v___x_722_);
                    v___x_726_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg(
                        v_inst_717_,
                        v_inst_718_,
                        v_successorsOf_719_,
                        v_a_720_,
                        v_snd_725_,
                    );
                    return v___x_726_;
                } else {
                    leanh::lean_dec_ref_known(v_index_x3f_724_, 1);
                    leanh::lean_dec(v_a_720_);
                    leanh::lean_dec_ref(v_successorsOf_719_);
                    leanh::lean_dec_ref(v_inst_718_);
                    leanh::lean_dec_ref(v_inst_717_);
                    v_snd_727_ = leanh::lean_ctor_get(v___x_722_, 1);
                    v_isSharedCheck_735_ = (!leanh::lean_is_exclusive(v___x_722_)) as u8;
                    if v_isSharedCheck_735_ == 0 {
                        v_unused_736_ = leanh::lean_ctor_get(v___x_722_, 0);
                        leanh::lean_dec(v_unused_736_);
                        v___x_729_ = v___x_722_;
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_727_);
                        leanh::lean_dec(v___x_722_);
                        v___x_729_ = leanh::lean_box(0);
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_731_ = leanh::lean_box(0);
                if v_isShared_730_ == 0 {
                    leanh::lean_ctor_set(v___x_729_, 0, v___x_731_);
                    v___x_733_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 1, v_snd_727_);
                    v___x_733_ = v_reuseFailAlloc_734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_SCC_scc___redArg___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = leanh::lean_box(0);
    v___x_738_ = leanh::lean_unsigned_to_nat(16);
    v___x_739_ = lean_mk_array(v___x_738_, v___x_737_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lean_SCC_scc___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__0_once),
        _init_l_Lean_SCC_scc___redArg___closed__0,
    );
    v___x_741_ = leanh::lean_unsigned_to_nat(0);
    v___x_742_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_742_, 0, v___x_741_);
    leanh::lean_ctor_set(v___x_742_, 1, v___x_740_);
    return v___x_742_;
}
pub unsafe fn _init_l_Lean_SCC_scc___redArg___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__1_once),
        _init_l_Lean_SCC_scc___redArg___closed__1,
    );
    v___x_744_ = leanh::lean_unsigned_to_nat(0);
    v___x_745_ = leanh::lean_box(0);
    v___x_746_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_746_, 0, v___x_745_);
    leanh::lean_ctor_set(v___x_746_, 1, v___x_744_);
    leanh::lean_ctor_set(v___x_746_, 2, v___x_743_);
    leanh::lean_ctor_set(v___x_746_, 3, v___x_745_);
    return v___x_746_;
}
pub unsafe fn l_Lean_SCC_scc___redArg(
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_inst_748_: *mut leanh::LeanObject,
    mut v_vertices_749_: *mut leanh::LeanObject,
    mut v_successorsOf_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385__overap_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sccs_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_751_ = leanh::lean_alloc_closure(
        l_Lean_SCC_scc___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_751_, 0, v_inst_747_);
    leanh::lean_closure_set(v___f_751_, 1, v_inst_748_);
    leanh::lean_closure_set(v___f_751_, 2, v_successorsOf_750_);
    v___x_752_ = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___redArg___closed__19;
    v___x_753_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_SCC_scc___redArg___closed__2_once),
        _init_l_Lean_SCC_scc___redArg___closed__2,
    );
    v___x_385__overap_754_ = l_List_forM___redArg(v___x_752_, v_vertices_749_, v___f_751_);
    v___x_755_ = leanh::lean_apply_1(v___x_385__overap_754_, v___x_753_);
    v_snd_756_ = leanh::lean_ctor_get(v___x_755_, 1);
    leanh::lean_inc(v_snd_756_);
    leanh::lean_dec_ref(v___x_755_);
    v_sccs_757_ = leanh::lean_ctor_get(v_snd_756_, 3);
    leanh::lean_inc(v_sccs_757_);
    leanh::lean_dec(v_snd_756_);
    v___x_758_ = l_List_reverse___redArg(v_sccs_757_);
    return v___x_758_;
}
pub unsafe fn l_Lean_SCC_scc(
    mut v_00_u03b1_759_: *mut leanh::LeanObject,
    mut v_inst_760_: *mut leanh::LeanObject,
    mut v_inst_761_: *mut leanh::LeanObject,
    mut v_vertices_762_: *mut leanh::LeanObject,
    mut v_successorsOf_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Lean_SCC_scc___redArg(
        v_inst_760_,
        v_inst_761_,
        v_vertices_762_,
        v_successorsOf_763_,
    );
    return v___x_764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_SCC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_SCC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_SCC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SCC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_SCC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_SCC(builtin);
}