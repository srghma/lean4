// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Basic
// Imports: Lean.Meta.ForEachExpr
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg___boxed,
    l_Array_instInhabited, l_Array_isEqvAux___redArg, l_Array_range, l_Array_zipWithMAux___redArg,
};
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt___boxed;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Nat_decEq___boxed, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isAppOf,
};
use crate::r#gen::Lean::Meta::ForEachExpr::{
    initialize_Lean_Meta_ForEachExpr, runtime_initialize_Lean_Meta_ForEachExpr,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__7_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116,
        105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 66, 97, 115, 105, 99,
        0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108,
        46, 80, 111, 115, 105, 116, 105, 111, 110, 115, 46, 103, 114, 111, 117, 112, 65, 110, 100,
        83, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value:
    crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 79,
    m_capacity: 79,
    m_length: 78,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 65, 114, 114, 97, 121, 46, 114, 97, 110, 103, 101, 32, 120, 115, 46, 115, 105, 122,
        101, 32, 61, 61, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 102, 108, 97, 116,
        116, 101, 110, 46, 113, 115, 111, 114, 116, 32, 78, 97, 116, 46, 98, 108, 116, 10, 32, 32,
        0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value:
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
    m_fun: l_Nat_decEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value:
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
    m_fun: l_Nat_blt___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value:
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
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value:
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
    m_fun: l_Array_append___redArg___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108,
        46, 80, 111, 115, 105, 116, 105, 111, 110, 115, 46, 109, 97, 112, 77, 119, 105, 116, 104,
        0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 115, 105, 122, 101, 32, 61, 32,
        121, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value:
    crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 112, 111, 115, 105, 116, 105, 111, 110, 115, 46, 110, 117, 109, 73, 110, 100, 105,
        99, 101, 115, 32, 61, 32, 120, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value:
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
static mut l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6897119537390546559 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14406337792964512117 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13137517462150097927 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12626132471895931337 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13654521671067000126 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9807102839232842375 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,521675044554151734 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12511094988777517575 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2877139833357715066 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7571840887366567224 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2190320298132512551 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1645003010576900649 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10689395642969904926 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2093547783 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1351251855787739013 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3046785150952533782 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7324067734669508202 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__29_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9807608616392736339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(
    mut v_recArgPos_351_: *mut crate::leanh::LeanObject,
    mut v_recFnName_352_: *mut crate::leanh::LeanObject,
    mut v_e_353_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_355_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    let mut v___x_362_: u8 = 0;
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_362_ = l_Lean_Expr_isAppOf(v_e_353_, v_recFnName_352_);
                if v___x_362_ == 0 {
                    v___y_355_ = v___x_362_;
                    state = 1;
                    continue;
                } else {
                    v___x_363_ = l_Lean_Expr_getAppNumArgs(v_e_353_);
                    v___x_364_ = lean_nat_dec_lt(v_recArgPos_351_, v___x_363_);
                    crate::leanh::lean_dec(v___x_363_);
                    v___y_355_ = v___x_364_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_355_ == 0 {
                    return v___y_355_;
                } else {
                    v___x_356_ = l_Lean_Expr_getAppNumArgs(v_e_353_);
                    v___x_357_ = lean_nat_sub(v___x_356_, v_recArgPos_351_);
                    crate::leanh::lean_dec(v___x_356_);
                    v___x_358_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_359_ = lean_nat_sub(v___x_357_, v___x_358_);
                    crate::leanh::lean_dec(v___x_357_);
                    v___x_360_ = l_Lean_Expr_getRevArg_x21(v_e_353_, v___x_359_);
                    v___x_361_ = l_Lean_Expr_hasLooseBVars(v___x_360_);
                    crate::leanh::lean_dec_ref(v___x_360_);
                    return v___x_361_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed(
    mut v_recArgPos_365_: *mut crate::leanh::LeanObject,
    mut v_recFnName_366_: *mut crate::leanh::LeanObject,
    mut v_e_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: u8 = 0;
    let mut v_r_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0(
        v_recArgPos_365_,
        v_recFnName_366_,
        v_e_367_,
    );
    crate::leanh::lean_dec_ref(v_e_367_);
    crate::leanh::lean_dec(v_recFnName_366_);
    crate::leanh::lean_dec(v_recArgPos_365_);
    v_r_369_ = crate::leanh::lean_box((v_res_368_) as usize);
    return v_r_369_;
}
pub unsafe fn l_Lean_Elab_Structural_recArgHasLooseBVarsAt(
    mut v_recFnName_370_: *mut crate::leanh::LeanObject,
    mut v_recArgPos_371_: *mut crate::leanh::LeanObject,
    mut v_e_372_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_app_x3f_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_373_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_recArgHasLooseBVarsAt___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_373_, 0, v_recArgPos_371_);
    crate::leanh::lean_closure_set(v___f_373_, 1, v_recFnName_370_);
    v_app_x3f_374_ = lean_find_expr(v___f_373_, v_e_372_);
    crate::leanh::lean_dec_ref(v___f_373_);
    if crate::leanh::lean_obj_tag(v_app_x3f_374_) == 0 {
        let mut v___x_375_: u8 = 0;
        v___x_375_ = 0;
        return v___x_375_;
    } else {
        let mut v___x_376_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_app_x3f_374_, 1);
        v___x_376_ = 1;
        return v___x_376_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(
    mut v_recFnName_377_: *mut crate::leanh::LeanObject,
    mut v_recArgPos_378_: *mut crate::leanh::LeanObject,
    mut v_e_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_380_: u8 = 0;
    let mut v_r_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ =
        l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_recFnName_377_, v_recArgPos_378_, v_e_379_);
    crate::leanh::lean_dec_ref(v_e_379_);
    v_r_381_ = crate::leanh::lean_box((v_res_380_) as usize);
    return v_r_381_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(
    mut v_as_382_: *mut crate::leanh::LeanObject,
    mut v_i_383_: usize,
    mut v_stop_384_: usize,
    mut v_b_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_386_: u8 = 0;
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: usize = 0;
    let mut v___x_391_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_386_ = lean_usize_dec_eq(v_i_383_, v_stop_384_);
                if v___x_386_ == 0 {
                    v___x_387_ = lean_array_uget_borrowed(v_as_382_, v_i_383_);
                    v___x_388_ = lean_array_get_size(v___x_387_);
                    v___x_389_ = lean_nat_add(v_b_385_, v___x_388_);
                    crate::leanh::lean_dec(v_b_385_);
                    v___x_390_ = 1usize;
                    v___x_391_ = lean_usize_add(v_i_383_, v___x_390_);
                    v_i_383_ = v___x_391_;
                    v_b_385_ = v___x_389_;
                    state = 0;
                    continue;
                } else {
                    return v_b_385_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0___boxed(
    mut v_as_393_: *mut crate::leanh::LeanObject,
    mut v_i_394_: *mut crate::leanh::LeanObject,
    mut v_stop_395_: *mut crate::leanh::LeanObject,
    mut v_b_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_397_: usize = 0;
    let mut v_stop_boxed_398_: usize = 0;
    let mut v_res_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_397_ = crate::leanh::lean_unbox_usize(v_i_394_);
    crate::leanh::lean_dec(v_i_394_);
    v_stop_boxed_398_ = crate::leanh::lean_unbox_usize(v_stop_395_);
    crate::leanh::lean_dec(v_stop_395_);
    v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_as_393_, v_i_boxed_397_, v_stop_boxed_398_, v_b_396_);
    crate::leanh::lean_dec_ref(v_as_393_);
    return v_res_399_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_numIndices(
    mut v_positions_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    v___x_401_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_402_ = lean_array_get_size(v_positions_400_);
    v___x_403_ = lean_nat_dec_lt(v___x_401_, v___x_402_);
    if v___x_403_ == 0 {
        return v___x_401_;
    } else {
        let mut v___x_404_: u8 = 0;
        v___x_404_ = lean_nat_dec_le(v___x_402_, v___x_402_);
        if v___x_404_ == 0 {
            if v___x_403_ == 0 {
                return v___x_401_;
            } else {
                let mut v___x_405_: usize = 0;
                let mut v___x_406_: usize = 0;
                let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_405_ = 0usize;
                v___x_406_ = lean_usize_of_nat(v___x_402_);
                v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_400_, v___x_405_, v___x_406_, v___x_401_);
                return v___x_407_;
            }
        } else {
            let mut v___x_408_: usize = 0;
            let mut v___x_409_: usize = 0;
            let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_408_ = 0usize;
            v___x_409_ = lean_usize_of_nat(v___x_402_);
            v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_Positions_numIndices_spec__0(v_positions_400_, v___x_408_, v___x_409_, v___x_401_);
            return v___x_410_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_numIndices___boxed(
    mut v_positions_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_412_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_411_);
    crate::leanh::lean_dec_ref(v_positions_411_);
    return v_res_412_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(
    mut v_inst_413_: *mut crate::leanh::LeanObject,
    mut v_xs_414_: *mut crate::leanh::LeanObject,
    mut v_f_415_: *mut crate::leanh::LeanObject,
    mut v_inst_416_: *mut crate::leanh::LeanObject,
    mut v_x_417_: *mut crate::leanh::LeanObject,
    mut v_x1_418_: *mut crate::leanh::LeanObject,
    mut v_x2_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    v___x_420_ = lean_array_get_borrowed(v_inst_413_, v_xs_414_, v_x2_419_);
    crate::leanh::lean_inc(v___x_420_);
    v___x_421_ = crate::leanh::lean_apply_1(v_f_415_, v___x_420_);
    v___x_422_ = crate::leanh::lean_apply_2(v_inst_416_, v___x_421_, v_x_417_);
    v___x_423_ = (crate::leanh::lean_unbox(v___x_422_) as u8);
    if v___x_423_ == 0 {
        crate::leanh::lean_dec(v_x2_419_);
        return v_x1_418_;
    } else {
        let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_424_ = lean_array_push(v_x1_418_, v_x2_419_);
        return v___x_424_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed(
    mut v_inst_425_: *mut crate::leanh::LeanObject,
    mut v_xs_426_: *mut crate::leanh::LeanObject,
    mut v_f_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_x_429_: *mut crate::leanh::LeanObject,
    mut v_x1_430_: *mut crate::leanh::LeanObject,
    mut v_x2_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_432_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0(
        v_inst_425_,
        v_xs_426_,
        v_f_427_,
        v_inst_428_,
        v_x_429_,
        v_x1_430_,
        v_x2_431_,
    );
    crate::leanh::lean_dec_ref(v_xs_426_);
    crate::leanh::lean_dec(v_inst_425_);
    return v_res_432_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1(
    mut v_xs_454_: *mut crate::leanh::LeanObject,
    mut v_inst_455_: *mut crate::leanh::LeanObject,
    mut v_f_456_: *mut crate::leanh::LeanObject,
    mut v_inst_457_: *mut crate::leanh::LeanObject,
    mut v_x_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    v___x_459_ = lean_array_get_size(v_xs_454_);
    v___x_460_ = l_Array_range(v___x_459_);
    v___x_461_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_462_ = lean_array_get_size(v___x_460_);
    v___x_463_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__0;
    v___x_464_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10;
    v___x_465_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
    if v___x_465_ == 0 {
        crate::leanh::lean_dec_ref(v___x_460_);
        crate::leanh::lean_dec(v_x_458_);
        crate::leanh::lean_dec_ref(v_inst_457_);
        crate::leanh::lean_dec(v_f_456_);
        crate::leanh::lean_dec(v_inst_455_);
        crate::leanh::lean_dec_ref(v_xs_454_);
        return v___x_463_;
    } else {
        let mut v___f_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_467_: u8 = 0;
        v___f_466_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            7,
            5,
        );
        crate::leanh::lean_closure_set(v___f_466_, 0, v_inst_455_);
        crate::leanh::lean_closure_set(v___f_466_, 1, v_xs_454_);
        crate::leanh::lean_closure_set(v___f_466_, 2, v_f_456_);
        crate::leanh::lean_closure_set(v___f_466_, 3, v_inst_457_);
        crate::leanh::lean_closure_set(v___f_466_, 4, v_x_458_);
        v___x_467_ = lean_nat_dec_le(v___x_462_, v___x_462_);
        if v___x_467_ == 0 {
            if v___x_465_ == 0 {
                crate::leanh::lean_dec_ref(v___f_466_);
                crate::leanh::lean_dec_ref(v___x_460_);
                return v___x_463_;
            } else {
                let mut v___x_468_: usize = 0;
                let mut v___x_469_: usize = 0;
                let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_468_ = 0usize;
                v___x_469_ = lean_usize_of_nat(v___x_462_);
                v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_464_,
                    v___f_466_,
                    v___x_460_,
                    v___x_468_,
                    v___x_469_,
                    v___x_463_,
                );
                return v___x_470_;
            }
        } else {
            let mut v___x_471_: usize = 0;
            let mut v___x_472_: usize = 0;
            let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_471_ = 0usize;
            v___x_472_ = lean_usize_of_nat(v___x_462_);
            v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_464_,
                v___f_466_,
                v___x_460_,
                v___x_471_,
                v___x_472_,
                v___x_463_,
            );
            return v___x_473_;
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_474_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__3;
    v___x_479_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_480_ = crate::leanh::lean_unsigned_to_nat(63);
    v___x_481_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__2;
    v___x_482_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1;
    v___x_483_ =
        l_mkPanicMessageWithDecl(v___x_482_, v___x_481_, v___x_480_, v___x_479_, v___x_478_);
    return v___x_483_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort___redArg(
    mut v_inst_489_: *mut crate::leanh::LeanObject,
    mut v_inst_490_: *mut crate::leanh::LeanObject,
    mut v_f_491_: *mut crate::leanh::LeanObject,
    mut v_xs_492_: *mut crate::leanh::LeanObject,
    mut v_ys_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_501_: usize = 0;
    let mut v___x_502_: usize = 0;
    let mut v_positions_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: u8 = 0;
    let mut v___x_511_: u8 = 0;
    let mut v___y_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v___y_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u8 = 0;
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___f_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: usize = 0;
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: usize = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_498_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_xs_492_);
                v___f_499_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1
                        as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_499_, 0, v_xs_492_);
                crate::leanh::lean_closure_set(v___f_499_, 1, v_inst_489_);
                crate::leanh::lean_closure_set(v___f_499_, 2, v_f_491_);
                crate::leanh::lean_closure_set(v___f_499_, 3, v_inst_490_);
                v___x_500_ =
                    l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10;
                v_sz_501_ = lean_array_size(v_ys_493_);
                v___x_502_ = 0usize;
                v_positions_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_500_,
                    v___f_499_,
                    v_sz_501_,
                    v___x_502_,
                    v_ys_493_,
                );
                v___x_504_ = lean_array_get_size(v_xs_492_);
                crate::leanh::lean_dec_ref(v_xs_492_);
                v___x_505_ = l_Array_range(v___x_504_);
                v___x_535_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_536_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__7;
                v___x_537_ = lean_array_get_size(v_positions_503_);
                v___x_538_ = lean_nat_dec_lt(v___x_535_, v___x_537_);
                if v___x_538_ == 0 {
                    v___y_527_ = v___x_536_;
                    state = 5;
                    continue;
                } else {
                    v___f_539_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__8;
                    v___x_540_ = lean_nat_dec_le(v___x_537_, v___x_537_);
                    if v___x_540_ == 0 {
                        if v___x_538_ == 0 {
                            v___y_527_ = v___x_536_;
                            state = 5;
                            continue;
                        } else {
                            v___x_541_ = lean_usize_of_nat(v___x_537_);
                            crate::leanh::lean_inc(v_positions_503_);
                            v___x_542_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_500_,
                                    v___f_539_,
                                    v_positions_503_,
                                    v___x_502_,
                                    v___x_541_,
                                    v___x_536_,
                                );
                            v___y_527_ = v___x_542_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_543_ = lean_usize_of_nat(v___x_537_);
                        crate::leanh::lean_inc(v_positions_503_);
                        v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_500_,
                            v___f_539_,
                            v_positions_503_,
                            v___x_502_,
                            v___x_543_,
                            v___x_536_,
                        );
                        v___y_527_ = v___x_544_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_495_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0_once
                    ),
                    _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__0,
                );
                v___x_496_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4_once
                    ),
                    _init_l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__4,
                );
                v___x_497_ = l_panic___redArg(v___x_495_, v___x_496_);
                return v___x_497_;
            }
            2 => {
                v___x_508_ = lean_array_get_size(v___x_505_);
                v___x_509_ = lean_array_get_size(v___y_507_);
                v___x_510_ = lean_nat_dec_eq(v___x_508_, v___x_509_);
                if v___x_510_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_507_);
                    crate::leanh::lean_dec_ref(v___x_505_);
                    crate::leanh::lean_dec(v_positions_503_);
                    state = 1;
                    continue;
                } else {
                    v___x_511_ =
                        l_Array_isEqvAux___redArg(v___x_505_, v___y_507_, v___f_498_, v___x_508_);
                    crate::leanh::lean_dec_ref(v___y_507_);
                    crate::leanh::lean_dec_ref(v___x_505_);
                    if v___x_511_ == 0 {
                        crate::leanh::lean_dec(v_positions_503_);
                        state = 1;
                        continue;
                    } else {
                        return v_positions_503_;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___y_513_);
                v___x_518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    crate::leanh::lean_box(0),
                    v___y_513_,
                    v___y_514_,
                    v___y_516_,
                    v___y_515_,
                    v___y_517_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_dec(v___y_517_);
                crate::leanh::lean_dec(v___y_514_);
                v___y_507_ = v___x_518_;
                state = 2;
                continue;
            }
            4 => {
                v___x_525_ = lean_nat_dec_le(v___y_524_, v___y_521_);
                if v___x_525_ == 0 {
                    crate::leanh::lean_dec(v___y_521_);
                    crate::leanh::lean_inc(v___y_524_);
                    v___y_513_ = v___y_520_;
                    v___y_514_ = v___y_522_;
                    v___y_515_ = v___y_524_;
                    v___y_516_ = v___y_523_;
                    v___y_517_ = v___y_524_;
                    state = 3;
                    continue;
                } else {
                    v___y_513_ = v___y_520_;
                    v___y_514_ = v___y_522_;
                    v___y_515_ = v___y_524_;
                    v___y_516_ = v___y_523_;
                    v___y_517_ = v___y_521_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_528_ = lean_array_get_size(v___y_527_);
                v___x_529_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_530_ = lean_nat_dec_eq(v___x_528_, v___x_529_);
                if v___x_530_ == 0 {
                    v___x_531_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__6;
                    v___x_532_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_533_ = lean_nat_sub(v___x_528_, v___x_532_);
                    v___x_534_ = lean_nat_dec_le(v___x_529_, v___x_533_);
                    if v___x_534_ == 0 {
                        crate::leanh::lean_inc(v___x_533_);
                        v___y_520_ = v___x_531_;
                        v___y_521_ = v___x_533_;
                        v___y_522_ = v___x_528_;
                        v___y_523_ = v___y_527_;
                        v___y_524_ = v___x_533_;
                        state = 4;
                        continue;
                    } else {
                        v___y_520_ = v___x_531_;
                        v___y_521_ = v___x_533_;
                        v___y_522_ = v___x_528_;
                        v___y_523_ = v___y_527_;
                        v___y_524_ = v___x_529_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_507_ = v___y_527_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_groupAndSort(
    mut v_00_u03b1_545_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_546_: *mut crate::leanh::LeanObject,
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_inst_548_: *mut crate::leanh::LeanObject,
    mut v_f_549_: *mut crate::leanh::LeanObject,
    mut v_xs_550_: *mut crate::leanh::LeanObject,
    mut v_ys_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg(
        v_inst_547_,
        v_inst_548_,
        v_f_549_,
        v_xs_550_,
        v_ys_551_,
    );
    return v___x_552_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(
    mut v_inst_553_: *mut crate::leanh::LeanObject,
    mut v_xs_554_: *mut crate::leanh::LeanObject,
    mut v_x_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = lean_array_get_borrowed(v_inst_553_, v_xs_554_, v_x_555_);
    crate::leanh::lean_inc(v___x_556_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed(
    mut v_inst_557_: *mut crate::leanh::LeanObject,
    mut v_xs_558_: *mut crate::leanh::LeanObject,
    mut v_x_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0(
        v_inst_557_,
        v_xs_558_,
        v_x_559_,
    );
    crate::leanh::lean_dec(v_x_559_);
    crate::leanh::lean_dec_ref(v_xs_558_);
    crate::leanh::lean_dec(v_inst_557_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1(
    mut v___f_561_: *mut crate::leanh::LeanObject,
    mut v_f_562_: *mut crate::leanh::LeanObject,
    mut v_y_563_: *mut crate::leanh::LeanObject,
    mut v_poss_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_566_: usize = 0;
    let mut v___x_567_: usize = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___lam__1___closed__10;
    v_sz_566_ = lean_array_size(v_poss_564_);
    v___x_567_ = 0usize;
    v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_565_,
        v___f_561_,
        v_sz_566_,
        v___x_567_,
        v_poss_564_,
    );
    v___x_569_ = crate::leanh::lean_apply_2(v_f_562_, v_y_563_, v___x_568_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_570_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__2;
    v___x_574_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_575_ = crate::leanh::lean_unsigned_to_nat(73);
    v___x_576_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1;
    v___x_577_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1;
    v___x_578_ =
        l_mkPanicMessageWithDecl(v___x_577_, v___x_576_, v___x_575_, v___x_574_, v___x_573_);
    return v___x_578_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__4;
    v___x_581_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_582_ = crate::leanh::lean_unsigned_to_nat(74);
    v___x_583_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__1;
    v___x_584_ = l_Lean_Elab_Structural_Positions_groupAndSort___redArg___closed__1;
    v___x_585_ =
        l_mkPanicMessageWithDecl(v___x_584_, v___x_583_, v___x_582_, v___x_581_, v___x_580_);
    return v___x_585_;
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith___redArg(
    mut v_inst_588_: *mut crate::leanh::LeanObject,
    mut v_inst_589_: *mut crate::leanh::LeanObject,
    mut v_f_590_: *mut crate::leanh::LeanObject,
    mut v_positions_591_: *mut crate::leanh::LeanObject,
    mut v_ys_592_: *mut crate::leanh::LeanObject,
    mut v_xs_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: u8 = 0;
    v___x_594_ = lean_array_get_size(v_positions_591_);
    v___x_595_ = lean_array_get_size(v_ys_592_);
    v___x_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
    if v___x_596_ == 0 {
        let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_593_);
        crate::leanh::lean_dec_ref(v_ys_592_);
        crate::leanh::lean_dec_ref(v_positions_591_);
        crate::leanh::lean_dec(v_f_590_);
        crate::leanh::lean_dec(v_inst_589_);
        v___x_597_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once
            ),
            _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0,
        );
        v___x_598_ = l_instInhabitedOfMonad___redArg(v_inst_588_, v___x_597_);
        v___x_599_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3_once
            ),
            _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__3,
        );
        v___x_600_ = l_panic___redArg(v___x_598_, v___x_599_);
        crate::leanh::lean_dec(v___x_598_);
        return v___x_600_;
    } else {
        let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_603_: u8 = 0;
        v___x_601_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_591_);
        v___x_602_ = lean_array_get_size(v_xs_593_);
        v___x_603_ = lean_nat_dec_eq(v___x_601_, v___x_602_);
        crate::leanh::lean_dec(v___x_601_);
        if v___x_603_ == 0 {
            let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_xs_593_);
            crate::leanh::lean_dec_ref(v_ys_592_);
            crate::leanh::lean_dec_ref(v_positions_591_);
            crate::leanh::lean_dec(v_f_590_);
            crate::leanh::lean_dec(v_inst_589_);
            v___x_604_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0_once
                ),
                _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__0,
            );
            v___x_605_ = l_instInhabitedOfMonad___redArg(v_inst_588_, v___x_604_);
            v___x_606_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5_once
                ),
                _init_l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__5,
            );
            v___x_607_ = l_panic___redArg(v___x_605_, v___x_606_);
            crate::leanh::lean_dec(v___x_605_);
            return v___x_607_;
        } else {
            let mut v___f_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_608_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_608_, 0, v_inst_589_);
            crate::leanh::lean_closure_set(v___f_608_, 1, v_xs_593_);
            v___f_609_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Structural_Positions_mapMwith___redArg___lam__1
                    as *mut core::ffi::c_void,
                4,
                2,
            );
            crate::leanh::lean_closure_set(v___f_609_, 0, v___f_608_);
            crate::leanh::lean_closure_set(v___f_609_, 1, v_f_590_);
            v___x_610_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_611_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg___closed__6;
            v___x_612_ = l_Array_zipWithMAux___redArg(
                v_inst_588_,
                v_ys_592_,
                v_positions_591_,
                v___f_609_,
                v___x_610_,
                v___x_611_,
            );
            return v___x_612_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_Positions_mapMwith(
    mut v_00_u03b3_613_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_614_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_615_: *mut crate::leanh::LeanObject,
    mut v_m_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_inst_618_: *mut crate::leanh::LeanObject,
    mut v_f_619_: *mut crate::leanh::LeanObject,
    mut v_positions_620_: *mut crate::leanh::LeanObject,
    mut v_ys_621_: *mut crate::leanh::LeanObject,
    mut v_xs_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_623_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(
        v_inst_617_,
        v_inst_618_,
        v_f_619_,
        v_positions_620_,
        v_ys_621_,
        v_xs_622_,
    );
    return v___x_623_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_;
    v___x_696_ = 0;
    v___x_697_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn___closed__30_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_;
    v___x_698_ = l_Lean_registerTraceClass(v___x_695_, v___x_696_, v___x_697_);
    return v___x_698_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2____boxed(
    mut v_a_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
    return v_res_700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_Structural_Basic_0__initFn_00___x40_Lean_Elab_PreDefinition_Structural_Basic_2093547783____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
}
