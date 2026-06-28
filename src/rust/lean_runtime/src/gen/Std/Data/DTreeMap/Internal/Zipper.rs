// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Zipper
// Imports: Std.Data.Iterators.Lemmas.Producers.Slice Init.Data.Slice Std.Data.DTreeMap.Internal.Lemmas Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Slice.InternalLemmas
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Slice::InternalLemmas::{
    initialize_Init_Data_Slice_InternalLemmas, runtime_initialize_Init_Data_Slice_InternalLemmas,
};
use crate::r#gen::Init::Data::Slice::{
    initialize_Init_Data_Slice, runtime_initialize_Init_Data_Slice,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Def::l_Std_DTreeMap_Internal_Impl_treeSize___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Lemmas::{
    initialize_Std_Data_DTreeMap_Internal_Lemmas,
    runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Slice::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Slice,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
pub static l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Zipper_step___redArg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(
    mut v_inst_1494_: *mut crate::leanh::LeanObject,
    mut v_t_1495_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1495_) == 0 {
                    v_size_1497_ = crate::leanh::lean_ctor_get(v_t_1495_, 0);
                    v_k_1498_ = crate::leanh::lean_ctor_get(v_t_1495_, 1);
                    v_v_1499_ = crate::leanh::lean_ctor_get(v_t_1495_, 2);
                    v_l_1500_ = crate::leanh::lean_ctor_get(v_t_1495_, 3);
                    v_r_1501_ = crate::leanh::lean_ctor_get(v_t_1495_, 4);
                    v_isSharedCheck_1516_ = (!crate::leanh::lean_is_exclusive(v_t_1495_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1503_ = v_t_1495_;
                        v_isShared_1504_ = v_isSharedCheck_1516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1501_);
                        crate::leanh::lean_inc(v_l_1500_);
                        crate::leanh::lean_inc(v_v_1499_);
                        crate::leanh::lean_inc(v_k_1498_);
                        crate::leanh::lean_inc(v_size_1497_);
                        crate::leanh::lean_dec(v_t_1495_);
                        v___x_1503_ = crate::leanh::lean_box(0);
                        v_isShared_1504_ = v_isSharedCheck_1516_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_lowerBound_1496_);
                    crate::leanh::lean_dec_ref(v_inst_1494_);
                    return v_t_1495_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1494_);
                crate::leanh::lean_inc(v_k_1498_);
                crate::leanh::lean_inc(v_lowerBound_1496_);
                v___x_1505_ =
                    crate::leanh::lean_apply_2(v_inst_1494_, v_lowerBound_1496_, v_k_1498_);
                v___x_1506_ = (crate::leanh::lean_unbox(v___x_1505_) as u8);
                match v___x_1506_ {
                    0 => {
                        v___x_1507_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_1494_, v_l_1500_, v_lowerBound_1496_);
                        if v_isShared_1504_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1503_, 3, v___x_1507_);
                            v___x_1509_ = v___x_1503_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1510_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_size_1497_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1498_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1499_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1501_);
                            v___x_1509_ = v_reuseFailAlloc_1510_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_l_1500_);
                        crate::leanh::lean_dec(v_lowerBound_1496_);
                        crate::leanh::lean_dec_ref(v_inst_1494_);
                        v___x_1511_ = crate::leanh::lean_box(1);
                        if v_isShared_1504_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1503_, 3, v___x_1511_);
                            v___x_1513_ = v___x_1503_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1514_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_size_1497_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1498_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1499_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 3, v___x_1511_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1501_);
                            v___x_1513_ = v_reuseFailAlloc_1514_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_1503_);
                        crate::leanh::lean_dec(v_l_1500_);
                        crate::leanh::lean_dec(v_v_1499_);
                        crate::leanh::lean_dec(v_k_1498_);
                        crate::leanh::lean_dec(v_size_1497_);
                        v_t_1495_ = v_r_1501_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1509_;
            }
            3 => {
                return v___x_1513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE(
    mut v_00_u03b1_1517_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1518_: *mut crate::leanh::LeanObject,
    mut v_inst_1519_: *mut crate::leanh::LeanObject,
    mut v_t_1520_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_1519_, v_t_1520_, v_lowerBound_1521_);
    return v___x_1522_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(
    mut v_inst_1523_: *mut crate::leanh::LeanObject,
    mut v_t_1524_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1524_) == 0 {
                    v_size_1526_ = crate::leanh::lean_ctor_get(v_t_1524_, 0);
                    v_k_1527_ = crate::leanh::lean_ctor_get(v_t_1524_, 1);
                    v_v_1528_ = crate::leanh::lean_ctor_get(v_t_1524_, 2);
                    v_l_1529_ = crate::leanh::lean_ctor_get(v_t_1524_, 3);
                    v_r_1530_ = crate::leanh::lean_ctor_get(v_t_1524_, 4);
                    v_isSharedCheck_1541_ = (!crate::leanh::lean_is_exclusive(v_t_1524_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1532_ = v_t_1524_;
                        v_isShared_1533_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1530_);
                        crate::leanh::lean_inc(v_l_1529_);
                        crate::leanh::lean_inc(v_v_1528_);
                        crate::leanh::lean_inc(v_k_1527_);
                        crate::leanh::lean_inc(v_size_1526_);
                        crate::leanh::lean_dec(v_t_1524_);
                        v___x_1532_ = crate::leanh::lean_box(0);
                        v_isShared_1533_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_lowerBound_1525_);
                    crate::leanh::lean_dec_ref(v_inst_1523_);
                    return v_t_1524_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1523_);
                crate::leanh::lean_inc(v_k_1527_);
                crate::leanh::lean_inc(v_lowerBound_1525_);
                v___x_1534_ =
                    crate::leanh::lean_apply_2(v_inst_1523_, v_lowerBound_1525_, v_k_1527_);
                v___x_1535_ = (crate::leanh::lean_unbox(v___x_1534_) as u8);
                match v___x_1535_ {
                    0 => {
                        v___x_1536_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_1523_, v_l_1529_, v_lowerBound_1525_);
                        if v_isShared_1533_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1532_, 3, v___x_1536_);
                            v___x_1538_ = v___x_1532_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1539_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_size_1526_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1527_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1528_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 3, v___x_1536_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1530_);
                            v___x_1538_ = v_reuseFailAlloc_1539_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_1532_);
                        crate::leanh::lean_dec(v_l_1529_);
                        crate::leanh::lean_dec(v_v_1528_);
                        crate::leanh::lean_dec(v_k_1527_);
                        crate::leanh::lean_dec(v_size_1526_);
                        crate::leanh::lean_dec(v_lowerBound_1525_);
                        crate::leanh::lean_dec_ref(v_inst_1523_);
                        return v_r_1530_;
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_1532_);
                        crate::leanh::lean_dec(v_l_1529_);
                        crate::leanh::lean_dec(v_v_1528_);
                        crate::leanh::lean_dec(v_k_1527_);
                        crate::leanh::lean_dec(v_size_1526_);
                        v_t_1524_ = v_r_1530_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT(
    mut v_00_u03b1_1542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_t_1545_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_1544_, v_t_1545_, v_lowerBound_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(
    mut v_t_1548_: *mut crate::leanh::LeanObject,
    mut v_h__1_1549_: *mut crate::leanh::LeanObject,
    mut v_h__2_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1548_) == 0 {
        let mut v_size_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1549_);
        v_size_1551_ = crate::leanh::lean_ctor_get(v_t_1548_, 0);
        crate::leanh::lean_inc(v_size_1551_);
        v_k_1552_ = crate::leanh::lean_ctor_get(v_t_1548_, 1);
        crate::leanh::lean_inc(v_k_1552_);
        v_v_1553_ = crate::leanh::lean_ctor_get(v_t_1548_, 2);
        crate::leanh::lean_inc(v_v_1553_);
        v_l_1554_ = crate::leanh::lean_ctor_get(v_t_1548_, 3);
        crate::leanh::lean_inc(v_l_1554_);
        v_r_1555_ = crate::leanh::lean_ctor_get(v_t_1548_, 4);
        crate::leanh::lean_inc(v_r_1555_);
        crate::leanh::lean_dec_ref_known(v_t_1548_, 5);
        v___x_1556_ = crate::leanh::lean_apply_5(
            v_h__2_1550_,
            v_size_1551_,
            v_k_1552_,
            v_v_1553_,
            v_l_1554_,
            v_r_1555_,
        );
        return v___x_1556_;
    } else {
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1550_);
        v___x_1557_ = crate::leanh::lean_box(0);
        v___x_1558_ = crate::leanh::lean_apply_1(v_h__1_1549_, v___x_1557_);
        return v___x_1558_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(
    mut v_00_u03b1_1559_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1560_: *mut crate::leanh::LeanObject,
    mut v_motive_1561_: *mut crate::leanh::LeanObject,
    mut v_t_1562_: *mut crate::leanh::LeanObject,
    mut v_h__1_1563_: *mut crate::leanh::LeanObject,
    mut v_h__2_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1562_) == 0 {
        let mut v_size_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1563_);
        v_size_1565_ = crate::leanh::lean_ctor_get(v_t_1562_, 0);
        crate::leanh::lean_inc(v_size_1565_);
        v_k_1566_ = crate::leanh::lean_ctor_get(v_t_1562_, 1);
        crate::leanh::lean_inc(v_k_1566_);
        v_v_1567_ = crate::leanh::lean_ctor_get(v_t_1562_, 2);
        crate::leanh::lean_inc(v_v_1567_);
        v_l_1568_ = crate::leanh::lean_ctor_get(v_t_1562_, 3);
        crate::leanh::lean_inc(v_l_1568_);
        v_r_1569_ = crate::leanh::lean_ctor_get(v_t_1562_, 4);
        crate::leanh::lean_inc(v_r_1569_);
        crate::leanh::lean_dec_ref_known(v_t_1562_, 5);
        v___x_1570_ = crate::leanh::lean_apply_5(
            v_h__2_1564_,
            v_size_1565_,
            v_k_1566_,
            v_v_1567_,
            v_l_1568_,
            v_r_1569_,
        );
        return v___x_1570_;
    } else {
        let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1564_);
        v___x_1571_ = crate::leanh::lean_box(0);
        v___x_1572_ = crate::leanh::lean_apply_1(v_h__1_1563_, v___x_1571_);
        return v___x_1572_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(
    mut v_x_1573_: u8,
    mut v_h__1_1574_: *mut crate::leanh::LeanObject,
    mut v_h__2_1575_: *mut crate::leanh::LeanObject,
    mut v_h__3_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1573_ {
        0 => {
            let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1576_);
            crate::leanh::lean_dec(v_h__2_1575_);
            v___x_1577_ = crate::leanh::lean_box(0);
            v___x_1578_ = crate::leanh::lean_apply_1(v_h__1_1574_, v___x_1577_);
            return v___x_1578_;
        }
        1 => {
            let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1576_);
            crate::leanh::lean_dec(v_h__1_1574_);
            v___x_1579_ = crate::leanh::lean_box(0);
            v___x_1580_ = crate::leanh::lean_apply_1(v_h__2_1575_, v___x_1579_);
            return v___x_1580_;
        }
        _ => {
            let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1575_);
            crate::leanh::lean_dec(v_h__1_1574_);
            v___x_1581_ = crate::leanh::lean_box(0);
            v___x_1582_ = crate::leanh::lean_apply_1(v_h__3_1576_, v___x_1581_);
            return v___x_1582_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(
    mut v_x_1583_: *mut crate::leanh::LeanObject,
    mut v_h__1_1584_: *mut crate::leanh::LeanObject,
    mut v_h__2_1585_: *mut crate::leanh::LeanObject,
    mut v_h__3_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_1587_: u8 = 0;
    let mut v_res_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1587_ = (crate::leanh::lean_unbox(v_x_1583_) as u8);
    v_res_1588_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_36__boxed_1587_, v_h__1_1584_, v_h__2_1585_, v_h__3_1586_);
    return v_res_1588_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(
    mut v_motive_1589_: *mut crate::leanh::LeanObject,
    mut v_x_1590_: u8,
    mut v_h__1_1591_: *mut crate::leanh::LeanObject,
    mut v_h__2_1592_: *mut crate::leanh::LeanObject,
    mut v_h__3_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_1590_ {
        0 => {
            let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1593_);
            crate::leanh::lean_dec(v_h__2_1592_);
            v___x_1594_ = crate::leanh::lean_box(0);
            v___x_1595_ = crate::leanh::lean_apply_1(v_h__1_1591_, v___x_1594_);
            return v___x_1595_;
        }
        1 => {
            let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1593_);
            crate::leanh::lean_dec(v_h__1_1591_);
            v___x_1596_ = crate::leanh::lean_box(0);
            v___x_1597_ = crate::leanh::lean_apply_1(v_h__2_1592_, v___x_1596_);
            return v___x_1597_;
        }
        _ => {
            let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1592_);
            crate::leanh::lean_dec(v_h__1_1591_);
            v___x_1598_ = crate::leanh::lean_box(0);
            v___x_1599_ = crate::leanh::lean_apply_1(v_h__3_1593_, v___x_1598_);
            return v___x_1599_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(
    mut v_motive_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
    mut v_h__1_1602_: *mut crate::leanh::LeanObject,
    mut v_h__2_1603_: *mut crate::leanh::LeanObject,
    mut v_h__3_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_1605_: u8 = 0;
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1605_ = (crate::leanh::lean_unbox(v_x_1601_) as u8);
    v_res_1606_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_1600_, v_x_51__boxed_1605_, v_h__1_1602_, v_h__2_1603_, v_h__3_1604_);
    return v_res_1606_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(
    mut v_x_1607_: u8,
    mut v_h__1_1608_: *mut crate::leanh::LeanObject,
    mut v_h__2_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1607_ == 0 {
        let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1608_);
        v___x_1610_ = crate::leanh::lean_box(0);
        v___x_1611_ = crate::leanh::lean_apply_1(v_h__2_1609_, v___x_1610_);
        return v___x_1611_;
    } else {
        let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1609_);
        v___x_1612_ = crate::leanh::lean_box(0);
        v___x_1613_ = crate::leanh::lean_apply_1(v_h__1_1608_, v___x_1612_);
        return v___x_1613_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1614_: *mut crate::leanh::LeanObject,
    mut v_h__1_1615_: *mut crate::leanh::LeanObject,
    mut v_h__2_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1617_ = (crate::leanh::lean_unbox(v_x_1614_) as u8);
    v_res_1618_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(
            v_x_26__boxed_1617_,
            v_h__1_1615_,
            v_h__2_1616_,
        );
    return v_res_1618_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(
    mut v_motive_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: u8,
    mut v_h__1_1621_: *mut crate::leanh::LeanObject,
    mut v_h__2_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1620_ == 0 {
        let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1621_);
        v___x_1623_ = crate::leanh::lean_box(0);
        v___x_1624_ = crate::leanh::lean_apply_1(v_h__2_1622_, v___x_1623_);
        return v___x_1624_;
    } else {
        let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1622_);
        v___x_1625_ = crate::leanh::lean_box(0);
        v___x_1626_ = crate::leanh::lean_apply_1(v_h__1_1621_, v___x_1625_);
        return v___x_1626_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1627_: *mut crate::leanh::LeanObject,
    mut v_x_1628_: *mut crate::leanh::LeanObject,
    mut v_h__1_1629_: *mut crate::leanh::LeanObject,
    mut v_h__2_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1631_: u8 = 0;
    let mut v_res_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1631_ = (crate::leanh::lean_unbox(v_x_1628_) as u8);
    v_res_1632_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(
        v_motive_1627_,
        v_x_37__boxed_1631_,
        v_h__1_1629_,
        v_h__2_1630_,
    );
    return v_res_1632_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(
    mut v_x_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1633_) == 0 {
        let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1634_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1634_;
    } else {
        let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1635_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1635_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_1636_);
    crate::leanh::lean_dec(v_x_1636_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx(
    mut v_00_u03b1_1638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_x_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(
    mut v_00_u03b1_1642_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1643_: *mut crate::leanh::LeanObject,
    mut v_x_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ =
        l_Std_DTreeMap_Internal_Zipper_ctorIdx(v_00_u03b1_1642_, v_00_u03b2_1643_, v_x_1644_);
    crate::leanh::lean_dec(v_x_1644_);
    return v_res_1645_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(
    mut v_t_1646_: *mut crate::leanh::LeanObject,
    mut v_k_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1646_) == 0 {
        return v_k_1647_;
    } else {
        let mut v_k_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1648_ = crate::leanh::lean_ctor_get(v_t_1646_, 0);
        crate::leanh::lean_inc(v_k_1648_);
        v_v_1649_ = crate::leanh::lean_ctor_get(v_t_1646_, 1);
        crate::leanh::lean_inc(v_v_1649_);
        v_tree_1650_ = crate::leanh::lean_ctor_get(v_t_1646_, 2);
        crate::leanh::lean_inc(v_tree_1650_);
        v_next_1651_ = crate::leanh::lean_ctor_get(v_t_1646_, 3);
        crate::leanh::lean_inc(v_next_1651_);
        crate::leanh::lean_dec_ref_known(v_t_1646_, 4);
        v___x_1652_ =
            crate::leanh::lean_apply_4(v_k_1647_, v_k_1648_, v_v_1649_, v_tree_1650_, v_next_1651_);
        return v___x_1652_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim(
    mut v_00_u03b1_1653_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1654_: *mut crate::leanh::LeanObject,
    mut v_motive_1655_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1656_: *mut crate::leanh::LeanObject,
    mut v_t_1657_: *mut crate::leanh::LeanObject,
    mut v_h_1658_: *mut crate::leanh::LeanObject,
    mut v_k_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1657_, v_k_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(
    mut v_00_u03b1_1661_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1662_: *mut crate::leanh::LeanObject,
    mut v_motive_1663_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1664_: *mut crate::leanh::LeanObject,
    mut v_t_1665_: *mut crate::leanh::LeanObject,
    mut v_h_1666_: *mut crate::leanh::LeanObject,
    mut v_k_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(
        v_00_u03b1_1661_,
        v_00_u03b2_1662_,
        v_motive_1663_,
        v_ctorIdx_1664_,
        v_t_1665_,
        v_h_1666_,
        v_k_1667_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1664_);
    return v_res_1668_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(
    mut v_t_1669_: *mut crate::leanh::LeanObject,
    mut v_done_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1669_, v_done_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_done_elim(
    mut v_00_u03b1_1672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut crate::leanh::LeanObject,
    mut v_motive_1674_: *mut crate::leanh::LeanObject,
    mut v_t_1675_: *mut crate::leanh::LeanObject,
    mut v_h_1676_: *mut crate::leanh::LeanObject,
    mut v_done_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1675_, v_done_1677_);
    return v___x_1678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(
    mut v_t_1679_: *mut crate::leanh::LeanObject,
    mut v_cons_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1679_, v_cons_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_cons_elim(
    mut v_00_u03b1_1682_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1683_: *mut crate::leanh::LeanObject,
    mut v_motive_1684_: *mut crate::leanh::LeanObject,
    mut v_t_1685_: *mut crate::leanh::LeanObject,
    mut v_h_1686_: *mut crate::leanh::LeanObject,
    mut v_cons_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1685_, v_cons_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(
    mut v_init_1689_: *mut crate::leanh::LeanObject,
    mut v_x_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1690_) == 0 {
                    v_k_1691_ = crate::leanh::lean_ctor_get(v_x_1690_, 1);
                    v_v_1692_ = crate::leanh::lean_ctor_get(v_x_1690_, 2);
                    v_l_1693_ = crate::leanh::lean_ctor_get(v_x_1690_, 3);
                    v_r_1694_ = crate::leanh::lean_ctor_get(v_x_1690_, 4);
                    v___x_1695_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1689_, v_r_1694_);
                    crate::leanh::lean_inc(v_v_1692_);
                    crate::leanh::lean_inc(v_k_1691_);
                    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1696_, 0, v_k_1691_);
                    crate::leanh::lean_ctor_set(v___x_1696_, 1, v_v_1692_);
                    v___x_1697_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                    crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1695_);
                    v_init_1689_ = v___x_1697_;
                    v_x_1690_ = v_l_1693_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1689_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(
    mut v_init_1699_: *mut crate::leanh::LeanObject,
    mut v_x_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1699_, v_x_1700_);
    crate::leanh::lean_dec(v_x_1700_);
    return v_res_1701_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___redArg(
    mut v_x_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1702_) == 0 {
        let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1703_ = crate::leanh::lean_box(0);
        return v___x_1703_;
    } else {
        let mut v_k_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1704_ = crate::leanh::lean_ctor_get(v_x_1702_, 0);
        v_v_1705_ = crate::leanh::lean_ctor_get(v_x_1702_, 1);
        v_tree_1706_ = crate::leanh::lean_ctor_get(v_x_1702_, 2);
        v_next_1707_ = crate::leanh::lean_ctor_get(v_x_1702_, 3);
        crate::leanh::lean_inc(v_v_1705_);
        crate::leanh::lean_inc(v_k_1704_);
        v___x_1708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1708_, 0, v_k_1704_);
        crate::leanh::lean_ctor_set(v___x_1708_, 1, v_v_1705_);
        v___x_1709_ = crate::leanh::lean_box(0);
        v___x_1710_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_1709_, v_tree_1706_);
        v___x_1711_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1711_, 0, v___x_1708_);
        crate::leanh::lean_ctor_set(v___x_1711_, 1, v___x_1710_);
        v___x_1712_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_1707_);
        v___x_1713_ = l_List_appendTR___redArg(v___x_1711_, v___x_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(
    mut v_x_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_1714_);
    crate::leanh::lean_dec(v_x_1714_);
    return v_res_1715_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList(
    mut v_00_u03b1_1716_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1717_: *mut crate::leanh::LeanObject,
    mut v_x_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___boxed(
    mut v_00_u03b1_1720_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1723_ =
        l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_1720_, v_00_u03b2_1721_, v_x_1722_);
    crate::leanh::lean_dec(v_x_1722_);
    return v_res_1723_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(
    mut v_00_u03b1_1724_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1725_: *mut crate::leanh::LeanObject,
    mut v_init_1726_: *mut crate::leanh::LeanObject,
    mut v_x_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1726_, v_x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(
    mut v_00_u03b1_1729_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1730_: *mut crate::leanh::LeanObject,
    mut v_init_1731_: *mut crate::leanh::LeanObject,
    mut v_x_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(
            v_00_u03b1_1729_,
            v_00_u03b2_1730_,
            v_init_1731_,
            v_x_1732_,
        );
    crate::leanh::lean_dec(v_x_1732_);
    return v_res_1733_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
    mut v_x_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1734_) == 0 {
        let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1735_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1735_;
    } else {
        let mut v_tree_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tree_1736_ = crate::leanh::lean_ctor_get(v_x_1734_, 2);
        v_next_1737_ = crate::leanh::lean_ctor_get(v_x_1734_, 3);
        v___x_1738_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1739_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_1736_);
        v___x_1740_ = lean_nat_add(v___x_1738_, v___x_1739_);
        crate::leanh::lean_dec(v___x_1739_);
        v___x_1741_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_1737_);
        v___x_1742_ = lean_nat_add(v___x_1740_, v___x_1741_);
        crate::leanh::lean_dec(v___x_1741_);
        crate::leanh::lean_dec(v___x_1740_);
        return v___x_1742_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(
    mut v_x_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
            v_x_1743_,
        );
    crate::leanh::lean_dec(v_x_1743_);
    return v_res_1744_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(
    mut v_00_u03b1_1745_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1746_: *mut crate::leanh::LeanObject,
    mut v_x_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
            v_x_1747_,
        );
    return v___x_1748_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(
    mut v_00_u03b1_1749_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1750_: *mut crate::leanh::LeanObject,
    mut v_x_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(
            v_00_u03b1_1749_,
            v_00_u03b2_1750_,
            v_x_1751_,
        );
    crate::leanh::lean_dec(v_x_1751_);
    return v_res_1752_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
    mut v_x_1753_: *mut crate::leanh::LeanObject,
    mut v_x_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1753_) == 0 {
                    v_k_1755_ = crate::leanh::lean_ctor_get(v_x_1753_, 1);
                    v_v_1756_ = crate::leanh::lean_ctor_get(v_x_1753_, 2);
                    v_l_1757_ = crate::leanh::lean_ctor_get(v_x_1753_, 3);
                    v_r_1758_ = crate::leanh::lean_ctor_get(v_x_1753_, 4);
                    crate::leanh::lean_inc(v_r_1758_);
                    crate::leanh::lean_inc(v_v_1756_);
                    crate::leanh::lean_inc(v_k_1755_);
                    v___x_1759_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1759_, 0, v_k_1755_);
                    crate::leanh::lean_ctor_set(v___x_1759_, 1, v_v_1756_);
                    crate::leanh::lean_ctor_set(v___x_1759_, 2, v_r_1758_);
                    crate::leanh::lean_ctor_set(v___x_1759_, 3, v_x_1754_);
                    v_x_1753_ = v_l_1757_;
                    v_x_1754_ = v___x_1759_;
                    state = 0;
                    continue;
                } else {
                    return v_x_1754_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(
    mut v_x_1761_: *mut crate::leanh::LeanObject,
    mut v_x_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_1761_, v_x_1762_);
    crate::leanh::lean_dec(v_x_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap(
    mut v_00_u03b1_1764_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1765_: *mut crate::leanh::LeanObject,
    mut v_x_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_1766_, v_x_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(
    mut v_00_u03b1_1769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1770_: *mut crate::leanh::LeanObject,
    mut v_x_1771_: *mut crate::leanh::LeanObject,
    mut v_x_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Std_DTreeMap_Internal_Zipper_prependMap(
        v_00_u03b1_1769_,
        v_00_u03b2_1770_,
        v_x_1771_,
        v_x_1772_,
    );
    crate::leanh::lean_dec(v_x_1771_);
    return v_res_1773_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
    mut v_inst_1774_: *mut crate::leanh::LeanObject,
    mut v_t_1775_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1776_: *mut crate::leanh::LeanObject,
    mut v_it_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1775_) == 0 {
                    v_k_1778_ = crate::leanh::lean_ctor_get(v_t_1775_, 1);
                    crate::leanh::lean_inc_n(v_k_1778_, 2);
                    v_v_1779_ = crate::leanh::lean_ctor_get(v_t_1775_, 2);
                    crate::leanh::lean_inc(v_v_1779_);
                    v_l_1780_ = crate::leanh::lean_ctor_get(v_t_1775_, 3);
                    crate::leanh::lean_inc(v_l_1780_);
                    v_r_1781_ = crate::leanh::lean_ctor_get(v_t_1775_, 4);
                    crate::leanh::lean_inc(v_r_1781_);
                    crate::leanh::lean_dec_ref_known(v_t_1775_, 5);
                    crate::leanh::lean_inc_ref(v_inst_1774_);
                    crate::leanh::lean_inc(v_lowerBound_1776_);
                    v___x_1782_ =
                        crate::leanh::lean_apply_2(v_inst_1774_, v_lowerBound_1776_, v_k_1778_);
                    v___x_1783_ = (crate::leanh::lean_unbox(v___x_1782_) as u8);
                    match v___x_1783_ {
                        0 => {
                            v___x_1784_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1784_, 0, v_k_1778_);
                            crate::leanh::lean_ctor_set(v___x_1784_, 1, v_v_1779_);
                            crate::leanh::lean_ctor_set(v___x_1784_, 2, v_r_1781_);
                            crate::leanh::lean_ctor_set(v___x_1784_, 3, v_it_1777_);
                            v_t_1775_ = v_l_1780_;
                            v_it_1777_ = v___x_1784_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_dec(v_l_1780_);
                            crate::leanh::lean_dec(v_lowerBound_1776_);
                            crate::leanh::lean_dec_ref(v_inst_1774_);
                            v___x_1786_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1786_, 0, v_k_1778_);
                            crate::leanh::lean_ctor_set(v___x_1786_, 1, v_v_1779_);
                            crate::leanh::lean_ctor_set(v___x_1786_, 2, v_r_1781_);
                            crate::leanh::lean_ctor_set(v___x_1786_, 3, v_it_1777_);
                            return v___x_1786_;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_l_1780_);
                            crate::leanh::lean_dec(v_v_1779_);
                            crate::leanh::lean_dec(v_k_1778_);
                            v_t_1775_ = v_r_1781_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lowerBound_1776_);
                    crate::leanh::lean_dec_ref(v_inst_1774_);
                    return v_it_1777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGE(
    mut v_00_u03b1_1788_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_t_1791_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1792_: *mut crate::leanh::LeanObject,
    mut v_it_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_1790_,
        v_t_1791_,
        v_lowerBound_1792_,
        v_it_1793_,
    );
    return v___x_1794_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
    mut v_inst_1795_: *mut crate::leanh::LeanObject,
    mut v_t_1796_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1797_: *mut crate::leanh::LeanObject,
    mut v_it_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1796_) == 0 {
                    v_k_1799_ = crate::leanh::lean_ctor_get(v_t_1796_, 1);
                    crate::leanh::lean_inc_n(v_k_1799_, 2);
                    v_v_1800_ = crate::leanh::lean_ctor_get(v_t_1796_, 2);
                    crate::leanh::lean_inc(v_v_1800_);
                    v_l_1801_ = crate::leanh::lean_ctor_get(v_t_1796_, 3);
                    crate::leanh::lean_inc(v_l_1801_);
                    v_r_1802_ = crate::leanh::lean_ctor_get(v_t_1796_, 4);
                    crate::leanh::lean_inc(v_r_1802_);
                    crate::leanh::lean_dec_ref_known(v_t_1796_, 5);
                    crate::leanh::lean_inc_ref(v_inst_1795_);
                    crate::leanh::lean_inc(v_lowerBound_1797_);
                    v___x_1803_ =
                        crate::leanh::lean_apply_2(v_inst_1795_, v_lowerBound_1797_, v_k_1799_);
                    v___x_1804_ = (crate::leanh::lean_unbox(v___x_1803_) as u8);
                    if v___x_1804_ == 0 {
                        v___x_1805_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1805_, 0, v_k_1799_);
                        crate::leanh::lean_ctor_set(v___x_1805_, 1, v_v_1800_);
                        crate::leanh::lean_ctor_set(v___x_1805_, 2, v_r_1802_);
                        crate::leanh::lean_ctor_set(v___x_1805_, 3, v_it_1798_);
                        v_t_1796_ = v_l_1801_;
                        v_it_1798_ = v___x_1805_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1801_);
                        crate::leanh::lean_dec(v_v_1800_);
                        crate::leanh::lean_dec(v_k_1799_);
                        v_t_1796_ = v_r_1802_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_lowerBound_1797_);
                    crate::leanh::lean_dec_ref(v_inst_1795_);
                    return v_it_1798_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGT(
    mut v_00_u03b1_1808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1809_: *mut crate::leanh::LeanObject,
    mut v_inst_1810_: *mut crate::leanh::LeanObject,
    mut v_t_1811_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_1812_: *mut crate::leanh::LeanObject,
    mut v_it_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_1810_,
        v_t_1811_,
        v_lowerBound_1812_,
        v_it_1813_,
    );
    return v___x_1814_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(
    mut v_x_1815_: *mut crate::leanh::LeanObject,
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v_h__1_1817_: *mut crate::leanh::LeanObject,
    mut v_h__2_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1815_) == 0 {
        let mut v_size_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1817_);
        v_size_1819_ = crate::leanh::lean_ctor_get(v_x_1815_, 0);
        crate::leanh::lean_inc(v_size_1819_);
        v_k_1820_ = crate::leanh::lean_ctor_get(v_x_1815_, 1);
        crate::leanh::lean_inc(v_k_1820_);
        v_v_1821_ = crate::leanh::lean_ctor_get(v_x_1815_, 2);
        crate::leanh::lean_inc(v_v_1821_);
        v_l_1822_ = crate::leanh::lean_ctor_get(v_x_1815_, 3);
        crate::leanh::lean_inc(v_l_1822_);
        v_r_1823_ = crate::leanh::lean_ctor_get(v_x_1815_, 4);
        crate::leanh::lean_inc(v_r_1823_);
        crate::leanh::lean_dec_ref_known(v_x_1815_, 5);
        v___x_1824_ = crate::leanh::lean_apply_6(
            v_h__2_1818_,
            v_size_1819_,
            v_k_1820_,
            v_v_1821_,
            v_l_1822_,
            v_r_1823_,
            v_x_1816_,
        );
        return v___x_1824_;
    } else {
        let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1818_);
        v___x_1825_ = crate::leanh::lean_apply_1(v_h__1_1817_, v_x_1816_);
        return v___x_1825_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(
    mut v_00_u03b1_1826_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut crate::leanh::LeanObject,
    mut v_motive_1828_: *mut crate::leanh::LeanObject,
    mut v_x_1829_: *mut crate::leanh::LeanObject,
    mut v_x_1830_: *mut crate::leanh::LeanObject,
    mut v_h__1_1831_: *mut crate::leanh::LeanObject,
    mut v_h__2_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1829_) == 0 {
        let mut v_size_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1831_);
        v_size_1833_ = crate::leanh::lean_ctor_get(v_x_1829_, 0);
        crate::leanh::lean_inc(v_size_1833_);
        v_k_1834_ = crate::leanh::lean_ctor_get(v_x_1829_, 1);
        crate::leanh::lean_inc(v_k_1834_);
        v_v_1835_ = crate::leanh::lean_ctor_get(v_x_1829_, 2);
        crate::leanh::lean_inc(v_v_1835_);
        v_l_1836_ = crate::leanh::lean_ctor_get(v_x_1829_, 3);
        crate::leanh::lean_inc(v_l_1836_);
        v_r_1837_ = crate::leanh::lean_ctor_get(v_x_1829_, 4);
        crate::leanh::lean_inc(v_r_1837_);
        crate::leanh::lean_dec_ref_known(v_x_1829_, 5);
        v___x_1838_ = crate::leanh::lean_apply_6(
            v_h__2_1832_,
            v_size_1833_,
            v_k_1834_,
            v_v_1835_,
            v_l_1836_,
            v_r_1837_,
            v_x_1830_,
        );
        return v___x_1838_;
    } else {
        let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1832_);
        v___x_1839_ = crate::leanh::lean_apply_1(v_h__1_1831_, v_x_1830_);
        return v___x_1839_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(
    mut v_x_1840_: *mut crate::leanh::LeanObject,
    mut v_h__1_1841_: *mut crate::leanh::LeanObject,
    mut v_h__2_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1840_) == 0 {
        let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1842_);
        v___x_1843_ = crate::leanh::lean_box(0);
        v___x_1844_ = crate::leanh::lean_apply_1(v_h__1_1841_, v___x_1843_);
        return v___x_1844_;
    } else {
        let mut v_k_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1841_);
        v_k_1845_ = crate::leanh::lean_ctor_get(v_x_1840_, 0);
        crate::leanh::lean_inc(v_k_1845_);
        v_v_1846_ = crate::leanh::lean_ctor_get(v_x_1840_, 1);
        crate::leanh::lean_inc(v_v_1846_);
        v_tree_1847_ = crate::leanh::lean_ctor_get(v_x_1840_, 2);
        crate::leanh::lean_inc(v_tree_1847_);
        v_next_1848_ = crate::leanh::lean_ctor_get(v_x_1840_, 3);
        crate::leanh::lean_inc(v_next_1848_);
        crate::leanh::lean_dec_ref_known(v_x_1840_, 4);
        v___x_1849_ = crate::leanh::lean_apply_4(
            v_h__2_1842_,
            v_k_1845_,
            v_v_1846_,
            v_tree_1847_,
            v_next_1848_,
        );
        return v___x_1849_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(
    mut v_00_u03b1_1850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1851_: *mut crate::leanh::LeanObject,
    mut v_motive_1852_: *mut crate::leanh::LeanObject,
    mut v_x_1853_: *mut crate::leanh::LeanObject,
    mut v_h__1_1854_: *mut crate::leanh::LeanObject,
    mut v_h__2_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1853_) == 0 {
        let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1855_);
        v___x_1856_ = crate::leanh::lean_box(0);
        v___x_1857_ = crate::leanh::lean_apply_1(v_h__1_1854_, v___x_1856_);
        return v___x_1857_;
    } else {
        let mut v_k_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1854_);
        v_k_1858_ = crate::leanh::lean_ctor_get(v_x_1853_, 0);
        crate::leanh::lean_inc(v_k_1858_);
        v_v_1859_ = crate::leanh::lean_ctor_get(v_x_1853_, 1);
        crate::leanh::lean_inc(v_v_1859_);
        v_tree_1860_ = crate::leanh::lean_ctor_get(v_x_1853_, 2);
        crate::leanh::lean_inc(v_tree_1860_);
        v_next_1861_ = crate::leanh::lean_ctor_get(v_x_1853_, 3);
        crate::leanh::lean_inc(v_next_1861_);
        crate::leanh::lean_dec_ref_known(v_x_1853_, 4);
        v___x_1862_ = crate::leanh::lean_apply_4(
            v_h__2_1855_,
            v_k_1858_,
            v_v_1859_,
            v_tree_1860_,
            v_next_1861_,
        );
        return v___x_1862_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(
    mut v_x_1863_: *mut crate::leanh::LeanObject,
    mut v_h__1_1864_: *mut crate::leanh::LeanObject,
    mut v_h__2_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1863_) == 0 {
        let mut v_size_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1864_);
        v_size_1866_ = crate::leanh::lean_ctor_get(v_x_1863_, 0);
        crate::leanh::lean_inc(v_size_1866_);
        v_k_1867_ = crate::leanh::lean_ctor_get(v_x_1863_, 1);
        crate::leanh::lean_inc(v_k_1867_);
        v_v_1868_ = crate::leanh::lean_ctor_get(v_x_1863_, 2);
        crate::leanh::lean_inc(v_v_1868_);
        v_l_1869_ = crate::leanh::lean_ctor_get(v_x_1863_, 3);
        crate::leanh::lean_inc(v_l_1869_);
        v_r_1870_ = crate::leanh::lean_ctor_get(v_x_1863_, 4);
        crate::leanh::lean_inc(v_r_1870_);
        crate::leanh::lean_dec_ref_known(v_x_1863_, 5);
        v___x_1871_ = crate::leanh::lean_apply_5(
            v_h__2_1865_,
            v_size_1866_,
            v_k_1867_,
            v_v_1868_,
            v_l_1869_,
            v_r_1870_,
        );
        return v___x_1871_;
    } else {
        let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1865_);
        v___x_1872_ = crate::leanh::lean_box(0);
        v___x_1873_ = crate::leanh::lean_apply_1(v_h__1_1864_, v___x_1872_);
        return v___x_1873_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(
    mut v_00_u03b1_1874_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1875_: *mut crate::leanh::LeanObject,
    mut v_motive_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
    mut v_h__1_1878_: *mut crate::leanh::LeanObject,
    mut v_h__2_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1877_) == 0 {
        let mut v_size_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1878_);
        v_size_1880_ = crate::leanh::lean_ctor_get(v_x_1877_, 0);
        crate::leanh::lean_inc(v_size_1880_);
        v_k_1881_ = crate::leanh::lean_ctor_get(v_x_1877_, 1);
        crate::leanh::lean_inc(v_k_1881_);
        v_v_1882_ = crate::leanh::lean_ctor_get(v_x_1877_, 2);
        crate::leanh::lean_inc(v_v_1882_);
        v_l_1883_ = crate::leanh::lean_ctor_get(v_x_1877_, 3);
        crate::leanh::lean_inc(v_l_1883_);
        v_r_1884_ = crate::leanh::lean_ctor_get(v_x_1877_, 4);
        crate::leanh::lean_inc(v_r_1884_);
        crate::leanh::lean_dec_ref_known(v_x_1877_, 5);
        v___x_1885_ = crate::leanh::lean_apply_5(
            v_h__2_1879_,
            v_size_1880_,
            v_k_1881_,
            v_v_1882_,
            v_l_1883_,
            v_r_1884_,
        );
        return v___x_1885_;
    } else {
        let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1879_);
        v___x_1886_ = crate::leanh::lean_box(0);
        v___x_1887_ = crate::leanh::lean_apply_1(v_h__1_1878_, v___x_1886_);
        return v___x_1887_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_step___redArg(
    mut v_x_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1888_) == 0 {
        let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1889_ = crate::leanh::lean_box(2);
        return v___x_1889_;
    } else {
        let mut v_k_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1890_ = crate::leanh::lean_ctor_get(v_x_1888_, 0);
        crate::leanh::lean_inc(v_k_1890_);
        v_v_1891_ = crate::leanh::lean_ctor_get(v_x_1888_, 1);
        crate::leanh::lean_inc(v_v_1891_);
        v_tree_1892_ = crate::leanh::lean_ctor_get(v_x_1888_, 2);
        crate::leanh::lean_inc(v_tree_1892_);
        v_next_1893_ = crate::leanh::lean_ctor_get(v_x_1888_, 3);
        crate::leanh::lean_inc(v_next_1893_);
        crate::leanh::lean_dec_ref_known(v_x_1888_, 4);
        v___x_1894_ =
            l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_1892_, v_next_1893_);
        crate::leanh::lean_dec(v_tree_1892_);
        v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1895_, 0, v_k_1890_);
        crate::leanh::lean_ctor_set(v___x_1895_, 1, v_v_1891_);
        v___x_1896_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1896_, 0, v___x_1894_);
        crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
        return v___x_1896_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_step(
    mut v_00_u03b1_1897_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1898_: *mut crate::leanh::LeanObject,
    mut v_x_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_1899_);
    return v___x_1900_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(
    mut v_00_u03b1_1902_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1904_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0;
    return v___f_1904_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(
    mut v_00_u03b1_1905_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = crate::leanh::lean_box(0);
    return v___x_1907_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___redArg(
    mut v_t_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_t_1908_);
    return v_t_1908_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(
    mut v_t_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_1909_);
    crate::leanh::lean_dec(v_t_1909_);
    return v_res_1910_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter(
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1912_: *mut crate::leanh::LeanObject,
    mut v_t_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_t_1913_);
    return v_t_1913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___boxed(
    mut v_00_u03b1_1914_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1915_: *mut crate::leanh::LeanObject,
    mut v_t_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ =
        l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_1914_, v_00_u03b2_1915_, v_t_1916_);
    crate::leanh::lean_dec(v_t_1916_);
    return v_res_1917_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(
    mut v_t_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = crate::leanh::lean_box(0);
    v___x_1920_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1918_, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(
    mut v_t_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_1921_);
    crate::leanh::lean_dec(v_t_1921_);
    return v_res_1922_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree(
    mut v_00_u03b1_1923_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1924_: *mut crate::leanh::LeanObject,
    mut v_t_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(
    mut v_00_u03b1_1927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1928_: *mut crate::leanh::LeanObject,
    mut v_t_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ =
        l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_1927_, v_00_u03b2_1928_, v_t_1929_);
    crate::leanh::lean_dec(v_t_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(
    mut v_x_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1931_);
    return v_x_1931_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(
    mut v_x_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(v_x_1932_);
    crate::leanh::lean_dec(v_x_1932_);
    return v_res_1933_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator(
    mut v_00_u03b1_1935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1937_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0;
    return v___f_1937_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_1938_: *mut crate::leanh::LeanObject,
    mut v_h__1_1939_: *mut crate::leanh::LeanObject,
    mut v_h__2_1940_: *mut crate::leanh::LeanObject,
    mut v_h__3_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1938_) {
        0 => {
            let mut v_it_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1941_);
            crate::leanh::lean_dec(v_h__2_1940_);
            v_it_1942_ = crate::leanh::lean_ctor_get(v_x_1938_, 0);
            crate::leanh::lean_inc(v_it_1942_);
            v_out_1943_ = crate::leanh::lean_ctor_get(v_x_1938_, 1);
            crate::leanh::lean_inc(v_out_1943_);
            crate::leanh::lean_dec_ref_known(v_x_1938_, 2);
            v___x_1944_ = crate::leanh::lean_apply_2(v_h__1_1939_, v_it_1942_, v_out_1943_);
            return v___x_1944_;
        }
        1 => {
            let mut v_it_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1941_);
            crate::leanh::lean_dec(v_h__1_1939_);
            v_it_1945_ = crate::leanh::lean_ctor_get(v_x_1938_, 0);
            crate::leanh::lean_inc(v_it_1945_);
            crate::leanh::lean_dec_ref_known(v_x_1938_, 1);
            v___x_1946_ = crate::leanh::lean_apply_1(v_h__2_1940_, v_it_1945_);
            return v___x_1946_;
        }
        _ => {
            let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1940_);
            crate::leanh::lean_dec(v_h__1_1939_);
            v___x_1947_ = crate::leanh::lean_box(0);
            v___x_1948_ = crate::leanh::lean_apply_1(v_h__3_1941_, v___x_1947_);
            return v___x_1948_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_1949_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1950_: *mut crate::leanh::LeanObject,
    mut v_m_1951_: *mut crate::leanh::LeanObject,
    mut v_motive_1952_: *mut crate::leanh::LeanObject,
    mut v_x_1953_: *mut crate::leanh::LeanObject,
    mut v_h__1_1954_: *mut crate::leanh::LeanObject,
    mut v_h__2_1955_: *mut crate::leanh::LeanObject,
    mut v_h__3_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1953_) {
        0 => {
            let mut v_it_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1956_);
            crate::leanh::lean_dec(v_h__2_1955_);
            v_it_1957_ = crate::leanh::lean_ctor_get(v_x_1953_, 0);
            crate::leanh::lean_inc(v_it_1957_);
            v_out_1958_ = crate::leanh::lean_ctor_get(v_x_1953_, 1);
            crate::leanh::lean_inc(v_out_1958_);
            crate::leanh::lean_dec_ref_known(v_x_1953_, 2);
            v___x_1959_ = crate::leanh::lean_apply_2(v_h__1_1954_, v_it_1957_, v_out_1958_);
            return v___x_1959_;
        }
        1 => {
            let mut v_it_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1956_);
            crate::leanh::lean_dec(v_h__1_1954_);
            v_it_1960_ = crate::leanh::lean_ctor_get(v_x_1953_, 0);
            crate::leanh::lean_inc(v_it_1960_);
            crate::leanh::lean_dec_ref_known(v_x_1953_, 1);
            v___x_1961_ = crate::leanh::lean_apply_1(v_h__2_1955_, v_it_1960_);
            return v___x_1961_;
        }
        _ => {
            let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1955_);
            crate::leanh::lean_dec(v_h__1_1954_);
            v___x_1962_ = crate::leanh::lean_box(0);
            v___x_1963_ = crate::leanh::lean_apply_1(v_h__3_1956_, v___x_1962_);
            return v___x_1963_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxcIterator_step___redArg(
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
    mut v_x_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_k_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_unused_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_iter_1966_ = crate::leanh::lean_ctor_get(v_x_1965_, 0);
                crate::leanh::lean_inc(v_iter_1966_);
                if crate::leanh::lean_obj_tag(v_iter_1966_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_1965_);
                    crate::leanh::lean_dec_ref(v_inst_1964_);
                    v___x_1967_ = crate::leanh::lean_box(2);
                    return v___x_1967_;
                } else {
                    v_upper_1968_ = crate::leanh::lean_ctor_get(v_x_1965_, 1);
                    v_isSharedCheck_1985_ = (!crate::leanh::lean_is_exclusive(v_x_1965_)) as u8;
                    if v_isSharedCheck_1985_ == 0 {
                        v_unused_1986_ = crate::leanh::lean_ctor_get(v_x_1965_, 0);
                        crate::leanh::lean_dec(v_unused_1986_);
                        v___x_1970_ = v_x_1965_;
                        v_isShared_1971_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upper_1968_);
                        crate::leanh::lean_dec(v_x_1965_);
                        v___x_1970_ = crate::leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_k_1972_ = crate::leanh::lean_ctor_get(v_iter_1966_, 0);
                crate::leanh::lean_inc_n(v_k_1972_, 2);
                v_v_1973_ = crate::leanh::lean_ctor_get(v_iter_1966_, 1);
                crate::leanh::lean_inc(v_v_1973_);
                v_tree_1974_ = crate::leanh::lean_ctor_get(v_iter_1966_, 2);
                crate::leanh::lean_inc(v_tree_1974_);
                v_next_1975_ = crate::leanh::lean_ctor_get(v_iter_1966_, 3);
                crate::leanh::lean_inc(v_next_1975_);
                crate::leanh::lean_dec_ref_known(v_iter_1966_, 4);
                crate::leanh::lean_inc(v_upper_1968_);
                v___x_1976_ = crate::leanh::lean_apply_2(v_inst_1964_, v_k_1972_, v_upper_1968_);
                v___x_1977_ = (crate::leanh::lean_unbox(v___x_1976_) as u8);
                if v___x_1977_ == 2 {
                    crate::leanh::lean_dec(v_next_1975_);
                    crate::leanh::lean_dec(v_tree_1974_);
                    crate::leanh::lean_dec(v_v_1973_);
                    crate::leanh::lean_dec(v_k_1972_);
                    crate::leanh::lean_del_object(v___x_1970_);
                    crate::leanh::lean_dec(v_upper_1968_);
                    v___x_1978_ = crate::leanh::lean_box(2);
                    return v___x_1978_;
                } else {
                    v___x_1979_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                        v_tree_1974_,
                        v_next_1975_,
                    );
                    crate::leanh::lean_dec(v_tree_1974_);
                    if v_isShared_1971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1970_, 0, v___x_1979_);
                        v___x_1981_ = v___x_1970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_upper_1968_);
                        v___x_1981_ = v_reuseFailAlloc_1984_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1982_, 0, v_k_1972_);
                crate::leanh::lean_ctor_set(v___x_1982_, 1, v_v_1973_);
                v___x_1983_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                crate::leanh::lean_ctor_set(v___x_1983_, 1, v___x_1982_);
                return v___x_1983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxcIterator_step(
    mut v_00_u03b1_1987_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1988_: *mut crate::leanh::LeanObject,
    mut v_inst_1989_: *mut crate::leanh::LeanObject,
    mut v_x_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_1989_, v_x_1990_);
    return v___x_1991_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(
    mut v_inst_1992_: *mut crate::leanh::LeanObject,
    mut v_it_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_1992_, v_it_1993_);
    return v___x_1994_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(
    mut v_inst_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1996_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1996_, 0, v_inst_1995_);
    return v___f_1996_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(
    mut v_00_u03b1_1997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1998_: *mut crate::leanh::LeanObject,
    mut v_inst_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2000_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2000_, 0, v_inst_1999_);
    return v___f_2000_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(
    mut v_x_2001_: *mut crate::leanh::LeanObject,
    mut v_h__1_2002_: *mut crate::leanh::LeanObject,
    mut v_h__2_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_iter_2004_ = crate::leanh::lean_ctor_get(v_x_2001_, 0);
    if crate::leanh::lean_obj_tag(v_iter_2004_) == 0 {
        let mut v_upper_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2003_);
        v_upper_2005_ = crate::leanh::lean_ctor_get(v_x_2001_, 1);
        crate::leanh::lean_inc(v_upper_2005_);
        crate::leanh::lean_dec_ref(v_x_2001_);
        v___x_2006_ = crate::leanh::lean_apply_1(v_h__1_2002_, v_upper_2005_);
        return v___x_2006_;
    } else {
        let mut v_upper_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_iter_2004_);
        crate::leanh::lean_dec(v_h__1_2002_);
        v_upper_2007_ = crate::leanh::lean_ctor_get(v_x_2001_, 1);
        crate::leanh::lean_inc(v_upper_2007_);
        crate::leanh::lean_dec_ref(v_x_2001_);
        v_k_2008_ = crate::leanh::lean_ctor_get(v_iter_2004_, 0);
        crate::leanh::lean_inc(v_k_2008_);
        v_v_2009_ = crate::leanh::lean_ctor_get(v_iter_2004_, 1);
        crate::leanh::lean_inc(v_v_2009_);
        v_tree_2010_ = crate::leanh::lean_ctor_get(v_iter_2004_, 2);
        crate::leanh::lean_inc(v_tree_2010_);
        v_next_2011_ = crate::leanh::lean_ctor_get(v_iter_2004_, 3);
        crate::leanh::lean_inc(v_next_2011_);
        crate::leanh::lean_dec_ref_known(v_iter_2004_, 4);
        v___x_2012_ = crate::leanh::lean_apply_5(
            v_h__2_2003_,
            v_k_2008_,
            v_v_2009_,
            v_tree_2010_,
            v_next_2011_,
            v_upper_2007_,
        );
        return v___x_2012_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(
    mut v_00_u03b1_2013_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2014_: *mut crate::leanh::LeanObject,
    mut v_inst_2015_: *mut crate::leanh::LeanObject,
    mut v_motive_2016_: *mut crate::leanh::LeanObject,
    mut v_x_2017_: *mut crate::leanh::LeanObject,
    mut v_h__1_2018_: *mut crate::leanh::LeanObject,
    mut v_h__2_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_iter_2020_ = crate::leanh::lean_ctor_get(v_x_2017_, 0);
    if crate::leanh::lean_obj_tag(v_iter_2020_) == 0 {
        let mut v_upper_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2019_);
        v_upper_2021_ = crate::leanh::lean_ctor_get(v_x_2017_, 1);
        crate::leanh::lean_inc(v_upper_2021_);
        crate::leanh::lean_dec_ref(v_x_2017_);
        v___x_2022_ = crate::leanh::lean_apply_1(v_h__1_2018_, v_upper_2021_);
        return v___x_2022_;
    } else {
        let mut v_upper_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_iter_2020_);
        crate::leanh::lean_dec(v_h__1_2018_);
        v_upper_2023_ = crate::leanh::lean_ctor_get(v_x_2017_, 1);
        crate::leanh::lean_inc(v_upper_2023_);
        crate::leanh::lean_dec_ref(v_x_2017_);
        v_k_2024_ = crate::leanh::lean_ctor_get(v_iter_2020_, 0);
        crate::leanh::lean_inc(v_k_2024_);
        v_v_2025_ = crate::leanh::lean_ctor_get(v_iter_2020_, 1);
        crate::leanh::lean_inc(v_v_2025_);
        v_tree_2026_ = crate::leanh::lean_ctor_get(v_iter_2020_, 2);
        crate::leanh::lean_inc(v_tree_2026_);
        v_next_2027_ = crate::leanh::lean_ctor_get(v_iter_2020_, 3);
        crate::leanh::lean_inc(v_next_2027_);
        crate::leanh::lean_dec_ref_known(v_iter_2020_, 4);
        v___x_2028_ = crate::leanh::lean_apply_5(
            v_h__2_2019_,
            v_k_2024_,
            v_v_2025_,
            v_tree_2026_,
            v_next_2027_,
            v_upper_2023_,
        );
        return v___x_2028_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(
    mut v_00_u03b1_2029_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2030_: *mut crate::leanh::LeanObject,
    mut v_inst_2031_: *mut crate::leanh::LeanObject,
    mut v_motive_2032_: *mut crate::leanh::LeanObject,
    mut v_x_2033_: *mut crate::leanh::LeanObject,
    mut v_h__1_2034_: *mut crate::leanh::LeanObject,
    mut v_h__2_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_2029_, v_00_u03b2_2030_, v_inst_2031_, v_motive_2032_, v_x_2033_, v_h__1_2034_, v_h__2_2035_);
    crate::leanh::lean_dec_ref(v_inst_2031_);
    return v_res_2036_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(
    mut v_00_u03b1_2037_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2038_: *mut crate::leanh::LeanObject,
    mut v_inst_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = crate::leanh::lean_box(0);
    return v___x_2040_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(
    mut v_00_u03b1_2041_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2042_: *mut crate::leanh::LeanObject,
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_2041_, v_00_u03b2_2042_, v_inst_2043_);
    crate::leanh::lean_dec_ref(v_inst_2043_);
    return v_res_2044_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RxoIterator_step___redArg(
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_x_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v_k_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_unused_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_iter_2047_ = crate::leanh::lean_ctor_get(v_x_2046_, 0);
                crate::leanh::lean_inc(v_iter_2047_);
                if crate::leanh::lean_obj_tag(v_iter_2047_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_2046_);
                    crate::leanh::lean_dec_ref(v_inst_2045_);
                    v___x_2048_ = crate::leanh::lean_box(2);
                    return v___x_2048_;
                } else {
                    v_upper_2049_ = crate::leanh::lean_ctor_get(v_x_2046_, 1);
                    v_isSharedCheck_2066_ = (!crate::leanh::lean_is_exclusive(v_x_2046_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v_unused_2067_ = crate::leanh::lean_ctor_get(v_x_2046_, 0);
                        crate::leanh::lean_dec(v_unused_2067_);
                        v___x_2051_ = v_x_2046_;
                        v_isShared_2052_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_upper_2049_);
                        crate::leanh::lean_dec(v_x_2046_);
                        v___x_2051_ = crate::leanh::lean_box(0);
                        v_isShared_2052_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_k_2053_ = crate::leanh::lean_ctor_get(v_iter_2047_, 0);
                crate::leanh::lean_inc_n(v_k_2053_, 2);
                v_v_2054_ = crate::leanh::lean_ctor_get(v_iter_2047_, 1);
                crate::leanh::lean_inc(v_v_2054_);
                v_tree_2055_ = crate::leanh::lean_ctor_get(v_iter_2047_, 2);
                crate::leanh::lean_inc(v_tree_2055_);
                v_next_2056_ = crate::leanh::lean_ctor_get(v_iter_2047_, 3);
                crate::leanh::lean_inc(v_next_2056_);
                crate::leanh::lean_dec_ref_known(v_iter_2047_, 4);
                crate::leanh::lean_inc(v_upper_2049_);
                v___x_2057_ = crate::leanh::lean_apply_2(v_inst_2045_, v_k_2053_, v_upper_2049_);
                v___x_2058_ = (crate::leanh::lean_unbox(v___x_2057_) as u8);
                if v___x_2058_ == 0 {
                    v___x_2059_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                        v_tree_2055_,
                        v_next_2056_,
                    );
                    crate::leanh::lean_dec(v_tree_2055_);
                    if v_isShared_2052_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2051_, 0, v___x_2059_);
                        v___x_2061_ = v___x_2051_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2059_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_upper_2049_);
                        v___x_2061_ = v_reuseFailAlloc_2064_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_next_2056_);
                    crate::leanh::lean_dec(v_tree_2055_);
                    crate::leanh::lean_dec(v_v_2054_);
                    crate::leanh::lean_dec(v_k_2053_);
                    crate::leanh::lean_del_object(v___x_2051_);
                    crate::leanh::lean_dec(v_upper_2049_);
                    v___x_2065_ = crate::leanh::lean_box(2);
                    return v___x_2065_;
                }
            }
            2 => {
                v___x_2062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2062_, 0, v_k_2053_);
                crate::leanh::lean_ctor_set(v___x_2062_, 1, v_v_2054_);
                v___x_2063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                crate::leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                return v___x_2063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxoIterator_step(
    mut v_00_u03b1_2068_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2069_: *mut crate::leanh::LeanObject,
    mut v_inst_2070_: *mut crate::leanh::LeanObject,
    mut v_x_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_2070_, v_x_2071_);
    return v___x_2072_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(
    mut v_inst_2073_: *mut crate::leanh::LeanObject,
    mut v_it_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_2073_, v_it_2074_);
    return v___x_2075_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(
    mut v_inst_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2077_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2077_, 0, v_inst_2076_);
    return v___f_2077_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(
    mut v_00_u03b1_2078_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2081_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2081_, 0, v_inst_2080_);
    return v___f_2081_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(
    mut v_x_2082_: *mut crate::leanh::LeanObject,
    mut v_h__1_2083_: *mut crate::leanh::LeanObject,
    mut v_h__2_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_iter_2085_ = crate::leanh::lean_ctor_get(v_x_2082_, 0);
    if crate::leanh::lean_obj_tag(v_iter_2085_) == 0 {
        let mut v_upper_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2084_);
        v_upper_2086_ = crate::leanh::lean_ctor_get(v_x_2082_, 1);
        crate::leanh::lean_inc(v_upper_2086_);
        crate::leanh::lean_dec_ref(v_x_2082_);
        v___x_2087_ = crate::leanh::lean_apply_1(v_h__1_2083_, v_upper_2086_);
        return v___x_2087_;
    } else {
        let mut v_upper_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_iter_2085_);
        crate::leanh::lean_dec(v_h__1_2083_);
        v_upper_2088_ = crate::leanh::lean_ctor_get(v_x_2082_, 1);
        crate::leanh::lean_inc(v_upper_2088_);
        crate::leanh::lean_dec_ref(v_x_2082_);
        v_k_2089_ = crate::leanh::lean_ctor_get(v_iter_2085_, 0);
        crate::leanh::lean_inc(v_k_2089_);
        v_v_2090_ = crate::leanh::lean_ctor_get(v_iter_2085_, 1);
        crate::leanh::lean_inc(v_v_2090_);
        v_tree_2091_ = crate::leanh::lean_ctor_get(v_iter_2085_, 2);
        crate::leanh::lean_inc(v_tree_2091_);
        v_next_2092_ = crate::leanh::lean_ctor_get(v_iter_2085_, 3);
        crate::leanh::lean_inc(v_next_2092_);
        crate::leanh::lean_dec_ref_known(v_iter_2085_, 4);
        v___x_2093_ = crate::leanh::lean_apply_5(
            v_h__2_2084_,
            v_k_2089_,
            v_v_2090_,
            v_tree_2091_,
            v_next_2092_,
            v_upper_2088_,
        );
        return v___x_2093_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(
    mut v_00_u03b1_2094_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut crate::leanh::LeanObject,
    mut v_inst_2096_: *mut crate::leanh::LeanObject,
    mut v_motive_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_h__1_2099_: *mut crate::leanh::LeanObject,
    mut v_h__2_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_iter_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_iter_2101_ = crate::leanh::lean_ctor_get(v_x_2098_, 0);
    if crate::leanh::lean_obj_tag(v_iter_2101_) == 0 {
        let mut v_upper_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2100_);
        v_upper_2102_ = crate::leanh::lean_ctor_get(v_x_2098_, 1);
        crate::leanh::lean_inc(v_upper_2102_);
        crate::leanh::lean_dec_ref(v_x_2098_);
        v___x_2103_ = crate::leanh::lean_apply_1(v_h__1_2099_, v_upper_2102_);
        return v___x_2103_;
    } else {
        let mut v_upper_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_iter_2101_);
        crate::leanh::lean_dec(v_h__1_2099_);
        v_upper_2104_ = crate::leanh::lean_ctor_get(v_x_2098_, 1);
        crate::leanh::lean_inc(v_upper_2104_);
        crate::leanh::lean_dec_ref(v_x_2098_);
        v_k_2105_ = crate::leanh::lean_ctor_get(v_iter_2101_, 0);
        crate::leanh::lean_inc(v_k_2105_);
        v_v_2106_ = crate::leanh::lean_ctor_get(v_iter_2101_, 1);
        crate::leanh::lean_inc(v_v_2106_);
        v_tree_2107_ = crate::leanh::lean_ctor_get(v_iter_2101_, 2);
        crate::leanh::lean_inc(v_tree_2107_);
        v_next_2108_ = crate::leanh::lean_ctor_get(v_iter_2101_, 3);
        crate::leanh::lean_inc(v_next_2108_);
        crate::leanh::lean_dec_ref_known(v_iter_2101_, 4);
        v___x_2109_ = crate::leanh::lean_apply_5(
            v_h__2_2100_,
            v_k_2105_,
            v_v_2106_,
            v_tree_2107_,
            v_next_2108_,
            v_upper_2104_,
        );
        return v___x_2109_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(
    mut v_00_u03b1_2110_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2111_: *mut crate::leanh::LeanObject,
    mut v_inst_2112_: *mut crate::leanh::LeanObject,
    mut v_motive_2113_: *mut crate::leanh::LeanObject,
    mut v_x_2114_: *mut crate::leanh::LeanObject,
    mut v_h__1_2115_: *mut crate::leanh::LeanObject,
    mut v_h__2_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2117_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_2110_, v_00_u03b2_2111_, v_inst_2112_, v_motive_2113_, v_x_2114_, v_h__1_2115_, v_h__2_2116_);
    crate::leanh::lean_dec_ref(v_inst_2112_);
    return v_res_2117_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(
    mut v_00_u03b1_2118_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2119_: *mut crate::leanh::LeanObject,
    mut v_inst_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = crate::leanh::lean_box(0);
    return v___x_2121_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2122_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2123_: *mut crate::leanh::LeanObject,
    mut v_inst_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_2122_, v_00_u03b2_2123_, v_inst_2124_);
    crate::leanh::lean_dec_ref(v_inst_2124_);
    return v_res_2125_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(
    mut v_carrier_2126_: *mut crate::leanh::LeanObject,
    mut v_range_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2128_, 0, v_carrier_2126_);
    crate::leanh::lean_ctor_set(v___x_2128_, 1, v_range_2127_);
    return v___x_2128_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice(
    mut v_00_u03b1_2130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2131_: *mut crate::leanh::LeanObject,
    mut v_inst_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2133_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0;
    return v___f_2133_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(
    mut v_00_u03b1_2134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2135_: *mut crate::leanh::LeanObject,
    mut v_inst_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(
        v_00_u03b1_2134_,
        v_00_u03b2_2135_,
        v_inst_2136_,
    );
    crate::leanh::lean_dec_ref(v_inst_2136_);
    return v_res_2137_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(
    mut v_x_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2139_ = crate::leanh::lean_ctor_get(v_x_2138_, 0);
                v_range_2140_ = crate::leanh::lean_ctor_get(v_x_2138_, 1);
                v_isSharedCheck_2149_ = (!crate::leanh::lean_is_exclusive(v_x_2138_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2142_ = v_x_2138_;
                    v_isShared_2143_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2140_);
                    crate::leanh::lean_inc(v_treeMap_2139_);
                    crate::leanh::lean_dec(v_x_2138_);
                    v___x_2142_ = crate::leanh::lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2144_ = crate::leanh::lean_box(0);
                v___x_2145_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2139_,
                    v___x_2144_,
                );
                crate::leanh::lean_dec(v_treeMap_2139_);
                if v_isShared_2143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_range_2140_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RicSlice_instToIterator(
    mut v_00_u03b1_2151_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2152_: *mut crate::leanh::LeanObject,
    mut v_inst_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2154_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0;
    return v___f_2154_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2155_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2156_: *mut crate::leanh::LeanObject,
    mut v_inst_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(
        v_00_u03b1_2155_,
        v_00_u03b2_2156_,
        v_inst_2157_,
    );
    crate::leanh::lean_dec_ref(v_inst_2157_);
    return v_res_2158_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(
    mut v_carrier_2159_: *mut crate::leanh::LeanObject,
    mut v_range_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2161_, 0, v_carrier_2159_);
    crate::leanh::lean_ctor_set(v___x_2161_, 1, v_range_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(
    mut v_00_u03b1_2163_: *mut crate::leanh::LeanObject,
    mut v_inst_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2165_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0;
    return v___f_2165_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(
    mut v_00_u03b1_2166_: *mut crate::leanh::LeanObject,
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_2166_, v_inst_2167_);
    crate::leanh::lean_dec_ref(v_inst_2167_);
    return v_res_2168_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(
    mut v_x_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2170_ = crate::leanh::lean_ctor_get(v_x_2169_, 0);
                v_range_2171_ = crate::leanh::lean_ctor_get(v_x_2169_, 1);
                v_isSharedCheck_2180_ = (!crate::leanh::lean_is_exclusive(v_x_2169_)) as u8;
                if v_isSharedCheck_2180_ == 0 {
                    v___x_2173_ = v_x_2169_;
                    v_isShared_2174_ = v_isSharedCheck_2180_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2171_);
                    crate::leanh::lean_inc(v_treeMap_2170_);
                    crate::leanh::lean_dec(v_x_2169_);
                    v___x_2173_ = crate::leanh::lean_box(0);
                    v_isShared_2174_ = v_isSharedCheck_2180_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2175_ = crate::leanh::lean_box(0);
                v___x_2176_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2170_,
                    v___x_2175_,
                );
                crate::leanh::lean_dec(v_treeMap_2170_);
                if v_isShared_2174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_range_2171_);
                    v___x_2178_ = v_reuseFailAlloc_2179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(
    mut v_00_u03b1_2182_: *mut crate::leanh::LeanObject,
    mut v_inst_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2184_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0;
    return v___f_2184_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2185_: *mut crate::leanh::LeanObject,
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ =
        l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_2185_, v_inst_2186_);
    crate::leanh::lean_dec_ref(v_inst_2186_);
    return v_res_2187_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(
    mut v_carrier_2188_: *mut crate::leanh::LeanObject,
    mut v_range_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2190_, 0, v_carrier_2188_);
    crate::leanh::lean_ctor_set(v___x_2190_, 1, v_range_2189_);
    return v___x_2190_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(
    mut v_00_u03b1_2192_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2193_: *mut crate::leanh::LeanObject,
    mut v_inst_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2195_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0;
    return v___f_2195_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(
    mut v_00_u03b1_2196_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2197_: *mut crate::leanh::LeanObject,
    mut v_inst_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(
        v_00_u03b1_2196_,
        v_00_u03b2_2197_,
        v_inst_2198_,
    );
    crate::leanh::lean_dec_ref(v_inst_2198_);
    return v_res_2199_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(
    mut v_x_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2201_ = crate::leanh::lean_ctor_get(v_x_2200_, 0);
                v_range_2202_ = crate::leanh::lean_ctor_get(v_x_2200_, 1);
                v_isSharedCheck_2211_ = (!crate::leanh::lean_is_exclusive(v_x_2200_)) as u8;
                if v_isSharedCheck_2211_ == 0 {
                    v___x_2204_ = v_x_2200_;
                    v_isShared_2205_ = v_isSharedCheck_2211_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2202_);
                    crate::leanh::lean_inc(v_treeMap_2201_);
                    crate::leanh::lean_dec(v_x_2200_);
                    v___x_2204_ = crate::leanh::lean_box(0);
                    v_isShared_2205_ = v_isSharedCheck_2211_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2206_ = crate::leanh::lean_box(0);
                v___x_2207_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2201_,
                    v___x_2206_,
                );
                crate::leanh::lean_dec(v_treeMap_2201_);
                if v_isShared_2205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2204_, 0, v___x_2207_);
                    v___x_2209_ = v___x_2204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_range_2202_);
                    v___x_2209_ = v_reuseFailAlloc_2210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(
    mut v_00_u03b1_2213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2214_: *mut crate::leanh::LeanObject,
    mut v_inst_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2216_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0;
    return v___f_2216_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2217_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2218_: *mut crate::leanh::LeanObject,
    mut v_inst_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(
        v_00_u03b1_2217_,
        v_00_u03b2_2218_,
        v_inst_2219_,
    );
    crate::leanh::lean_dec_ref(v_inst_2219_);
    return v_res_2220_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(
    mut v_carrier_2221_: *mut crate::leanh::LeanObject,
    mut v_range_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2223_, 0, v_carrier_2221_);
    crate::leanh::lean_ctor_set(v___x_2223_, 1, v_range_2222_);
    return v___x_2223_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice(
    mut v_00_u03b1_2225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2226_: *mut crate::leanh::LeanObject,
    mut v_inst_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2228_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0;
    return v___f_2228_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(
    mut v_00_u03b1_2229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut crate::leanh::LeanObject,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(
        v_00_u03b1_2229_,
        v_00_u03b2_2230_,
        v_inst_2231_,
    );
    crate::leanh::lean_dec_ref(v_inst_2231_);
    return v_res_2232_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(
    mut v_x_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2234_ = crate::leanh::lean_ctor_get(v_x_2233_, 0);
                v_range_2235_ = crate::leanh::lean_ctor_get(v_x_2233_, 1);
                v_isSharedCheck_2244_ = (!crate::leanh::lean_is_exclusive(v_x_2233_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2237_ = v_x_2233_;
                    v_isShared_2238_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2235_);
                    crate::leanh::lean_inc(v_treeMap_2234_);
                    crate::leanh::lean_dec(v_x_2233_);
                    v___x_2237_ = crate::leanh::lean_box(0);
                    v_isShared_2238_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2239_ = crate::leanh::lean_box(0);
                v___x_2240_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2234_,
                    v___x_2239_,
                );
                crate::leanh::lean_dec(v_treeMap_2234_);
                if v_isShared_2238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2237_, 0, v___x_2240_);
                    v___x_2242_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_range_2235_);
                    v___x_2242_ = v_reuseFailAlloc_2243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RioSlice_instToIterator(
    mut v_00_u03b1_2246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2247_: *mut crate::leanh::LeanObject,
    mut v_inst_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2249_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0;
    return v___f_2249_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2251_: *mut crate::leanh::LeanObject,
    mut v_inst_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(
        v_00_u03b1_2250_,
        v_00_u03b2_2251_,
        v_inst_2252_,
    );
    crate::leanh::lean_dec_ref(v_inst_2252_);
    return v_res_2253_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(
    mut v_carrier_2254_: *mut crate::leanh::LeanObject,
    mut v_range_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2256_, 0, v_carrier_2254_);
    crate::leanh::lean_ctor_set(v___x_2256_, 1, v_range_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(
    mut v_00_u03b1_2258_: *mut crate::leanh::LeanObject,
    mut v_inst_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2260_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0;
    return v___f_2260_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(
    mut v_00_u03b1_2261_: *mut crate::leanh::LeanObject,
    mut v_inst_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2263_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_2261_, v_inst_2262_);
    crate::leanh::lean_dec_ref(v_inst_2262_);
    return v_res_2263_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(
    mut v_x_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2265_ = crate::leanh::lean_ctor_get(v_x_2264_, 0);
                v_range_2266_ = crate::leanh::lean_ctor_get(v_x_2264_, 1);
                v_isSharedCheck_2275_ = (!crate::leanh::lean_is_exclusive(v_x_2264_)) as u8;
                if v_isSharedCheck_2275_ == 0 {
                    v___x_2268_ = v_x_2264_;
                    v_isShared_2269_ = v_isSharedCheck_2275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2266_);
                    crate::leanh::lean_inc(v_treeMap_2265_);
                    crate::leanh::lean_dec(v_x_2264_);
                    v___x_2268_ = crate::leanh::lean_box(0);
                    v_isShared_2269_ = v_isSharedCheck_2275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2270_ = crate::leanh::lean_box(0);
                v___x_2271_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2265_,
                    v___x_2270_,
                );
                crate::leanh::lean_dec(v_treeMap_2265_);
                if v_isShared_2269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_range_2266_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(
    mut v_00_u03b1_2277_: *mut crate::leanh::LeanObject,
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2279_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0;
    return v___f_2279_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2280_: *mut crate::leanh::LeanObject,
    mut v_inst_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ =
        l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_2280_, v_inst_2281_);
    crate::leanh::lean_dec_ref(v_inst_2281_);
    return v_res_2282_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(
    mut v_carrier_2283_: *mut crate::leanh::LeanObject,
    mut v_range_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2285_, 0, v_carrier_2283_);
    crate::leanh::lean_ctor_set(v___x_2285_, 1, v_range_2284_);
    return v___x_2285_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(
    mut v_00_u03b1_2287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2288_: *mut crate::leanh::LeanObject,
    mut v_inst_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2290_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0;
    return v___f_2290_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(
    mut v_00_u03b1_2291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2292_: *mut crate::leanh::LeanObject,
    mut v_inst_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2294_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(
        v_00_u03b1_2291_,
        v_00_u03b2_2292_,
        v_inst_2293_,
    );
    crate::leanh::lean_dec_ref(v_inst_2293_);
    return v_res_2294_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(
    mut v_x_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2296_ = crate::leanh::lean_ctor_get(v_x_2295_, 0);
                v_range_2297_ = crate::leanh::lean_ctor_get(v_x_2295_, 1);
                v_isSharedCheck_2306_ = (!crate::leanh::lean_is_exclusive(v_x_2295_)) as u8;
                if v_isSharedCheck_2306_ == 0 {
                    v___x_2299_ = v_x_2295_;
                    v_isShared_2300_ = v_isSharedCheck_2306_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_2297_);
                    crate::leanh::lean_inc(v_treeMap_2296_);
                    crate::leanh::lean_dec(v_x_2295_);
                    v___x_2299_ = crate::leanh::lean_box(0);
                    v_isShared_2300_ = v_isSharedCheck_2306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2301_ = crate::leanh::lean_box(0);
                v___x_2302_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2296_,
                    v___x_2301_,
                );
                crate::leanh::lean_dec(v_treeMap_2296_);
                if v_isShared_2300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2299_, 0, v___x_2302_);
                    v___x_2304_ = v___x_2299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_range_2297_);
                    v___x_2304_ = v_reuseFailAlloc_2305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(
    mut v_00_u03b1_2308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2309_: *mut crate::leanh::LeanObject,
    mut v_inst_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2311_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0;
    return v___f_2311_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2313_: *mut crate::leanh::LeanObject,
    mut v_inst_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(
        v_00_u03b1_2312_,
        v_00_u03b2_2313_,
        v_inst_2314_,
    );
    crate::leanh::lean_dec_ref(v_inst_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rccIterator___redArg(
    mut v_inst_2316_: *mut crate::leanh::LeanObject,
    mut v_t_2317_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2318_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = crate::leanh::lean_box(0);
    v___x_2321_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2316_,
        v_t_2317_,
        v_lowerBound_2318_,
        v___x_2320_,
    );
    v___x_2322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
    crate::leanh::lean_ctor_set(v___x_2322_, 1, v_upperBound_2319_);
    return v___x_2322_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rccIterator(
    mut v_00_u03b1_2323_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2324_: *mut crate::leanh::LeanObject,
    mut v_inst_2325_: *mut crate::leanh::LeanObject,
    mut v_t_2326_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2327_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = crate::leanh::lean_box(0);
    v___x_2330_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2325_,
        v_t_2326_,
        v_lowerBound_2327_,
        v___x_2329_,
    );
    v___x_2331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2331_, 0, v___x_2330_);
    crate::leanh::lean_ctor_set(v___x_2331_, 1, v_upperBound_2328_);
    return v___x_2331_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(
    mut v_carrier_2332_: *mut crate::leanh::LeanObject,
    mut v_range_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2334_, 0, v_carrier_2332_);
    crate::leanh::lean_ctor_set(v___x_2334_, 1, v_range_2333_);
    return v___x_2334_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice(
    mut v_00_u03b1_2336_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2337_: *mut crate::leanh::LeanObject,
    mut v_inst_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2339_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0;
    return v___f_2339_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(
    mut v_00_u03b1_2340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(
        v_00_u03b1_2340_,
        v_00_u03b2_2341_,
        v_inst_2342_,
    );
    crate::leanh::lean_dec_ref(v_inst_2342_);
    return v_res_2343_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2344_: *mut crate::leanh::LeanObject,
    mut v_x_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2346_ = crate::leanh::lean_ctor_get(v_x_2345_, 1);
                crate::leanh::lean_inc_ref(v_range_2346_);
                v_treeMap_2347_ = crate::leanh::lean_ctor_get(v_x_2345_, 0);
                crate::leanh::lean_inc(v_treeMap_2347_);
                crate::leanh::lean_dec_ref(v_x_2345_);
                v_lower_2348_ = crate::leanh::lean_ctor_get(v_range_2346_, 0);
                v_upper_2349_ = crate::leanh::lean_ctor_get(v_range_2346_, 1);
                v_isSharedCheck_2358_ = (!crate::leanh::lean_is_exclusive(v_range_2346_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v___x_2351_ = v_range_2346_;
                    v_isShared_2352_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2349_);
                    crate::leanh::lean_inc(v_lower_2348_);
                    crate::leanh::lean_dec(v_range_2346_);
                    v___x_2351_ = crate::leanh::lean_box(0);
                    v_isShared_2352_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2353_ = crate::leanh::lean_box(0);
                v___x_2354_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2344_,
                    v_treeMap_2347_,
                    v_lower_2348_,
                    v___x_2353_,
                );
                if v_isShared_2352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_upper_2349_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(
    mut v_inst_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2360_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2360_, 0, v_inst_2359_);
    return v___f_2360_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RccSlice_instToIterator(
    mut v_00_u03b1_2361_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2362_: *mut crate::leanh::LeanObject,
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2364_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2364_, 0, v_inst_2363_);
    return v___f_2364_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(
    mut v_carrier_2365_: *mut crate::leanh::LeanObject,
    mut v_range_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2367_, 0, v_carrier_2365_);
    crate::leanh::lean_ctor_set(v___x_2367_, 1, v_range_2366_);
    return v___x_2367_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(
    mut v_00_u03b1_2369_: *mut crate::leanh::LeanObject,
    mut v_inst_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2371_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0;
    return v___f_2371_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(
    mut v_00_u03b1_2372_: *mut crate::leanh::LeanObject,
    mut v_inst_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_2372_, v_inst_2373_);
    crate::leanh::lean_dec_ref(v_inst_2373_);
    return v_res_2374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2375_: *mut crate::leanh::LeanObject,
    mut v_x_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2377_ = crate::leanh::lean_ctor_get(v_x_2376_, 1);
                crate::leanh::lean_inc_ref(v_range_2377_);
                v_treeMap_2378_ = crate::leanh::lean_ctor_get(v_x_2376_, 0);
                crate::leanh::lean_inc(v_treeMap_2378_);
                crate::leanh::lean_dec_ref(v_x_2376_);
                v_lower_2379_ = crate::leanh::lean_ctor_get(v_range_2377_, 0);
                v_upper_2380_ = crate::leanh::lean_ctor_get(v_range_2377_, 1);
                v_isSharedCheck_2389_ = (!crate::leanh::lean_is_exclusive(v_range_2377_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v___x_2382_ = v_range_2377_;
                    v_isShared_2383_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2380_);
                    crate::leanh::lean_inc(v_lower_2379_);
                    crate::leanh::lean_dec(v_range_2377_);
                    v___x_2382_ = crate::leanh::lean_box(0);
                    v_isShared_2383_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2384_ = crate::leanh::lean_box(0);
                v___x_2385_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2375_,
                    v_treeMap_2378_,
                    v_lower_2379_,
                    v___x_2384_,
                );
                if v_isShared_2383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2382_, 0, v___x_2385_);
                    v___x_2387_ = v___x_2382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_upper_2380_);
                    v___x_2387_ = v_reuseFailAlloc_2388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(
    mut v_inst_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2391_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2391_, 0, v_inst_2390_);
    return v___f_2391_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(
    mut v_00_u03b1_2392_: *mut crate::leanh::LeanObject,
    mut v_inst_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2394_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2394_, 0, v_inst_2393_);
    return v___f_2394_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(
    mut v_carrier_2395_: *mut crate::leanh::LeanObject,
    mut v_range_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2397_, 0, v_carrier_2395_);
    crate::leanh::lean_ctor_set(v___x_2397_, 1, v_range_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(
    mut v_00_u03b1_2399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2400_: *mut crate::leanh::LeanObject,
    mut v_inst_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2402_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0;
    return v___f_2402_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(
    mut v_00_u03b1_2403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2404_: *mut crate::leanh::LeanObject,
    mut v_inst_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(
        v_00_u03b1_2403_,
        v_00_u03b2_2404_,
        v_inst_2405_,
    );
    crate::leanh::lean_dec_ref(v_inst_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2407_: *mut crate::leanh::LeanObject,
    mut v_x_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2409_ = crate::leanh::lean_ctor_get(v_x_2408_, 1);
                crate::leanh::lean_inc_ref(v_range_2409_);
                v_treeMap_2410_ = crate::leanh::lean_ctor_get(v_x_2408_, 0);
                crate::leanh::lean_inc(v_treeMap_2410_);
                crate::leanh::lean_dec_ref(v_x_2408_);
                v_lower_2411_ = crate::leanh::lean_ctor_get(v_range_2409_, 0);
                v_upper_2412_ = crate::leanh::lean_ctor_get(v_range_2409_, 1);
                v_isSharedCheck_2421_ = (!crate::leanh::lean_is_exclusive(v_range_2409_)) as u8;
                if v_isSharedCheck_2421_ == 0 {
                    v___x_2414_ = v_range_2409_;
                    v_isShared_2415_ = v_isSharedCheck_2421_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2412_);
                    crate::leanh::lean_inc(v_lower_2411_);
                    crate::leanh::lean_dec(v_range_2409_);
                    v___x_2414_ = crate::leanh::lean_box(0);
                    v_isShared_2415_ = v_isSharedCheck_2421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2416_ = crate::leanh::lean_box(0);
                v___x_2417_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2407_,
                    v_treeMap_2410_,
                    v_lower_2411_,
                    v___x_2416_,
                );
                if v_isShared_2415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_upper_2412_);
                    v___x_2419_ = v_reuseFailAlloc_2420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2423_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2423_, 0, v_inst_2422_);
    return v___f_2423_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(
    mut v_00_u03b1_2424_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2425_: *mut crate::leanh::LeanObject,
    mut v_inst_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2427_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2427_, 0, v_inst_2426_);
    return v___f_2427_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rcoIterator___redArg(
    mut v_inst_2428_: *mut crate::leanh::LeanObject,
    mut v_t_2429_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2430_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = crate::leanh::lean_box(0);
    v___x_2433_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2428_,
        v_t_2429_,
        v_lowerBound_2430_,
        v___x_2432_,
    );
    v___x_2434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2434_, 0, v___x_2433_);
    crate::leanh::lean_ctor_set(v___x_2434_, 1, v_upperBound_2431_);
    return v___x_2434_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rcoIterator(
    mut v_00_u03b1_2435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2436_: *mut crate::leanh::LeanObject,
    mut v_inst_2437_: *mut crate::leanh::LeanObject,
    mut v_t_2438_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2439_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = crate::leanh::lean_box(0);
    v___x_2442_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2437_,
        v_t_2438_,
        v_lowerBound_2439_,
        v___x_2441_,
    );
    v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 1, v_upperBound_2440_);
    return v___x_2443_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(
    mut v_carrier_2444_: *mut crate::leanh::LeanObject,
    mut v_range_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2446_, 0, v_carrier_2444_);
    crate::leanh::lean_ctor_set(v___x_2446_, 1, v_range_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(
    mut v_00_u03b1_2448_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2449_: *mut crate::leanh::LeanObject,
    mut v_inst_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2451_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0;
    return v___f_2451_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(
    mut v_00_u03b1_2452_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2453_: *mut crate::leanh::LeanObject,
    mut v_inst_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(
        v_00_u03b1_2452_,
        v_00_u03b2_2453_,
        v_inst_2454_,
    );
    crate::leanh::lean_dec_ref(v_inst_2454_);
    return v_res_2455_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2456_: *mut crate::leanh::LeanObject,
    mut v_x_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2458_ = crate::leanh::lean_ctor_get(v_x_2457_, 1);
                crate::leanh::lean_inc_ref(v_range_2458_);
                v_treeMap_2459_ = crate::leanh::lean_ctor_get(v_x_2457_, 0);
                crate::leanh::lean_inc(v_treeMap_2459_);
                crate::leanh::lean_dec_ref(v_x_2457_);
                v_lower_2460_ = crate::leanh::lean_ctor_get(v_range_2458_, 0);
                v_upper_2461_ = crate::leanh::lean_ctor_get(v_range_2458_, 1);
                v_isSharedCheck_2470_ = (!crate::leanh::lean_is_exclusive(v_range_2458_)) as u8;
                if v_isSharedCheck_2470_ == 0 {
                    v___x_2463_ = v_range_2458_;
                    v_isShared_2464_ = v_isSharedCheck_2470_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2461_);
                    crate::leanh::lean_inc(v_lower_2460_);
                    crate::leanh::lean_dec(v_range_2458_);
                    v___x_2463_ = crate::leanh::lean_box(0);
                    v_isShared_2464_ = v_isSharedCheck_2470_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2465_ = crate::leanh::lean_box(0);
                v___x_2466_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2456_,
                    v_treeMap_2459_,
                    v_lower_2460_,
                    v___x_2465_,
                );
                if v_isShared_2464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2466_);
                    v___x_2468_ = v___x_2463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_upper_2461_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2472_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2472_, 0, v_inst_2471_);
    return v___f_2472_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RcoSlice_instToIterator(
    mut v_00_u03b1_2473_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2474_: *mut crate::leanh::LeanObject,
    mut v_inst_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2476_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2476_, 0, v_inst_2475_);
    return v___f_2476_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(
    mut v_carrier_2477_: *mut crate::leanh::LeanObject,
    mut v_range_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2479_, 0, v_carrier_2477_);
    crate::leanh::lean_ctor_set(v___x_2479_, 1, v_range_2478_);
    return v___x_2479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(
    mut v_00_u03b1_2481_: *mut crate::leanh::LeanObject,
    mut v_inst_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2483_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0;
    return v___f_2483_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(
    mut v_00_u03b1_2484_: *mut crate::leanh::LeanObject,
    mut v_inst_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_2484_, v_inst_2485_);
    crate::leanh::lean_dec_ref(v_inst_2485_);
    return v_res_2486_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2487_: *mut crate::leanh::LeanObject,
    mut v_x_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2489_ = crate::leanh::lean_ctor_get(v_x_2488_, 1);
                crate::leanh::lean_inc_ref(v_range_2489_);
                v_treeMap_2490_ = crate::leanh::lean_ctor_get(v_x_2488_, 0);
                crate::leanh::lean_inc(v_treeMap_2490_);
                crate::leanh::lean_dec_ref(v_x_2488_);
                v_lower_2491_ = crate::leanh::lean_ctor_get(v_range_2489_, 0);
                v_upper_2492_ = crate::leanh::lean_ctor_get(v_range_2489_, 1);
                v_isSharedCheck_2501_ = (!crate::leanh::lean_is_exclusive(v_range_2489_)) as u8;
                if v_isSharedCheck_2501_ == 0 {
                    v___x_2494_ = v_range_2489_;
                    v_isShared_2495_ = v_isSharedCheck_2501_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2492_);
                    crate::leanh::lean_inc(v_lower_2491_);
                    crate::leanh::lean_dec(v_range_2489_);
                    v___x_2494_ = crate::leanh::lean_box(0);
                    v_isShared_2495_ = v_isSharedCheck_2501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2496_ = crate::leanh::lean_box(0);
                v___x_2497_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2487_,
                    v_treeMap_2490_,
                    v_lower_2491_,
                    v___x_2496_,
                );
                if v_isShared_2495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2494_, 0, v___x_2497_);
                    v___x_2499_ = v___x_2494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_upper_2492_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(
    mut v_inst_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2503_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2503_, 0, v_inst_2502_);
    return v___f_2503_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(
    mut v_00_u03b1_2504_: *mut crate::leanh::LeanObject,
    mut v_inst_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2506_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2506_, 0, v_inst_2505_);
    return v___f_2506_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(
    mut v_carrier_2507_: *mut crate::leanh::LeanObject,
    mut v_range_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2509_, 0, v_carrier_2507_);
    crate::leanh::lean_ctor_set(v___x_2509_, 1, v_range_2508_);
    return v___x_2509_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(
    mut v_00_u03b1_2511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2512_: *mut crate::leanh::LeanObject,
    mut v_inst_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2514_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0;
    return v___f_2514_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(
    mut v_00_u03b1_2515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2516_: *mut crate::leanh::LeanObject,
    mut v_inst_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(
        v_00_u03b1_2515_,
        v_00_u03b2_2516_,
        v_inst_2517_,
    );
    crate::leanh::lean_dec_ref(v_inst_2517_);
    return v_res_2518_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2519_: *mut crate::leanh::LeanObject,
    mut v_x_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2521_ = crate::leanh::lean_ctor_get(v_x_2520_, 1);
                crate::leanh::lean_inc_ref(v_range_2521_);
                v_treeMap_2522_ = crate::leanh::lean_ctor_get(v_x_2520_, 0);
                crate::leanh::lean_inc(v_treeMap_2522_);
                crate::leanh::lean_dec_ref(v_x_2520_);
                v_lower_2523_ = crate::leanh::lean_ctor_get(v_range_2521_, 0);
                v_upper_2524_ = crate::leanh::lean_ctor_get(v_range_2521_, 1);
                v_isSharedCheck_2533_ = (!crate::leanh::lean_is_exclusive(v_range_2521_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v___x_2526_ = v_range_2521_;
                    v_isShared_2527_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2524_);
                    crate::leanh::lean_inc(v_lower_2523_);
                    crate::leanh::lean_dec(v_range_2521_);
                    v___x_2526_ = crate::leanh::lean_box(0);
                    v_isShared_2527_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2528_ = crate::leanh::lean_box(0);
                v___x_2529_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2519_,
                    v_treeMap_2522_,
                    v_lower_2523_,
                    v___x_2528_,
                );
                if v_isShared_2527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_upper_2524_);
                    v___x_2531_ = v_reuseFailAlloc_2532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(
    mut v_inst_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2535_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2535_, 0, v_inst_2534_);
    return v___f_2535_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(
    mut v_00_u03b1_2536_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2537_: *mut crate::leanh::LeanObject,
    mut v_inst_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2539_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2539_, 0, v_inst_2538_);
    return v___f_2539_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rooIterator___redArg(
    mut v_inst_2540_: *mut crate::leanh::LeanObject,
    mut v_t_2541_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2542_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = crate::leanh::lean_box(0);
    v___x_2545_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2540_,
        v_t_2541_,
        v_lowerBound_2542_,
        v___x_2544_,
    );
    v___x_2546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    crate::leanh::lean_ctor_set(v___x_2546_, 1, v_upperBound_2543_);
    return v___x_2546_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rooIterator(
    mut v_00_u03b1_2547_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2548_: *mut crate::leanh::LeanObject,
    mut v_inst_2549_: *mut crate::leanh::LeanObject,
    mut v_t_2550_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2551_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = crate::leanh::lean_box(0);
    v___x_2554_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2549_,
        v_t_2550_,
        v_lowerBound_2551_,
        v___x_2553_,
    );
    v___x_2555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2554_);
    crate::leanh::lean_ctor_set(v___x_2555_, 1, v_upperBound_2552_);
    return v___x_2555_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(
    mut v_carrier_2556_: *mut crate::leanh::LeanObject,
    mut v_range_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2558_, 0, v_carrier_2556_);
    crate::leanh::lean_ctor_set(v___x_2558_, 1, v_range_2557_);
    return v___x_2558_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice(
    mut v_00_u03b1_2560_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2561_: *mut crate::leanh::LeanObject,
    mut v_inst_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2563_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0;
    return v___f_2563_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(
    mut v_00_u03b1_2564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2565_: *mut crate::leanh::LeanObject,
    mut v_inst_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(
        v_00_u03b1_2564_,
        v_00_u03b2_2565_,
        v_inst_2566_,
    );
    crate::leanh::lean_dec_ref(v_inst_2566_);
    return v_res_2567_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2568_: *mut crate::leanh::LeanObject,
    mut v_x_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2570_ = crate::leanh::lean_ctor_get(v_x_2569_, 1);
                crate::leanh::lean_inc_ref(v_range_2570_);
                v_treeMap_2571_ = crate::leanh::lean_ctor_get(v_x_2569_, 0);
                crate::leanh::lean_inc(v_treeMap_2571_);
                crate::leanh::lean_dec_ref(v_x_2569_);
                v_lower_2572_ = crate::leanh::lean_ctor_get(v_range_2570_, 0);
                v_upper_2573_ = crate::leanh::lean_ctor_get(v_range_2570_, 1);
                v_isSharedCheck_2582_ = (!crate::leanh::lean_is_exclusive(v_range_2570_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v___x_2575_ = v_range_2570_;
                    v_isShared_2576_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2573_);
                    crate::leanh::lean_inc(v_lower_2572_);
                    crate::leanh::lean_dec(v_range_2570_);
                    v___x_2575_ = crate::leanh::lean_box(0);
                    v_isShared_2576_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2577_ = crate::leanh::lean_box(0);
                v___x_2578_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2568_,
                    v_treeMap_2571_,
                    v_lower_2572_,
                    v___x_2577_,
                );
                if v_isShared_2576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2578_);
                    v___x_2580_ = v___x_2575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_upper_2573_);
                    v___x_2580_ = v_reuseFailAlloc_2581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(
    mut v_inst_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2584_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2584_, 0, v_inst_2583_);
    return v___f_2584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RooSlice_instToIterator(
    mut v_00_u03b1_2585_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2586_: *mut crate::leanh::LeanObject,
    mut v_inst_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2588_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2588_, 0, v_inst_2587_);
    return v___f_2588_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(
    mut v_carrier_2589_: *mut crate::leanh::LeanObject,
    mut v_range_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2591_, 0, v_carrier_2589_);
    crate::leanh::lean_ctor_set(v___x_2591_, 1, v_range_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(
    mut v_00_u03b1_2593_: *mut crate::leanh::LeanObject,
    mut v_inst_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2595_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0;
    return v___f_2595_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(
    mut v_00_u03b1_2596_: *mut crate::leanh::LeanObject,
    mut v_inst_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_2596_, v_inst_2597_);
    crate::leanh::lean_dec_ref(v_inst_2597_);
    return v_res_2598_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2599_: *mut crate::leanh::LeanObject,
    mut v_x_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2601_ = crate::leanh::lean_ctor_get(v_x_2600_, 1);
                crate::leanh::lean_inc_ref(v_range_2601_);
                v_treeMap_2602_ = crate::leanh::lean_ctor_get(v_x_2600_, 0);
                crate::leanh::lean_inc(v_treeMap_2602_);
                crate::leanh::lean_dec_ref(v_x_2600_);
                v_lower_2603_ = crate::leanh::lean_ctor_get(v_range_2601_, 0);
                v_upper_2604_ = crate::leanh::lean_ctor_get(v_range_2601_, 1);
                v_isSharedCheck_2613_ = (!crate::leanh::lean_is_exclusive(v_range_2601_)) as u8;
                if v_isSharedCheck_2613_ == 0 {
                    v___x_2606_ = v_range_2601_;
                    v_isShared_2607_ = v_isSharedCheck_2613_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2604_);
                    crate::leanh::lean_inc(v_lower_2603_);
                    crate::leanh::lean_dec(v_range_2601_);
                    v___x_2606_ = crate::leanh::lean_box(0);
                    v_isShared_2607_ = v_isSharedCheck_2613_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2608_ = crate::leanh::lean_box(0);
                v___x_2609_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2599_,
                    v_treeMap_2602_,
                    v_lower_2603_,
                    v___x_2608_,
                );
                if v_isShared_2607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2606_, 0, v___x_2609_);
                    v___x_2611_ = v___x_2606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2612_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_upper_2604_);
                    v___x_2611_ = v_reuseFailAlloc_2612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(
    mut v_inst_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2615_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2615_, 0, v_inst_2614_);
    return v___f_2615_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(
    mut v_00_u03b1_2616_: *mut crate::leanh::LeanObject,
    mut v_inst_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2618_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2618_, 0, v_inst_2617_);
    return v___f_2618_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(
    mut v_carrier_2619_: *mut crate::leanh::LeanObject,
    mut v_range_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2621_, 0, v_carrier_2619_);
    crate::leanh::lean_ctor_set(v___x_2621_, 1, v_range_2620_);
    return v___x_2621_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(
    mut v_00_u03b1_2623_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2624_: *mut crate::leanh::LeanObject,
    mut v_inst_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2626_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0;
    return v___f_2626_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(
    mut v_00_u03b1_2627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2628_: *mut crate::leanh::LeanObject,
    mut v_inst_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(
        v_00_u03b1_2627_,
        v_00_u03b2_2628_,
        v_inst_2629_,
    );
    crate::leanh::lean_dec_ref(v_inst_2629_);
    return v_res_2630_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2631_: *mut crate::leanh::LeanObject,
    mut v_x_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2633_ = crate::leanh::lean_ctor_get(v_x_2632_, 1);
                crate::leanh::lean_inc_ref(v_range_2633_);
                v_treeMap_2634_ = crate::leanh::lean_ctor_get(v_x_2632_, 0);
                crate::leanh::lean_inc(v_treeMap_2634_);
                crate::leanh::lean_dec_ref(v_x_2632_);
                v_lower_2635_ = crate::leanh::lean_ctor_get(v_range_2633_, 0);
                v_upper_2636_ = crate::leanh::lean_ctor_get(v_range_2633_, 1);
                v_isSharedCheck_2645_ = (!crate::leanh::lean_is_exclusive(v_range_2633_)) as u8;
                if v_isSharedCheck_2645_ == 0 {
                    v___x_2638_ = v_range_2633_;
                    v_isShared_2639_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2636_);
                    crate::leanh::lean_inc(v_lower_2635_);
                    crate::leanh::lean_dec(v_range_2633_);
                    v___x_2638_ = crate::leanh::lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2640_ = crate::leanh::lean_box(0);
                v___x_2641_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2631_,
                    v_treeMap_2634_,
                    v_lower_2635_,
                    v___x_2640_,
                );
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2641_);
                    v___x_2643_ = v___x_2638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_upper_2636_);
                    v___x_2643_ = v_reuseFailAlloc_2644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(
    mut v_inst_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2647_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2647_, 0, v_inst_2646_);
    return v___f_2647_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(
    mut v_00_u03b1_2648_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2649_: *mut crate::leanh::LeanObject,
    mut v_inst_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2651_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2651_, 0, v_inst_2650_);
    return v___f_2651_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rocIterator___redArg(
    mut v_inst_2652_: *mut crate::leanh::LeanObject,
    mut v_t_2653_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2654_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = crate::leanh::lean_box(0);
    v___x_2657_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2652_,
        v_t_2653_,
        v_lowerBound_2654_,
        v___x_2656_,
    );
    v___x_2658_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2658_, 0, v___x_2657_);
    crate::leanh::lean_ctor_set(v___x_2658_, 1, v_upperBound_2655_);
    return v___x_2658_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rocIterator(
    mut v_00_u03b1_2659_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2660_: *mut crate::leanh::LeanObject,
    mut v_inst_2661_: *mut crate::leanh::LeanObject,
    mut v_t_2662_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2663_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = crate::leanh::lean_box(0);
    v___x_2666_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2661_,
        v_t_2662_,
        v_lowerBound_2663_,
        v___x_2665_,
    );
    v___x_2667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2667_, 0, v___x_2666_);
    crate::leanh::lean_ctor_set(v___x_2667_, 1, v_upperBound_2664_);
    return v___x_2667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(
    mut v_carrier_2668_: *mut crate::leanh::LeanObject,
    mut v_range_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2670_, 0, v_carrier_2668_);
    crate::leanh::lean_ctor_set(v___x_2670_, 1, v_range_2669_);
    return v___x_2670_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice(
    mut v_00_u03b1_2672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2673_: *mut crate::leanh::LeanObject,
    mut v_inst_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2675_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0;
    return v___f_2675_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(
    mut v_00_u03b1_2676_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2677_: *mut crate::leanh::LeanObject,
    mut v_inst_2678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(
        v_00_u03b1_2676_,
        v_00_u03b2_2677_,
        v_inst_2678_,
    );
    crate::leanh::lean_dec_ref(v_inst_2678_);
    return v_res_2679_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2680_: *mut crate::leanh::LeanObject,
    mut v_x_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2682_ = crate::leanh::lean_ctor_get(v_x_2681_, 1);
                crate::leanh::lean_inc_ref(v_range_2682_);
                v_treeMap_2683_ = crate::leanh::lean_ctor_get(v_x_2681_, 0);
                crate::leanh::lean_inc(v_treeMap_2683_);
                crate::leanh::lean_dec_ref(v_x_2681_);
                v_lower_2684_ = crate::leanh::lean_ctor_get(v_range_2682_, 0);
                v_upper_2685_ = crate::leanh::lean_ctor_get(v_range_2682_, 1);
                v_isSharedCheck_2694_ = (!crate::leanh::lean_is_exclusive(v_range_2682_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v___x_2687_ = v_range_2682_;
                    v_isShared_2688_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2685_);
                    crate::leanh::lean_inc(v_lower_2684_);
                    crate::leanh::lean_dec(v_range_2682_);
                    v___x_2687_ = crate::leanh::lean_box(0);
                    v_isShared_2688_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2689_ = crate::leanh::lean_box(0);
                v___x_2690_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2680_,
                    v_treeMap_2683_,
                    v_lower_2684_,
                    v___x_2689_,
                );
                if v_isShared_2688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2690_);
                    v___x_2692_ = v___x_2687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_upper_2685_);
                    v___x_2692_ = v_reuseFailAlloc_2693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(
    mut v_inst_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2696_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2696_, 0, v_inst_2695_);
    return v___f_2696_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RocSlice_instToIterator(
    mut v_00_u03b1_2697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2698_: *mut crate::leanh::LeanObject,
    mut v_inst_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2700_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2700_, 0, v_inst_2699_);
    return v___f_2700_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(
    mut v_carrier_2701_: *mut crate::leanh::LeanObject,
    mut v_range_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2703_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2703_, 0, v_carrier_2701_);
    crate::leanh::lean_ctor_set(v___x_2703_, 1, v_range_2702_);
    return v___x_2703_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(
    mut v_00_u03b1_2705_: *mut crate::leanh::LeanObject,
    mut v_inst_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2707_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0;
    return v___f_2707_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(
    mut v_00_u03b1_2708_: *mut crate::leanh::LeanObject,
    mut v_inst_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_2708_, v_inst_2709_);
    crate::leanh::lean_dec_ref(v_inst_2709_);
    return v_res_2710_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2711_: *mut crate::leanh::LeanObject,
    mut v_x_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2713_ = crate::leanh::lean_ctor_get(v_x_2712_, 1);
                crate::leanh::lean_inc_ref(v_range_2713_);
                v_treeMap_2714_ = crate::leanh::lean_ctor_get(v_x_2712_, 0);
                crate::leanh::lean_inc(v_treeMap_2714_);
                crate::leanh::lean_dec_ref(v_x_2712_);
                v_lower_2715_ = crate::leanh::lean_ctor_get(v_range_2713_, 0);
                v_upper_2716_ = crate::leanh::lean_ctor_get(v_range_2713_, 1);
                v_isSharedCheck_2725_ = (!crate::leanh::lean_is_exclusive(v_range_2713_)) as u8;
                if v_isSharedCheck_2725_ == 0 {
                    v___x_2718_ = v_range_2713_;
                    v_isShared_2719_ = v_isSharedCheck_2725_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2716_);
                    crate::leanh::lean_inc(v_lower_2715_);
                    crate::leanh::lean_dec(v_range_2713_);
                    v___x_2718_ = crate::leanh::lean_box(0);
                    v_isShared_2719_ = v_isSharedCheck_2725_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2720_ = crate::leanh::lean_box(0);
                v___x_2721_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2711_,
                    v_treeMap_2714_,
                    v_lower_2715_,
                    v___x_2720_,
                );
                if v_isShared_2719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2721_);
                    v___x_2723_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_upper_2716_);
                    v___x_2723_ = v_reuseFailAlloc_2724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(
    mut v_inst_2726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2727_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2727_, 0, v_inst_2726_);
    return v___f_2727_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(
    mut v_00_u03b1_2728_: *mut crate::leanh::LeanObject,
    mut v_inst_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2730_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2730_, 0, v_inst_2729_);
    return v___f_2730_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(
    mut v_carrier_2731_: *mut crate::leanh::LeanObject,
    mut v_range_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2733_, 0, v_carrier_2731_);
    crate::leanh::lean_ctor_set(v___x_2733_, 1, v_range_2732_);
    return v___x_2733_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(
    mut v_00_u03b1_2735_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2736_: *mut crate::leanh::LeanObject,
    mut v_inst_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2738_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0;
    return v___f_2738_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(
    mut v_00_u03b1_2739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2740_: *mut crate::leanh::LeanObject,
    mut v_inst_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2742_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(
        v_00_u03b1_2739_,
        v_00_u03b2_2740_,
        v_inst_2741_,
    );
    crate::leanh::lean_dec_ref(v_inst_2741_);
    return v_res_2742_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2743_: *mut crate::leanh::LeanObject,
    mut v_x_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2745_ = crate::leanh::lean_ctor_get(v_x_2744_, 1);
                crate::leanh::lean_inc_ref(v_range_2745_);
                v_treeMap_2746_ = crate::leanh::lean_ctor_get(v_x_2744_, 0);
                crate::leanh::lean_inc(v_treeMap_2746_);
                crate::leanh::lean_dec_ref(v_x_2744_);
                v_lower_2747_ = crate::leanh::lean_ctor_get(v_range_2745_, 0);
                v_upper_2748_ = crate::leanh::lean_ctor_get(v_range_2745_, 1);
                v_isSharedCheck_2757_ = (!crate::leanh::lean_is_exclusive(v_range_2745_)) as u8;
                if v_isSharedCheck_2757_ == 0 {
                    v___x_2750_ = v_range_2745_;
                    v_isShared_2751_ = v_isSharedCheck_2757_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_2748_);
                    crate::leanh::lean_inc(v_lower_2747_);
                    crate::leanh::lean_dec(v_range_2745_);
                    v___x_2750_ = crate::leanh::lean_box(0);
                    v_isShared_2751_ = v_isSharedCheck_2757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2752_ = crate::leanh::lean_box(0);
                v___x_2753_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2743_,
                    v_treeMap_2746_,
                    v_lower_2747_,
                    v___x_2752_,
                );
                if v_isShared_2751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_upper_2748_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(
    mut v_inst_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2759_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2759_, 0, v_inst_2758_);
    return v___f_2759_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(
    mut v_00_u03b1_2760_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2761_: *mut crate::leanh::LeanObject,
    mut v_inst_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2763_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2763_, 0, v_inst_2762_);
    return v___f_2763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rciIterator___redArg(
    mut v_inst_2764_: *mut crate::leanh::LeanObject,
    mut v_t_2765_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = crate::leanh::lean_box(0);
    v___x_2768_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2764_,
        v_t_2765_,
        v_lowerBound_2766_,
        v___x_2767_,
    );
    return v___x_2768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rciIterator(
    mut v_00_u03b1_2769_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2770_: *mut crate::leanh::LeanObject,
    mut v_inst_2771_: *mut crate::leanh::LeanObject,
    mut v_t_2772_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = crate::leanh::lean_box(0);
    v___x_2775_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2771_,
        v_t_2772_,
        v_lowerBound_2773_,
        v___x_2774_,
    );
    return v___x_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(
    mut v_carrier_2776_: *mut crate::leanh::LeanObject,
    mut v_range_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2778_, 0, v_carrier_2776_);
    crate::leanh::lean_ctor_set(v___x_2778_, 1, v_range_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice(
    mut v_00_u03b1_2780_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2781_: *mut crate::leanh::LeanObject,
    mut v_inst_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2783_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0;
    return v___f_2783_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(
    mut v_00_u03b1_2784_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(
        v_00_u03b1_2784_,
        v_00_u03b2_2785_,
        v_inst_2786_,
    );
    crate::leanh::lean_dec_ref(v_inst_2786_);
    return v_res_2787_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2790_ = crate::leanh::lean_ctor_get(v_x_2789_, 0);
    crate::leanh::lean_inc(v_treeMap_2790_);
    v_range_2791_ = crate::leanh::lean_ctor_get(v_x_2789_, 1);
    crate::leanh::lean_inc(v_range_2791_);
    crate::leanh::lean_dec_ref(v_x_2789_);
    v___x_2792_ = crate::leanh::lean_box(0);
    v___x_2793_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2788_,
        v_treeMap_2790_,
        v_range_2791_,
        v___x_2792_,
    );
    return v___x_2793_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(
    mut v_inst_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2795_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2795_, 0, v_inst_2794_);
    return v___f_2795_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator(
    mut v_00_u03b1_2796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2797_: *mut crate::leanh::LeanObject,
    mut v_inst_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2799_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2799_, 0, v_inst_2798_);
    return v___f_2799_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(
    mut v_carrier_2800_: *mut crate::leanh::LeanObject,
    mut v_range_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2802_, 0, v_carrier_2800_);
    crate::leanh::lean_ctor_set(v___x_2802_, 1, v_range_2801_);
    return v___x_2802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(
    mut v_00_u03b1_2804_: *mut crate::leanh::LeanObject,
    mut v_inst_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2806_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0;
    return v___f_2806_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(
    mut v_00_u03b1_2807_: *mut crate::leanh::LeanObject,
    mut v_inst_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_2807_, v_inst_2808_);
    crate::leanh::lean_dec_ref(v_inst_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2810_: *mut crate::leanh::LeanObject,
    mut v_x_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2812_ = crate::leanh::lean_ctor_get(v_x_2811_, 0);
    crate::leanh::lean_inc(v_treeMap_2812_);
    v_range_2813_ = crate::leanh::lean_ctor_get(v_x_2811_, 1);
    crate::leanh::lean_inc(v_range_2813_);
    crate::leanh::lean_dec_ref(v_x_2811_);
    v___x_2814_ = crate::leanh::lean_box(0);
    v___x_2815_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2810_,
        v_treeMap_2812_,
        v_range_2813_,
        v___x_2814_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(
    mut v_inst_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2817_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2817_, 0, v_inst_2816_);
    return v___f_2817_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(
    mut v_00_u03b1_2818_: *mut crate::leanh::LeanObject,
    mut v_inst_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2820_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2820_, 0, v_inst_2819_);
    return v___f_2820_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(
    mut v_carrier_2821_: *mut crate::leanh::LeanObject,
    mut v_range_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2823_, 0, v_carrier_2821_);
    crate::leanh::lean_ctor_set(v___x_2823_, 1, v_range_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(
    mut v_00_u03b1_2825_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2828_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0;
    return v___f_2828_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(
    mut v_00_u03b1_2829_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2830_: *mut crate::leanh::LeanObject,
    mut v_inst_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(
        v_00_u03b1_2829_,
        v_00_u03b2_2830_,
        v_inst_2831_,
    );
    crate::leanh::lean_dec_ref(v_inst_2831_);
    return v_res_2832_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2833_: *mut crate::leanh::LeanObject,
    mut v_x_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2835_ = crate::leanh::lean_ctor_get(v_x_2834_, 0);
    crate::leanh::lean_inc(v_treeMap_2835_);
    v_range_2836_ = crate::leanh::lean_ctor_get(v_x_2834_, 1);
    crate::leanh::lean_inc(v_range_2836_);
    crate::leanh::lean_dec_ref(v_x_2834_);
    v___x_2837_ = crate::leanh::lean_box(0);
    v___x_2838_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2833_,
        v_treeMap_2835_,
        v_range_2836_,
        v___x_2837_,
    );
    return v___x_2838_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(
    mut v_inst_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2840_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2840_, 0, v_inst_2839_);
    return v___f_2840_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(
    mut v_00_u03b1_2841_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2842_: *mut crate::leanh::LeanObject,
    mut v_inst_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2844_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2844_, 0, v_inst_2843_);
    return v___f_2844_;
}
pub unsafe fn l_Std_DTreeMap_Internal_roiIterator___redArg(
    mut v_inst_2845_: *mut crate::leanh::LeanObject,
    mut v_t_2846_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = crate::leanh::lean_box(0);
    v___x_2849_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2845_,
        v_t_2846_,
        v_lowerBound_2847_,
        v___x_2848_,
    );
    return v___x_2849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_roiIterator(
    mut v_00_u03b1_2850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2851_: *mut crate::leanh::LeanObject,
    mut v_inst_2852_: *mut crate::leanh::LeanObject,
    mut v_t_2853_: *mut crate::leanh::LeanObject,
    mut v_lowerBound_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2855_ = crate::leanh::lean_box(0);
    v___x_2856_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2852_,
        v_t_2853_,
        v_lowerBound_2854_,
        v___x_2855_,
    );
    return v___x_2856_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(
    mut v_carrier_2857_: *mut crate::leanh::LeanObject,
    mut v_range_2858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2859_, 0, v_carrier_2857_);
    crate::leanh::lean_ctor_set(v___x_2859_, 1, v_range_2858_);
    return v___x_2859_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(
    mut v_00_u03b1_2861_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2862_: *mut crate::leanh::LeanObject,
    mut v_inst_2863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2864_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0;
    return v___f_2864_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(
    mut v_00_u03b1_2865_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2866_: *mut crate::leanh::LeanObject,
    mut v_inst_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(
        v_00_u03b1_2865_,
        v_00_u03b2_2866_,
        v_inst_2867_,
    );
    crate::leanh::lean_dec_ref(v_inst_2867_);
    return v_res_2868_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2869_: *mut crate::leanh::LeanObject,
    mut v_x_2870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2871_ = crate::leanh::lean_ctor_get(v_x_2870_, 0);
    crate::leanh::lean_inc(v_treeMap_2871_);
    v_range_2872_ = crate::leanh::lean_ctor_get(v_x_2870_, 1);
    crate::leanh::lean_inc(v_range_2872_);
    crate::leanh::lean_dec_ref(v_x_2870_);
    v___x_2873_ = crate::leanh::lean_box(0);
    v___x_2874_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2869_,
        v_treeMap_2871_,
        v_range_2872_,
        v___x_2873_,
    );
    return v___x_2874_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2876_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2876_, 0, v_inst_2875_);
    return v___f_2876_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator(
    mut v_00_u03b1_2877_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2880_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2880_, 0, v_inst_2879_);
    return v___f_2880_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(
    mut v_carrier_2881_: *mut crate::leanh::LeanObject,
    mut v_range_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2883_, 0, v_carrier_2881_);
    crate::leanh::lean_ctor_set(v___x_2883_, 1, v_range_2882_);
    return v___x_2883_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(
    mut v_00_u03b1_2885_: *mut crate::leanh::LeanObject,
    mut v_inst_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2887_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0;
    return v___f_2887_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(
    mut v_00_u03b1_2888_: *mut crate::leanh::LeanObject,
    mut v_inst_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_2888_, v_inst_2889_);
    crate::leanh::lean_dec_ref(v_inst_2889_);
    return v_res_2890_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2891_: *mut crate::leanh::LeanObject,
    mut v_x_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2893_ = crate::leanh::lean_ctor_get(v_x_2892_, 0);
    crate::leanh::lean_inc(v_treeMap_2893_);
    v_range_2894_ = crate::leanh::lean_ctor_get(v_x_2892_, 1);
    crate::leanh::lean_inc(v_range_2894_);
    crate::leanh::lean_dec_ref(v_x_2892_);
    v___x_2895_ = crate::leanh::lean_box(0);
    v___x_2896_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2891_,
        v_treeMap_2893_,
        v_range_2894_,
        v___x_2895_,
    );
    return v___x_2896_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(
    mut v_inst_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2898_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2898_, 0, v_inst_2897_);
    return v___f_2898_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(
    mut v_00_u03b1_2899_: *mut crate::leanh::LeanObject,
    mut v_inst_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2901_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2901_, 0, v_inst_2900_);
    return v___f_2901_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(
    mut v_carrier_2902_: *mut crate::leanh::LeanObject,
    mut v_range_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2904_, 0, v_carrier_2902_);
    crate::leanh::lean_ctor_set(v___x_2904_, 1, v_range_2903_);
    return v___x_2904_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(
    mut v_00_u03b1_2906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2907_: *mut crate::leanh::LeanObject,
    mut v_inst_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2909_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0;
    return v___f_2909_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(
    mut v_00_u03b1_2910_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2911_: *mut crate::leanh::LeanObject,
    mut v_inst_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(
        v_00_u03b1_2910_,
        v_00_u03b2_2911_,
        v_inst_2912_,
    );
    crate::leanh::lean_dec_ref(v_inst_2912_);
    return v_res_2913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2914_: *mut crate::leanh::LeanObject,
    mut v_x_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2916_ = crate::leanh::lean_ctor_get(v_x_2915_, 0);
    crate::leanh::lean_inc(v_treeMap_2916_);
    v_range_2917_ = crate::leanh::lean_ctor_get(v_x_2915_, 1);
    crate::leanh::lean_inc(v_range_2917_);
    crate::leanh::lean_dec_ref(v_x_2915_);
    v___x_2918_ = crate::leanh::lean_box(0);
    v___x_2919_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2914_,
        v_treeMap_2916_,
        v_range_2917_,
        v___x_2918_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(
    mut v_inst_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2921_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2921_, 0, v_inst_2920_);
    return v___f_2921_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(
    mut v_00_u03b1_2922_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2923_: *mut crate::leanh::LeanObject,
    mut v_inst_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2925_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2925_, 0, v_inst_2924_);
    return v___f_2925_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___redArg(
    mut v_t_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = crate::leanh::lean_box(0);
    v___x_2928_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_2926_, v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(
    mut v_t_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_2929_);
    crate::leanh::lean_dec(v_t_2929_);
    return v_res_2930_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator(
    mut v_00_u03b1_2931_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2932_: *mut crate::leanh::LeanObject,
    mut v_t_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_2933_);
    return v___x_2934_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___boxed(
    mut v_00_u03b1_2935_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2936_: *mut crate::leanh::LeanObject,
    mut v_t_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2938_ =
        l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_2935_, v_00_u03b2_2936_, v_t_2937_);
    crate::leanh::lean_dec(v_t_2937_);
    return v_res_2938_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(
    mut v_carrier_2939_: *mut crate::leanh::LeanObject,
    mut v_range_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2941_, 0, v_carrier_2939_);
    crate::leanh::lean_ctor_set(v___x_2941_, 1, v_range_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(
    mut v_00_u03b1_2943_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2945_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0;
    return v___f_2945_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(
    mut v_x_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2947_ = crate::leanh::lean_ctor_get(v_x_2946_, 0);
    v___x_2948_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_2947_);
    return v___x_2948_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(v_x_2949_);
    crate::leanh::lean_dec_ref(v_x_2949_);
    return v_res_2950_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator(
    mut v_00_u03b1_2952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2954_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0;
    return v___f_2954_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(
    mut v_carrier_2955_: *mut crate::leanh::LeanObject,
    mut v_range_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2957_, 0, v_carrier_2955_);
    crate::leanh::lean_ctor_set(v___x_2957_, 1, v_range_2956_);
    return v___x_2957_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(
    mut v_00_u03b1_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2960_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0;
    return v___f_2960_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(
    mut v_x_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2962_ = crate::leanh::lean_ctor_get(v_x_2961_, 0);
    v___x_2963_ = crate::leanh::lean_box(0);
    v___x_2964_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_2962_, v___x_2963_);
    return v___x_2964_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(v_x_2965_);
    crate::leanh::lean_dec_ref(v_x_2965_);
    return v_res_2966_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(
    mut v_00_u03b1_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2969_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0;
    return v___f_2969_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(
    mut v_carrier_2970_: *mut crate::leanh::LeanObject,
    mut v_range_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2972_, 0, v_carrier_2970_);
    crate::leanh::lean_ctor_set(v___x_2972_, 1, v_range_2971_);
    return v___x_2972_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(
    mut v_00_u03b1_2974_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2976_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0;
    return v___f_2976_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(
    mut v_x_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_treeMap_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2978_ = crate::leanh::lean_ctor_get(v_x_2977_, 0);
    v___x_2979_ = crate::leanh::lean_box(0);
    v___x_2980_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(v_x_2981_);
    crate::leanh::lean_dec_ref(v_x_2981_);
    return v_res_2982_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(
    mut v_00_u03b1_2984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2986_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0;
    return v___f_2986_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_InternalLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Zipper(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Zipper(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_InternalLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
}
