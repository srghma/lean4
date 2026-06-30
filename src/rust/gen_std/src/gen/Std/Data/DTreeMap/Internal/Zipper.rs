// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Zipper
// Imports: Std.Data.Iterators.Lemmas.Producers.Slice Init.Data.Slice Std.Data.DTreeMap.Internal.Lemmas Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Slice.InternalLemmas
use crate::ffi::lean_nat_add;
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
pub static l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Zipper_step___redArg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value:
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
    m_fun: l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_t_1495_: *mut leanh::LeanObject,
    mut v_lowerBound_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1495_) == 0 {
                    v_size_1497_ = leanh::lean_ctor_get(v_t_1495_, 0);
                    v_k_1498_ = leanh::lean_ctor_get(v_t_1495_, 1);
                    v_v_1499_ = leanh::lean_ctor_get(v_t_1495_, 2);
                    v_l_1500_ = leanh::lean_ctor_get(v_t_1495_, 3);
                    v_r_1501_ = leanh::lean_ctor_get(v_t_1495_, 4);
                    v_isSharedCheck_1516_ = (!leanh::lean_is_exclusive(v_t_1495_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1503_ = v_t_1495_;
                        v_isShared_1504_ = v_isSharedCheck_1516_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1501_);
                        leanh::lean_inc(v_l_1500_);
                        leanh::lean_inc(v_v_1499_);
                        leanh::lean_inc(v_k_1498_);
                        leanh::lean_inc(v_size_1497_);
                        leanh::lean_dec(v_t_1495_);
                        v___x_1503_ = leanh::lean_box(0);
                        v_isShared_1504_ = v_isSharedCheck_1516_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_lowerBound_1496_);
                    leanh::lean_dec_ref(v_inst_1494_);
                    return v_t_1495_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1494_);
                leanh::lean_inc(v_k_1498_);
                leanh::lean_inc(v_lowerBound_1496_);
                v___x_1505_ =
                    leanh::lean_apply_2(v_inst_1494_, v_lowerBound_1496_, v_k_1498_);
                v___x_1506_ = (leanh::lean_unbox(v___x_1505_) as u8);
                match v___x_1506_ {
                    0 => {
                        v___x_1507_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_1494_, v_l_1500_, v_lowerBound_1496_);
                        if v_isShared_1504_ == 0 {
                            leanh::lean_ctor_set(v___x_1503_, 3, v___x_1507_);
                            v___x_1509_ = v___x_1503_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1510_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_size_1497_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1498_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1499_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1501_);
                            v___x_1509_ = v_reuseFailAlloc_1510_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_l_1500_);
                        leanh::lean_dec(v_lowerBound_1496_);
                        leanh::lean_dec_ref(v_inst_1494_);
                        v___x_1511_ = leanh::lean_box(1);
                        if v_isShared_1504_ == 0 {
                            leanh::lean_ctor_set(v___x_1503_, 3, v___x_1511_);
                            v___x_1513_ = v___x_1503_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1514_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_size_1497_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1498_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1499_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 3, v___x_1511_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1501_);
                            v___x_1513_ = v_reuseFailAlloc_1514_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_1503_);
                        leanh::lean_dec(v_l_1500_);
                        leanh::lean_dec(v_v_1499_);
                        leanh::lean_dec(v_k_1498_);
                        leanh::lean_dec(v_size_1497_);
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
    mut v_00_u03b1_1517_: *mut leanh::LeanObject,
    mut v_00_u03b2_1518_: *mut leanh::LeanObject,
    mut v_inst_1519_: *mut leanh::LeanObject,
    mut v_t_1520_: *mut leanh::LeanObject,
    mut v_lowerBound_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_1519_, v_t_1520_, v_lowerBound_1521_);
    return v___x_1522_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(
    mut v_inst_1523_: *mut leanh::LeanObject,
    mut v_t_1524_: *mut leanh::LeanObject,
    mut v_lowerBound_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1524_) == 0 {
                    v_size_1526_ = leanh::lean_ctor_get(v_t_1524_, 0);
                    v_k_1527_ = leanh::lean_ctor_get(v_t_1524_, 1);
                    v_v_1528_ = leanh::lean_ctor_get(v_t_1524_, 2);
                    v_l_1529_ = leanh::lean_ctor_get(v_t_1524_, 3);
                    v_r_1530_ = leanh::lean_ctor_get(v_t_1524_, 4);
                    v_isSharedCheck_1541_ = (!leanh::lean_is_exclusive(v_t_1524_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1532_ = v_t_1524_;
                        v_isShared_1533_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1530_);
                        leanh::lean_inc(v_l_1529_);
                        leanh::lean_inc(v_v_1528_);
                        leanh::lean_inc(v_k_1527_);
                        leanh::lean_inc(v_size_1526_);
                        leanh::lean_dec(v_t_1524_);
                        v___x_1532_ = leanh::lean_box(0);
                        v_isShared_1533_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_lowerBound_1525_);
                    leanh::lean_dec_ref(v_inst_1523_);
                    return v_t_1524_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1523_);
                leanh::lean_inc(v_k_1527_);
                leanh::lean_inc(v_lowerBound_1525_);
                v___x_1534_ =
                    leanh::lean_apply_2(v_inst_1523_, v_lowerBound_1525_, v_k_1527_);
                v___x_1535_ = (leanh::lean_unbox(v___x_1534_) as u8);
                match v___x_1535_ {
                    0 => {
                        v___x_1536_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_1523_, v_l_1529_, v_lowerBound_1525_);
                        if v_isShared_1533_ == 0 {
                            leanh::lean_ctor_set(v___x_1532_, 3, v___x_1536_);
                            v___x_1538_ = v___x_1532_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1539_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_size_1526_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1527_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1528_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 3, v___x_1536_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_r_1530_);
                            v___x_1538_ = v_reuseFailAlloc_1539_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_1532_);
                        leanh::lean_dec(v_l_1529_);
                        leanh::lean_dec(v_v_1528_);
                        leanh::lean_dec(v_k_1527_);
                        leanh::lean_dec(v_size_1526_);
                        leanh::lean_dec(v_lowerBound_1525_);
                        leanh::lean_dec_ref(v_inst_1523_);
                        return v_r_1530_;
                    }
                    _ => {
                        leanh::lean_del_object(v___x_1532_);
                        leanh::lean_dec(v_l_1529_);
                        leanh::lean_dec(v_v_1528_);
                        leanh::lean_dec(v_k_1527_);
                        leanh::lean_dec(v_size_1526_);
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
    mut v_00_u03b1_1542_: *mut leanh::LeanObject,
    mut v_00_u03b2_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_t_1545_: *mut leanh::LeanObject,
    mut v_lowerBound_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_1544_, v_t_1545_, v_lowerBound_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(
    mut v_t_1548_: *mut leanh::LeanObject,
    mut v_h__1_1549_: *mut leanh::LeanObject,
    mut v_h__2_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1548_) == 0 {
        let mut v_size_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1549_);
        v_size_1551_ = leanh::lean_ctor_get(v_t_1548_, 0);
        leanh::lean_inc(v_size_1551_);
        v_k_1552_ = leanh::lean_ctor_get(v_t_1548_, 1);
        leanh::lean_inc(v_k_1552_);
        v_v_1553_ = leanh::lean_ctor_get(v_t_1548_, 2);
        leanh::lean_inc(v_v_1553_);
        v_l_1554_ = leanh::lean_ctor_get(v_t_1548_, 3);
        leanh::lean_inc(v_l_1554_);
        v_r_1555_ = leanh::lean_ctor_get(v_t_1548_, 4);
        leanh::lean_inc(v_r_1555_);
        leanh::lean_dec_ref_known(v_t_1548_, 5);
        v___x_1556_ = leanh::lean_apply_5(
            v_h__2_1550_,
            v_size_1551_,
            v_k_1552_,
            v_v_1553_,
            v_l_1554_,
            v_r_1555_,
        );
        return v___x_1556_;
    } else {
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1550_);
        v___x_1557_ = leanh::lean_box(0);
        v___x_1558_ = leanh::lean_apply_1(v_h__1_1549_, v___x_1557_);
        return v___x_1558_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(
    mut v_00_u03b1_1559_: *mut leanh::LeanObject,
    mut v_00_u03b2_1560_: *mut leanh::LeanObject,
    mut v_motive_1561_: *mut leanh::LeanObject,
    mut v_t_1562_: *mut leanh::LeanObject,
    mut v_h__1_1563_: *mut leanh::LeanObject,
    mut v_h__2_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1562_) == 0 {
        let mut v_size_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1563_);
        v_size_1565_ = leanh::lean_ctor_get(v_t_1562_, 0);
        leanh::lean_inc(v_size_1565_);
        v_k_1566_ = leanh::lean_ctor_get(v_t_1562_, 1);
        leanh::lean_inc(v_k_1566_);
        v_v_1567_ = leanh::lean_ctor_get(v_t_1562_, 2);
        leanh::lean_inc(v_v_1567_);
        v_l_1568_ = leanh::lean_ctor_get(v_t_1562_, 3);
        leanh::lean_inc(v_l_1568_);
        v_r_1569_ = leanh::lean_ctor_get(v_t_1562_, 4);
        leanh::lean_inc(v_r_1569_);
        leanh::lean_dec_ref_known(v_t_1562_, 5);
        v___x_1570_ = leanh::lean_apply_5(
            v_h__2_1564_,
            v_size_1565_,
            v_k_1566_,
            v_v_1567_,
            v_l_1568_,
            v_r_1569_,
        );
        return v___x_1570_;
    } else {
        let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1564_);
        v___x_1571_ = leanh::lean_box(0);
        v___x_1572_ = leanh::lean_apply_1(v_h__1_1563_, v___x_1571_);
        return v___x_1572_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(
    mut v_x_1573_: u8,
    mut v_h__1_1574_: *mut leanh::LeanObject,
    mut v_h__2_1575_: *mut leanh::LeanObject,
    mut v_h__3_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1573_ {
        0 => {
            let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1576_);
            leanh::lean_dec(v_h__2_1575_);
            v___x_1577_ = leanh::lean_box(0);
            v___x_1578_ = leanh::lean_apply_1(v_h__1_1574_, v___x_1577_);
            return v___x_1578_;
        }
        1 => {
            let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1576_);
            leanh::lean_dec(v_h__1_1574_);
            v___x_1579_ = leanh::lean_box(0);
            v___x_1580_ = leanh::lean_apply_1(v_h__2_1575_, v___x_1579_);
            return v___x_1580_;
        }
        _ => {
            let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1575_);
            leanh::lean_dec(v_h__1_1574_);
            v___x_1581_ = leanh::lean_box(0);
            v___x_1582_ = leanh::lean_apply_1(v_h__3_1576_, v___x_1581_);
            return v___x_1582_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_h__1_1584_: *mut leanh::LeanObject,
    mut v_h__2_1585_: *mut leanh::LeanObject,
    mut v_h__3_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1587_: u8 = 0;
    let mut v_res_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1587_ = (leanh::lean_unbox(v_x_1583_) as u8);
    v_res_1588_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_36__boxed_1587_, v_h__1_1584_, v_h__2_1585_, v_h__3_1586_);
    return v_res_1588_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(
    mut v_motive_1589_: *mut leanh::LeanObject,
    mut v_x_1590_: u8,
    mut v_h__1_1591_: *mut leanh::LeanObject,
    mut v_h__2_1592_: *mut leanh::LeanObject,
    mut v_h__3_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_1590_ {
        0 => {
            let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1593_);
            leanh::lean_dec(v_h__2_1592_);
            v___x_1594_ = leanh::lean_box(0);
            v___x_1595_ = leanh::lean_apply_1(v_h__1_1591_, v___x_1594_);
            return v___x_1595_;
        }
        1 => {
            let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1593_);
            leanh::lean_dec(v_h__1_1591_);
            v___x_1596_ = leanh::lean_box(0);
            v___x_1597_ = leanh::lean_apply_1(v_h__2_1592_, v___x_1596_);
            return v___x_1597_;
        }
        _ => {
            let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1592_);
            leanh::lean_dec(v_h__1_1591_);
            v___x_1598_ = leanh::lean_box(0);
            v___x_1599_ = leanh::lean_apply_1(v_h__3_1593_, v___x_1598_);
            return v___x_1599_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(
    mut v_motive_1600_: *mut leanh::LeanObject,
    mut v_x_1601_: *mut leanh::LeanObject,
    mut v_h__1_1602_: *mut leanh::LeanObject,
    mut v_h__2_1603_: *mut leanh::LeanObject,
    mut v_h__3_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_51__boxed_1605_: u8 = 0;
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_1605_ = (leanh::lean_unbox(v_x_1601_) as u8);
    v_res_1606_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_1600_, v_x_51__boxed_1605_, v_h__1_1602_, v_h__2_1603_, v_h__3_1604_);
    return v_res_1606_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(
    mut v_x_1607_: u8,
    mut v_h__1_1608_: *mut leanh::LeanObject,
    mut v_h__2_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1607_ == 0 {
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1608_);
        v___x_1610_ = leanh::lean_box(0);
        v___x_1611_ = leanh::lean_apply_1(v_h__2_1609_, v___x_1610_);
        return v___x_1611_;
    } else {
        let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1609_);
        v___x_1612_ = leanh::lean_box(0);
        v___x_1613_ = leanh::lean_apply_1(v_h__1_1608_, v___x_1612_);
        return v___x_1613_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1614_: *mut leanh::LeanObject,
    mut v_h__1_1615_: *mut leanh::LeanObject,
    mut v_h__2_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1617_ = (leanh::lean_unbox(v_x_1614_) as u8);
    v_res_1618_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(
            v_x_26__boxed_1617_,
            v_h__1_1615_,
            v_h__2_1616_,
        );
    return v_res_1618_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(
    mut v_motive_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: u8,
    mut v_h__1_1621_: *mut leanh::LeanObject,
    mut v_h__2_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1620_ == 0 {
        let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1621_);
        v___x_1623_ = leanh::lean_box(0);
        v___x_1624_ = leanh::lean_apply_1(v_h__2_1622_, v___x_1623_);
        return v___x_1624_;
    } else {
        let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1622_);
        v___x_1625_ = leanh::lean_box(0);
        v___x_1626_ = leanh::lean_apply_1(v_h__1_1621_, v___x_1625_);
        return v___x_1626_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1627_: *mut leanh::LeanObject,
    mut v_x_1628_: *mut leanh::LeanObject,
    mut v_h__1_1629_: *mut leanh::LeanObject,
    mut v_h__2_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_1631_: u8 = 0;
    let mut v_res_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1631_ = (leanh::lean_unbox(v_x_1628_) as u8);
    v_res_1632_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(
        v_motive_1627_,
        v_x_37__boxed_1631_,
        v_h__1_1629_,
        v_h__2_1630_,
    );
    return v_res_1632_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(
    mut v_x_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1633_) == 0 {
        let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1634_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1634_;
    } else {
        let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1635_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1635_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(
    mut v_x_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1637_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_1636_);
    leanh::lean_dec(v_x_1636_);
    return v_res_1637_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx(
    mut v_00_u03b1_1638_: *mut leanh::LeanObject,
    mut v_00_u03b2_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(
    mut v_00_u03b1_1642_: *mut leanh::LeanObject,
    mut v_00_u03b2_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ =
        l_Std_DTreeMap_Internal_Zipper_ctorIdx(v_00_u03b1_1642_, v_00_u03b2_1643_, v_x_1644_);
    leanh::lean_dec(v_x_1644_);
    return v_res_1645_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(
    mut v_t_1646_: *mut leanh::LeanObject,
    mut v_k_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1646_) == 0 {
        return v_k_1647_;
    } else {
        let mut v_k_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_1648_ = leanh::lean_ctor_get(v_t_1646_, 0);
        leanh::lean_inc(v_k_1648_);
        v_v_1649_ = leanh::lean_ctor_get(v_t_1646_, 1);
        leanh::lean_inc(v_v_1649_);
        v_tree_1650_ = leanh::lean_ctor_get(v_t_1646_, 2);
        leanh::lean_inc(v_tree_1650_);
        v_next_1651_ = leanh::lean_ctor_get(v_t_1646_, 3);
        leanh::lean_inc(v_next_1651_);
        leanh::lean_dec_ref_known(v_t_1646_, 4);
        v___x_1652_ =
            leanh::lean_apply_4(v_k_1647_, v_k_1648_, v_v_1649_, v_tree_1650_, v_next_1651_);
        return v___x_1652_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim(
    mut v_00_u03b1_1653_: *mut leanh::LeanObject,
    mut v_00_u03b2_1654_: *mut leanh::LeanObject,
    mut v_motive_1655_: *mut leanh::LeanObject,
    mut v_ctorIdx_1656_: *mut leanh::LeanObject,
    mut v_t_1657_: *mut leanh::LeanObject,
    mut v_h_1658_: *mut leanh::LeanObject,
    mut v_k_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1657_, v_k_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(
    mut v_00_u03b1_1661_: *mut leanh::LeanObject,
    mut v_00_u03b2_1662_: *mut leanh::LeanObject,
    mut v_motive_1663_: *mut leanh::LeanObject,
    mut v_ctorIdx_1664_: *mut leanh::LeanObject,
    mut v_t_1665_: *mut leanh::LeanObject,
    mut v_h_1666_: *mut leanh::LeanObject,
    mut v_k_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(
        v_00_u03b1_1661_,
        v_00_u03b2_1662_,
        v_motive_1663_,
        v_ctorIdx_1664_,
        v_t_1665_,
        v_h_1666_,
        v_k_1667_,
    );
    leanh::lean_dec(v_ctorIdx_1664_);
    return v_res_1668_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(
    mut v_t_1669_: *mut leanh::LeanObject,
    mut v_done_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1669_, v_done_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_done_elim(
    mut v_00_u03b1_1672_: *mut leanh::LeanObject,
    mut v_00_u03b2_1673_: *mut leanh::LeanObject,
    mut v_motive_1674_: *mut leanh::LeanObject,
    mut v_t_1675_: *mut leanh::LeanObject,
    mut v_h_1676_: *mut leanh::LeanObject,
    mut v_done_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1675_, v_done_1677_);
    return v___x_1678_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(
    mut v_t_1679_: *mut leanh::LeanObject,
    mut v_cons_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1679_, v_cons_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_cons_elim(
    mut v_00_u03b1_1682_: *mut leanh::LeanObject,
    mut v_00_u03b2_1683_: *mut leanh::LeanObject,
    mut v_motive_1684_: *mut leanh::LeanObject,
    mut v_t_1685_: *mut leanh::LeanObject,
    mut v_h_1686_: *mut leanh::LeanObject,
    mut v_cons_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_1685_, v_cons_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(
    mut v_init_1689_: *mut leanh::LeanObject,
    mut v_x_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1690_) == 0 {
                    v_k_1691_ = leanh::lean_ctor_get(v_x_1690_, 1);
                    v_v_1692_ = leanh::lean_ctor_get(v_x_1690_, 2);
                    v_l_1693_ = leanh::lean_ctor_get(v_x_1690_, 3);
                    v_r_1694_ = leanh::lean_ctor_get(v_x_1690_, 4);
                    v___x_1695_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1689_, v_r_1694_);
                    leanh::lean_inc(v_v_1692_);
                    leanh::lean_inc(v_k_1691_);
                    v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1696_, 0, v_k_1691_);
                    leanh::lean_ctor_set(v___x_1696_, 1, v_v_1692_);
                    v___x_1697_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
                    leanh::lean_ctor_set(v___x_1697_, 1, v___x_1695_);
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
    mut v_init_1699_: *mut leanh::LeanObject,
    mut v_x_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1699_, v_x_1700_);
    leanh::lean_dec(v_x_1700_);
    return v_res_1701_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___redArg(
    mut v_x_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1702_) == 0 {
        let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1703_ = leanh::lean_box(0);
        return v___x_1703_;
    } else {
        let mut v_k_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_1704_ = leanh::lean_ctor_get(v_x_1702_, 0);
        v_v_1705_ = leanh::lean_ctor_get(v_x_1702_, 1);
        v_tree_1706_ = leanh::lean_ctor_get(v_x_1702_, 2);
        v_next_1707_ = leanh::lean_ctor_get(v_x_1702_, 3);
        leanh::lean_inc(v_v_1705_);
        leanh::lean_inc(v_k_1704_);
        v___x_1708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1708_, 0, v_k_1704_);
        leanh::lean_ctor_set(v___x_1708_, 1, v_v_1705_);
        v___x_1709_ = leanh::lean_box(0);
        v___x_1710_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_1709_, v_tree_1706_);
        v___x_1711_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1711_, 0, v___x_1708_);
        leanh::lean_ctor_set(v___x_1711_, 1, v___x_1710_);
        v___x_1712_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_1707_);
        v___x_1713_ = l_List_appendTR___redArg(v___x_1711_, v___x_1712_);
        return v___x_1713_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(
    mut v_x_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_1714_);
    leanh::lean_dec(v_x_1714_);
    return v_res_1715_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList(
    mut v_00_u03b1_1716_: *mut leanh::LeanObject,
    mut v_00_u03b2_1717_: *mut leanh::LeanObject,
    mut v_x_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_toList___boxed(
    mut v_00_u03b1_1720_: *mut leanh::LeanObject,
    mut v_00_u03b2_1721_: *mut leanh::LeanObject,
    mut v_x_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1723_ =
        l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_1720_, v_00_u03b2_1721_, v_x_1722_);
    leanh::lean_dec(v_x_1722_);
    return v_res_1723_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(
    mut v_00_u03b1_1724_: *mut leanh::LeanObject,
    mut v_00_u03b2_1725_: *mut leanh::LeanObject,
    mut v_init_1726_: *mut leanh::LeanObject,
    mut v_x_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1728_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_1726_, v_x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(
    mut v_00_u03b1_1729_: *mut leanh::LeanObject,
    mut v_00_u03b2_1730_: *mut leanh::LeanObject,
    mut v_init_1731_: *mut leanh::LeanObject,
    mut v_x_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(
            v_00_u03b1_1729_,
            v_00_u03b2_1730_,
            v_init_1731_,
            v_x_1732_,
        );
    leanh::lean_dec(v_x_1732_);
    return v_res_1733_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
    mut v_x_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1734_) == 0 {
        let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1735_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1735_;
    } else {
        let mut v_tree_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tree_1736_ = leanh::lean_ctor_get(v_x_1734_, 2);
        v_next_1737_ = leanh::lean_ctor_get(v_x_1734_, 3);
        v___x_1738_ = leanh::lean_unsigned_to_nat(1);
        v___x_1739_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_1736_);
        v___x_1740_ = lean_nat_add(v___x_1738_, v___x_1739_);
        leanh::lean_dec(v___x_1739_);
        v___x_1741_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_1737_);
        v___x_1742_ = lean_nat_add(v___x_1740_, v___x_1741_);
        leanh::lean_dec(v___x_1741_);
        leanh::lean_dec(v___x_1740_);
        return v___x_1742_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(
    mut v_x_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
            v_x_1743_,
        );
    leanh::lean_dec(v_x_1743_);
    return v_res_1744_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(
    mut v_00_u03b1_1745_: *mut leanh::LeanObject,
    mut v_00_u03b2_1746_: *mut leanh::LeanObject,
    mut v_x_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(
            v_x_1747_,
        );
    return v___x_1748_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(
    mut v_00_u03b1_1749_: *mut leanh::LeanObject,
    mut v_00_u03b2_1750_: *mut leanh::LeanObject,
    mut v_x_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ =
        l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(
            v_00_u03b1_1749_,
            v_00_u03b2_1750_,
            v_x_1751_,
        );
    leanh::lean_dec(v_x_1751_);
    return v_res_1752_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
    mut v_x_1753_: *mut leanh::LeanObject,
    mut v_x_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1753_) == 0 {
                    v_k_1755_ = leanh::lean_ctor_get(v_x_1753_, 1);
                    v_v_1756_ = leanh::lean_ctor_get(v_x_1753_, 2);
                    v_l_1757_ = leanh::lean_ctor_get(v_x_1753_, 3);
                    v_r_1758_ = leanh::lean_ctor_get(v_x_1753_, 4);
                    leanh::lean_inc(v_r_1758_);
                    leanh::lean_inc(v_v_1756_);
                    leanh::lean_inc(v_k_1755_);
                    v___x_1759_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1759_, 0, v_k_1755_);
                    leanh::lean_ctor_set(v___x_1759_, 1, v_v_1756_);
                    leanh::lean_ctor_set(v___x_1759_, 2, v_r_1758_);
                    leanh::lean_ctor_set(v___x_1759_, 3, v_x_1754_);
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
    mut v_x_1761_: *mut leanh::LeanObject,
    mut v_x_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_1761_, v_x_1762_);
    leanh::lean_dec(v_x_1761_);
    return v_res_1763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap(
    mut v_00_u03b1_1764_: *mut leanh::LeanObject,
    mut v_00_u03b2_1765_: *mut leanh::LeanObject,
    mut v_x_1766_: *mut leanh::LeanObject,
    mut v_x_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_1766_, v_x_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(
    mut v_00_u03b1_1769_: *mut leanh::LeanObject,
    mut v_00_u03b2_1770_: *mut leanh::LeanObject,
    mut v_x_1771_: *mut leanh::LeanObject,
    mut v_x_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Std_DTreeMap_Internal_Zipper_prependMap(
        v_00_u03b1_1769_,
        v_00_u03b2_1770_,
        v_x_1771_,
        v_x_1772_,
    );
    leanh::lean_dec(v_x_1771_);
    return v_res_1773_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
    mut v_inst_1774_: *mut leanh::LeanObject,
    mut v_t_1775_: *mut leanh::LeanObject,
    mut v_lowerBound_1776_: *mut leanh::LeanObject,
    mut v_it_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1775_) == 0 {
                    v_k_1778_ = leanh::lean_ctor_get(v_t_1775_, 1);
                    leanh::lean_inc_n(v_k_1778_, 2);
                    v_v_1779_ = leanh::lean_ctor_get(v_t_1775_, 2);
                    leanh::lean_inc(v_v_1779_);
                    v_l_1780_ = leanh::lean_ctor_get(v_t_1775_, 3);
                    leanh::lean_inc(v_l_1780_);
                    v_r_1781_ = leanh::lean_ctor_get(v_t_1775_, 4);
                    leanh::lean_inc(v_r_1781_);
                    leanh::lean_dec_ref_known(v_t_1775_, 5);
                    leanh::lean_inc_ref(v_inst_1774_);
                    leanh::lean_inc(v_lowerBound_1776_);
                    v___x_1782_ =
                        leanh::lean_apply_2(v_inst_1774_, v_lowerBound_1776_, v_k_1778_);
                    v___x_1783_ = (leanh::lean_unbox(v___x_1782_) as u8);
                    match v___x_1783_ {
                        0 => {
                            v___x_1784_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1784_, 0, v_k_1778_);
                            leanh::lean_ctor_set(v___x_1784_, 1, v_v_1779_);
                            leanh::lean_ctor_set(v___x_1784_, 2, v_r_1781_);
                            leanh::lean_ctor_set(v___x_1784_, 3, v_it_1777_);
                            v_t_1775_ = v_l_1780_;
                            v_it_1777_ = v___x_1784_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_dec(v_l_1780_);
                            leanh::lean_dec(v_lowerBound_1776_);
                            leanh::lean_dec_ref(v_inst_1774_);
                            v___x_1786_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1786_, 0, v_k_1778_);
                            leanh::lean_ctor_set(v___x_1786_, 1, v_v_1779_);
                            leanh::lean_ctor_set(v___x_1786_, 2, v_r_1781_);
                            leanh::lean_ctor_set(v___x_1786_, 3, v_it_1777_);
                            return v___x_1786_;
                        }
                        _ => {
                            leanh::lean_dec(v_l_1780_);
                            leanh::lean_dec(v_v_1779_);
                            leanh::lean_dec(v_k_1778_);
                            v_t_1775_ = v_r_1781_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_lowerBound_1776_);
                    leanh::lean_dec_ref(v_inst_1774_);
                    return v_it_1777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGE(
    mut v_00_u03b1_1788_: *mut leanh::LeanObject,
    mut v_00_u03b2_1789_: *mut leanh::LeanObject,
    mut v_inst_1790_: *mut leanh::LeanObject,
    mut v_t_1791_: *mut leanh::LeanObject,
    mut v_lowerBound_1792_: *mut leanh::LeanObject,
    mut v_it_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_1790_,
        v_t_1791_,
        v_lowerBound_1792_,
        v_it_1793_,
    );
    return v___x_1794_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
    mut v_inst_1795_: *mut leanh::LeanObject,
    mut v_t_1796_: *mut leanh::LeanObject,
    mut v_lowerBound_1797_: *mut leanh::LeanObject,
    mut v_it_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1796_) == 0 {
                    v_k_1799_ = leanh::lean_ctor_get(v_t_1796_, 1);
                    leanh::lean_inc_n(v_k_1799_, 2);
                    v_v_1800_ = leanh::lean_ctor_get(v_t_1796_, 2);
                    leanh::lean_inc(v_v_1800_);
                    v_l_1801_ = leanh::lean_ctor_get(v_t_1796_, 3);
                    leanh::lean_inc(v_l_1801_);
                    v_r_1802_ = leanh::lean_ctor_get(v_t_1796_, 4);
                    leanh::lean_inc(v_r_1802_);
                    leanh::lean_dec_ref_known(v_t_1796_, 5);
                    leanh::lean_inc_ref(v_inst_1795_);
                    leanh::lean_inc(v_lowerBound_1797_);
                    v___x_1803_ =
                        leanh::lean_apply_2(v_inst_1795_, v_lowerBound_1797_, v_k_1799_);
                    v___x_1804_ = (leanh::lean_unbox(v___x_1803_) as u8);
                    if v___x_1804_ == 0 {
                        v___x_1805_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_1805_, 0, v_k_1799_);
                        leanh::lean_ctor_set(v___x_1805_, 1, v_v_1800_);
                        leanh::lean_ctor_set(v___x_1805_, 2, v_r_1802_);
                        leanh::lean_ctor_set(v___x_1805_, 3, v_it_1798_);
                        v_t_1796_ = v_l_1801_;
                        v_it_1798_ = v___x_1805_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1801_);
                        leanh::lean_dec(v_v_1800_);
                        leanh::lean_dec(v_k_1799_);
                        v_t_1796_ = v_r_1802_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_lowerBound_1797_);
                    leanh::lean_dec_ref(v_inst_1795_);
                    return v_it_1798_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_prependMapGT(
    mut v_00_u03b1_1808_: *mut leanh::LeanObject,
    mut v_00_u03b2_1809_: *mut leanh::LeanObject,
    mut v_inst_1810_: *mut leanh::LeanObject,
    mut v_t_1811_: *mut leanh::LeanObject,
    mut v_lowerBound_1812_: *mut leanh::LeanObject,
    mut v_it_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_1810_,
        v_t_1811_,
        v_lowerBound_1812_,
        v_it_1813_,
    );
    return v___x_1814_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(
    mut v_x_1815_: *mut leanh::LeanObject,
    mut v_x_1816_: *mut leanh::LeanObject,
    mut v_h__1_1817_: *mut leanh::LeanObject,
    mut v_h__2_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1815_) == 0 {
        let mut v_size_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1817_);
        v_size_1819_ = leanh::lean_ctor_get(v_x_1815_, 0);
        leanh::lean_inc(v_size_1819_);
        v_k_1820_ = leanh::lean_ctor_get(v_x_1815_, 1);
        leanh::lean_inc(v_k_1820_);
        v_v_1821_ = leanh::lean_ctor_get(v_x_1815_, 2);
        leanh::lean_inc(v_v_1821_);
        v_l_1822_ = leanh::lean_ctor_get(v_x_1815_, 3);
        leanh::lean_inc(v_l_1822_);
        v_r_1823_ = leanh::lean_ctor_get(v_x_1815_, 4);
        leanh::lean_inc(v_r_1823_);
        leanh::lean_dec_ref_known(v_x_1815_, 5);
        v___x_1824_ = leanh::lean_apply_6(
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
        let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1818_);
        v___x_1825_ = leanh::lean_apply_1(v_h__1_1817_, v_x_1816_);
        return v___x_1825_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(
    mut v_00_u03b1_1826_: *mut leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut leanh::LeanObject,
    mut v_motive_1828_: *mut leanh::LeanObject,
    mut v_x_1829_: *mut leanh::LeanObject,
    mut v_x_1830_: *mut leanh::LeanObject,
    mut v_h__1_1831_: *mut leanh::LeanObject,
    mut v_h__2_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1829_) == 0 {
        let mut v_size_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1831_);
        v_size_1833_ = leanh::lean_ctor_get(v_x_1829_, 0);
        leanh::lean_inc(v_size_1833_);
        v_k_1834_ = leanh::lean_ctor_get(v_x_1829_, 1);
        leanh::lean_inc(v_k_1834_);
        v_v_1835_ = leanh::lean_ctor_get(v_x_1829_, 2);
        leanh::lean_inc(v_v_1835_);
        v_l_1836_ = leanh::lean_ctor_get(v_x_1829_, 3);
        leanh::lean_inc(v_l_1836_);
        v_r_1837_ = leanh::lean_ctor_get(v_x_1829_, 4);
        leanh::lean_inc(v_r_1837_);
        leanh::lean_dec_ref_known(v_x_1829_, 5);
        v___x_1838_ = leanh::lean_apply_6(
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
        let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1832_);
        v___x_1839_ = leanh::lean_apply_1(v_h__1_1831_, v_x_1830_);
        return v___x_1839_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(
    mut v_x_1840_: *mut leanh::LeanObject,
    mut v_h__1_1841_: *mut leanh::LeanObject,
    mut v_h__2_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1840_) == 0 {
        let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1842_);
        v___x_1843_ = leanh::lean_box(0);
        v___x_1844_ = leanh::lean_apply_1(v_h__1_1841_, v___x_1843_);
        return v___x_1844_;
    } else {
        let mut v_k_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1841_);
        v_k_1845_ = leanh::lean_ctor_get(v_x_1840_, 0);
        leanh::lean_inc(v_k_1845_);
        v_v_1846_ = leanh::lean_ctor_get(v_x_1840_, 1);
        leanh::lean_inc(v_v_1846_);
        v_tree_1847_ = leanh::lean_ctor_get(v_x_1840_, 2);
        leanh::lean_inc(v_tree_1847_);
        v_next_1848_ = leanh::lean_ctor_get(v_x_1840_, 3);
        leanh::lean_inc(v_next_1848_);
        leanh::lean_dec_ref_known(v_x_1840_, 4);
        v___x_1849_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_1850_: *mut leanh::LeanObject,
    mut v_00_u03b2_1851_: *mut leanh::LeanObject,
    mut v_motive_1852_: *mut leanh::LeanObject,
    mut v_x_1853_: *mut leanh::LeanObject,
    mut v_h__1_1854_: *mut leanh::LeanObject,
    mut v_h__2_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1853_) == 0 {
        let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1855_);
        v___x_1856_ = leanh::lean_box(0);
        v___x_1857_ = leanh::lean_apply_1(v_h__1_1854_, v___x_1856_);
        return v___x_1857_;
    } else {
        let mut v_k_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1854_);
        v_k_1858_ = leanh::lean_ctor_get(v_x_1853_, 0);
        leanh::lean_inc(v_k_1858_);
        v_v_1859_ = leanh::lean_ctor_get(v_x_1853_, 1);
        leanh::lean_inc(v_v_1859_);
        v_tree_1860_ = leanh::lean_ctor_get(v_x_1853_, 2);
        leanh::lean_inc(v_tree_1860_);
        v_next_1861_ = leanh::lean_ctor_get(v_x_1853_, 3);
        leanh::lean_inc(v_next_1861_);
        leanh::lean_dec_ref_known(v_x_1853_, 4);
        v___x_1862_ = leanh::lean_apply_4(
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
    mut v_x_1863_: *mut leanh::LeanObject,
    mut v_h__1_1864_: *mut leanh::LeanObject,
    mut v_h__2_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1863_) == 0 {
        let mut v_size_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1864_);
        v_size_1866_ = leanh::lean_ctor_get(v_x_1863_, 0);
        leanh::lean_inc(v_size_1866_);
        v_k_1867_ = leanh::lean_ctor_get(v_x_1863_, 1);
        leanh::lean_inc(v_k_1867_);
        v_v_1868_ = leanh::lean_ctor_get(v_x_1863_, 2);
        leanh::lean_inc(v_v_1868_);
        v_l_1869_ = leanh::lean_ctor_get(v_x_1863_, 3);
        leanh::lean_inc(v_l_1869_);
        v_r_1870_ = leanh::lean_ctor_get(v_x_1863_, 4);
        leanh::lean_inc(v_r_1870_);
        leanh::lean_dec_ref_known(v_x_1863_, 5);
        v___x_1871_ = leanh::lean_apply_5(
            v_h__2_1865_,
            v_size_1866_,
            v_k_1867_,
            v_v_1868_,
            v_l_1869_,
            v_r_1870_,
        );
        return v___x_1871_;
    } else {
        let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1865_);
        v___x_1872_ = leanh::lean_box(0);
        v___x_1873_ = leanh::lean_apply_1(v_h__1_1864_, v___x_1872_);
        return v___x_1873_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(
    mut v_00_u03b1_1874_: *mut leanh::LeanObject,
    mut v_00_u03b2_1875_: *mut leanh::LeanObject,
    mut v_motive_1876_: *mut leanh::LeanObject,
    mut v_x_1877_: *mut leanh::LeanObject,
    mut v_h__1_1878_: *mut leanh::LeanObject,
    mut v_h__2_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1877_) == 0 {
        let mut v_size_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_l_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_r_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1878_);
        v_size_1880_ = leanh::lean_ctor_get(v_x_1877_, 0);
        leanh::lean_inc(v_size_1880_);
        v_k_1881_ = leanh::lean_ctor_get(v_x_1877_, 1);
        leanh::lean_inc(v_k_1881_);
        v_v_1882_ = leanh::lean_ctor_get(v_x_1877_, 2);
        leanh::lean_inc(v_v_1882_);
        v_l_1883_ = leanh::lean_ctor_get(v_x_1877_, 3);
        leanh::lean_inc(v_l_1883_);
        v_r_1884_ = leanh::lean_ctor_get(v_x_1877_, 4);
        leanh::lean_inc(v_r_1884_);
        leanh::lean_dec_ref_known(v_x_1877_, 5);
        v___x_1885_ = leanh::lean_apply_5(
            v_h__2_1879_,
            v_size_1880_,
            v_k_1881_,
            v_v_1882_,
            v_l_1883_,
            v_r_1884_,
        );
        return v___x_1885_;
    } else {
        let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1879_);
        v___x_1886_ = leanh::lean_box(0);
        v___x_1887_ = leanh::lean_apply_1(v_h__1_1878_, v___x_1886_);
        return v___x_1887_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_step___redArg(
    mut v_x_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1888_) == 0 {
        let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1889_ = leanh::lean_box(2);
        return v___x_1889_;
    } else {
        let mut v_k_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_1890_ = leanh::lean_ctor_get(v_x_1888_, 0);
        leanh::lean_inc(v_k_1890_);
        v_v_1891_ = leanh::lean_ctor_get(v_x_1888_, 1);
        leanh::lean_inc(v_v_1891_);
        v_tree_1892_ = leanh::lean_ctor_get(v_x_1888_, 2);
        leanh::lean_inc(v_tree_1892_);
        v_next_1893_ = leanh::lean_ctor_get(v_x_1888_, 3);
        leanh::lean_inc(v_next_1893_);
        leanh::lean_dec_ref_known(v_x_1888_, 4);
        v___x_1894_ =
            l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_1892_, v_next_1893_);
        leanh::lean_dec(v_tree_1892_);
        v___x_1895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1895_, 0, v_k_1890_);
        leanh::lean_ctor_set(v___x_1895_, 1, v_v_1891_);
        v___x_1896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1896_, 0, v___x_1894_);
        leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
        return v___x_1896_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_step(
    mut v_00_u03b1_1897_: *mut leanh::LeanObject,
    mut v_00_u03b2_1898_: *mut leanh::LeanObject,
    mut v_x_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_1899_);
    return v___x_1900_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(
    mut v_00_u03b1_1902_: *mut leanh::LeanObject,
    mut v_00_u03b2_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1904_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0;
    return v___f_1904_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(
    mut v_00_u03b1_1905_: *mut leanh::LeanObject,
    mut v_00_u03b2_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = leanh::lean_box(0);
    return v___x_1907_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___redArg(
    mut v_t_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_1908_);
    return v_t_1908_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(
    mut v_t_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_1909_);
    leanh::lean_dec(v_t_1909_);
    return v_res_1910_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter(
    mut v_00_u03b1_1911_: *mut leanh::LeanObject,
    mut v_00_u03b2_1912_: *mut leanh::LeanObject,
    mut v_t_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_1913_);
    return v_t_1913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iter___boxed(
    mut v_00_u03b1_1914_: *mut leanh::LeanObject,
    mut v_00_u03b2_1915_: *mut leanh::LeanObject,
    mut v_t_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ =
        l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_1914_, v_00_u03b2_1915_, v_t_1916_);
    leanh::lean_dec(v_t_1916_);
    return v_res_1917_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(
    mut v_t_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = leanh::lean_box(0);
    v___x_1920_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1918_, v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(
    mut v_t_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_1921_);
    leanh::lean_dec(v_t_1921_);
    return v_res_1922_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree(
    mut v_00_u03b1_1923_: *mut leanh::LeanObject,
    mut v_00_u03b2_1924_: *mut leanh::LeanObject,
    mut v_t_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(
    mut v_00_u03b1_1927_: *mut leanh::LeanObject,
    mut v_00_u03b2_1928_: *mut leanh::LeanObject,
    mut v_t_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ =
        l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_1927_, v_00_u03b2_1928_, v_t_1929_);
    leanh::lean_dec(v_t_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(
    mut v_x_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1931_);
    return v_x_1931_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(
    mut v_x_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(v_x_1932_);
    leanh::lean_dec(v_x_1932_);
    return v_res_1933_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Zipper_instToIterator(
    mut v_00_u03b1_1935_: *mut leanh::LeanObject,
    mut v_00_u03b2_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1937_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0;
    return v___f_1937_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_1938_: *mut leanh::LeanObject,
    mut v_h__1_1939_: *mut leanh::LeanObject,
    mut v_h__2_1940_: *mut leanh::LeanObject,
    mut v_h__3_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1938_) {
        0 => {
            let mut v_it_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1941_);
            leanh::lean_dec(v_h__2_1940_);
            v_it_1942_ = leanh::lean_ctor_get(v_x_1938_, 0);
            leanh::lean_inc(v_it_1942_);
            v_out_1943_ = leanh::lean_ctor_get(v_x_1938_, 1);
            leanh::lean_inc(v_out_1943_);
            leanh::lean_dec_ref_known(v_x_1938_, 2);
            v___x_1944_ = leanh::lean_apply_2(v_h__1_1939_, v_it_1942_, v_out_1943_);
            return v___x_1944_;
        }
        1 => {
            let mut v_it_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1941_);
            leanh::lean_dec(v_h__1_1939_);
            v_it_1945_ = leanh::lean_ctor_get(v_x_1938_, 0);
            leanh::lean_inc(v_it_1945_);
            leanh::lean_dec_ref_known(v_x_1938_, 1);
            v___x_1946_ = leanh::lean_apply_1(v_h__2_1940_, v_it_1945_);
            return v___x_1946_;
        }
        _ => {
            let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1940_);
            leanh::lean_dec(v_h__1_1939_);
            v___x_1947_ = leanh::lean_box(0);
            v___x_1948_ = leanh::lean_apply_1(v_h__3_1941_, v___x_1947_);
            return v___x_1948_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_1949_: *mut leanh::LeanObject,
    mut v_00_u03b2_1950_: *mut leanh::LeanObject,
    mut v_m_1951_: *mut leanh::LeanObject,
    mut v_motive_1952_: *mut leanh::LeanObject,
    mut v_x_1953_: *mut leanh::LeanObject,
    mut v_h__1_1954_: *mut leanh::LeanObject,
    mut v_h__2_1955_: *mut leanh::LeanObject,
    mut v_h__3_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1953_) {
        0 => {
            let mut v_it_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1956_);
            leanh::lean_dec(v_h__2_1955_);
            v_it_1957_ = leanh::lean_ctor_get(v_x_1953_, 0);
            leanh::lean_inc(v_it_1957_);
            v_out_1958_ = leanh::lean_ctor_get(v_x_1953_, 1);
            leanh::lean_inc(v_out_1958_);
            leanh::lean_dec_ref_known(v_x_1953_, 2);
            v___x_1959_ = leanh::lean_apply_2(v_h__1_1954_, v_it_1957_, v_out_1958_);
            return v___x_1959_;
        }
        1 => {
            let mut v_it_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1956_);
            leanh::lean_dec(v_h__1_1954_);
            v_it_1960_ = leanh::lean_ctor_get(v_x_1953_, 0);
            leanh::lean_inc(v_it_1960_);
            leanh::lean_dec_ref_known(v_x_1953_, 1);
            v___x_1961_ = leanh::lean_apply_1(v_h__2_1955_, v_it_1960_);
            return v___x_1961_;
        }
        _ => {
            let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1955_);
            leanh::lean_dec(v_h__1_1954_);
            v___x_1962_ = leanh::lean_box(0);
            v___x_1963_ = leanh::lean_apply_1(v_h__3_1956_, v___x_1962_);
            return v___x_1963_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxcIterator_step___redArg(
    mut v_inst_1964_: *mut leanh::LeanObject,
    mut v_x_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_k_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_unused_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_iter_1966_ = leanh::lean_ctor_get(v_x_1965_, 0);
                leanh::lean_inc(v_iter_1966_);
                if leanh::lean_obj_tag(v_iter_1966_) == 0 {
                    leanh::lean_dec_ref(v_x_1965_);
                    leanh::lean_dec_ref(v_inst_1964_);
                    v___x_1967_ = leanh::lean_box(2);
                    return v___x_1967_;
                } else {
                    v_upper_1968_ = leanh::lean_ctor_get(v_x_1965_, 1);
                    v_isSharedCheck_1985_ = (!leanh::lean_is_exclusive(v_x_1965_)) as u8;
                    if v_isSharedCheck_1985_ == 0 {
                        v_unused_1986_ = leanh::lean_ctor_get(v_x_1965_, 0);
                        leanh::lean_dec(v_unused_1986_);
                        v___x_1970_ = v_x_1965_;
                        v_isShared_1971_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upper_1968_);
                        leanh::lean_dec(v_x_1965_);
                        v___x_1970_ = leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_k_1972_ = leanh::lean_ctor_get(v_iter_1966_, 0);
                leanh::lean_inc_n(v_k_1972_, 2);
                v_v_1973_ = leanh::lean_ctor_get(v_iter_1966_, 1);
                leanh::lean_inc(v_v_1973_);
                v_tree_1974_ = leanh::lean_ctor_get(v_iter_1966_, 2);
                leanh::lean_inc(v_tree_1974_);
                v_next_1975_ = leanh::lean_ctor_get(v_iter_1966_, 3);
                leanh::lean_inc(v_next_1975_);
                leanh::lean_dec_ref_known(v_iter_1966_, 4);
                leanh::lean_inc(v_upper_1968_);
                v___x_1976_ = leanh::lean_apply_2(v_inst_1964_, v_k_1972_, v_upper_1968_);
                v___x_1977_ = (leanh::lean_unbox(v___x_1976_) as u8);
                if v___x_1977_ == 2 {
                    leanh::lean_dec(v_next_1975_);
                    leanh::lean_dec(v_tree_1974_);
                    leanh::lean_dec(v_v_1973_);
                    leanh::lean_dec(v_k_1972_);
                    leanh::lean_del_object(v___x_1970_);
                    leanh::lean_dec(v_upper_1968_);
                    v___x_1978_ = leanh::lean_box(2);
                    return v___x_1978_;
                } else {
                    v___x_1979_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                        v_tree_1974_,
                        v_next_1975_,
                    );
                    leanh::lean_dec(v_tree_1974_);
                    if v_isShared_1971_ == 0 {
                        leanh::lean_ctor_set(v___x_1970_, 0, v___x_1979_);
                        v___x_1981_ = v___x_1970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1979_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_upper_1968_);
                        v___x_1981_ = v_reuseFailAlloc_1984_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1982_, 0, v_k_1972_);
                leanh::lean_ctor_set(v___x_1982_, 1, v_v_1973_);
                v___x_1983_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1983_, 0, v___x_1981_);
                leanh::lean_ctor_set(v___x_1983_, 1, v___x_1982_);
                return v___x_1983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxcIterator_step(
    mut v_00_u03b1_1987_: *mut leanh::LeanObject,
    mut v_00_u03b2_1988_: *mut leanh::LeanObject,
    mut v_inst_1989_: *mut leanh::LeanObject,
    mut v_x_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_1989_, v_x_1990_);
    return v___x_1991_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(
    mut v_inst_1992_: *mut leanh::LeanObject,
    mut v_it_1993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_1992_, v_it_1993_);
    return v___x_1994_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(
    mut v_inst_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1996_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1996_, 0, v_inst_1995_);
    return v___f_1996_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(
    mut v_00_u03b1_1997_: *mut leanh::LeanObject,
    mut v_00_u03b2_1998_: *mut leanh::LeanObject,
    mut v_inst_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2000_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2000_, 0, v_inst_1999_);
    return v___f_2000_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(
    mut v_x_2001_: *mut leanh::LeanObject,
    mut v_h__1_2002_: *mut leanh::LeanObject,
    mut v_h__2_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_iter_2004_ = leanh::lean_ctor_get(v_x_2001_, 0);
    if leanh::lean_obj_tag(v_iter_2004_) == 0 {
        let mut v_upper_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2003_);
        v_upper_2005_ = leanh::lean_ctor_get(v_x_2001_, 1);
        leanh::lean_inc(v_upper_2005_);
        leanh::lean_dec_ref(v_x_2001_);
        v___x_2006_ = leanh::lean_apply_1(v_h__1_2002_, v_upper_2005_);
        return v___x_2006_;
    } else {
        let mut v_upper_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_iter_2004_);
        leanh::lean_dec(v_h__1_2002_);
        v_upper_2007_ = leanh::lean_ctor_get(v_x_2001_, 1);
        leanh::lean_inc(v_upper_2007_);
        leanh::lean_dec_ref(v_x_2001_);
        v_k_2008_ = leanh::lean_ctor_get(v_iter_2004_, 0);
        leanh::lean_inc(v_k_2008_);
        v_v_2009_ = leanh::lean_ctor_get(v_iter_2004_, 1);
        leanh::lean_inc(v_v_2009_);
        v_tree_2010_ = leanh::lean_ctor_get(v_iter_2004_, 2);
        leanh::lean_inc(v_tree_2010_);
        v_next_2011_ = leanh::lean_ctor_get(v_iter_2004_, 3);
        leanh::lean_inc(v_next_2011_);
        leanh::lean_dec_ref_known(v_iter_2004_, 4);
        v___x_2012_ = leanh::lean_apply_5(
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
    mut v_00_u03b1_2013_: *mut leanh::LeanObject,
    mut v_00_u03b2_2014_: *mut leanh::LeanObject,
    mut v_inst_2015_: *mut leanh::LeanObject,
    mut v_motive_2016_: *mut leanh::LeanObject,
    mut v_x_2017_: *mut leanh::LeanObject,
    mut v_h__1_2018_: *mut leanh::LeanObject,
    mut v_h__2_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_iter_2020_ = leanh::lean_ctor_get(v_x_2017_, 0);
    if leanh::lean_obj_tag(v_iter_2020_) == 0 {
        let mut v_upper_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2019_);
        v_upper_2021_ = leanh::lean_ctor_get(v_x_2017_, 1);
        leanh::lean_inc(v_upper_2021_);
        leanh::lean_dec_ref(v_x_2017_);
        v___x_2022_ = leanh::lean_apply_1(v_h__1_2018_, v_upper_2021_);
        return v___x_2022_;
    } else {
        let mut v_upper_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_iter_2020_);
        leanh::lean_dec(v_h__1_2018_);
        v_upper_2023_ = leanh::lean_ctor_get(v_x_2017_, 1);
        leanh::lean_inc(v_upper_2023_);
        leanh::lean_dec_ref(v_x_2017_);
        v_k_2024_ = leanh::lean_ctor_get(v_iter_2020_, 0);
        leanh::lean_inc(v_k_2024_);
        v_v_2025_ = leanh::lean_ctor_get(v_iter_2020_, 1);
        leanh::lean_inc(v_v_2025_);
        v_tree_2026_ = leanh::lean_ctor_get(v_iter_2020_, 2);
        leanh::lean_inc(v_tree_2026_);
        v_next_2027_ = leanh::lean_ctor_get(v_iter_2020_, 3);
        leanh::lean_inc(v_next_2027_);
        leanh::lean_dec_ref_known(v_iter_2020_, 4);
        v___x_2028_ = leanh::lean_apply_5(
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
    mut v_00_u03b1_2029_: *mut leanh::LeanObject,
    mut v_00_u03b2_2030_: *mut leanh::LeanObject,
    mut v_inst_2031_: *mut leanh::LeanObject,
    mut v_motive_2032_: *mut leanh::LeanObject,
    mut v_x_2033_: *mut leanh::LeanObject,
    mut v_h__1_2034_: *mut leanh::LeanObject,
    mut v_h__2_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_2029_, v_00_u03b2_2030_, v_inst_2031_, v_motive_2032_, v_x_2033_, v_h__1_2034_, v_h__2_2035_);
    leanh::lean_dec_ref(v_inst_2031_);
    return v_res_2036_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(
    mut v_00_u03b1_2037_: *mut leanh::LeanObject,
    mut v_00_u03b2_2038_: *mut leanh::LeanObject,
    mut v_inst_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2040_ = leanh::lean_box(0);
    return v___x_2040_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(
    mut v_00_u03b1_2041_: *mut leanh::LeanObject,
    mut v_00_u03b2_2042_: *mut leanh::LeanObject,
    mut v_inst_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_2041_, v_00_u03b2_2042_, v_inst_2043_);
    leanh::lean_dec_ref(v_inst_2043_);
    return v_res_2044_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RxoIterator_step___redArg(
    mut v_inst_2045_: *mut leanh::LeanObject,
    mut v_x_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v_k_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_unused_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_iter_2047_ = leanh::lean_ctor_get(v_x_2046_, 0);
                leanh::lean_inc(v_iter_2047_);
                if leanh::lean_obj_tag(v_iter_2047_) == 0 {
                    leanh::lean_dec_ref(v_x_2046_);
                    leanh::lean_dec_ref(v_inst_2045_);
                    v___x_2048_ = leanh::lean_box(2);
                    return v___x_2048_;
                } else {
                    v_upper_2049_ = leanh::lean_ctor_get(v_x_2046_, 1);
                    v_isSharedCheck_2066_ = (!leanh::lean_is_exclusive(v_x_2046_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v_unused_2067_ = leanh::lean_ctor_get(v_x_2046_, 0);
                        leanh::lean_dec(v_unused_2067_);
                        v___x_2051_ = v_x_2046_;
                        v_isShared_2052_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upper_2049_);
                        leanh::lean_dec(v_x_2046_);
                        v___x_2051_ = leanh::lean_box(0);
                        v_isShared_2052_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_k_2053_ = leanh::lean_ctor_get(v_iter_2047_, 0);
                leanh::lean_inc_n(v_k_2053_, 2);
                v_v_2054_ = leanh::lean_ctor_get(v_iter_2047_, 1);
                leanh::lean_inc(v_v_2054_);
                v_tree_2055_ = leanh::lean_ctor_get(v_iter_2047_, 2);
                leanh::lean_inc(v_tree_2055_);
                v_next_2056_ = leanh::lean_ctor_get(v_iter_2047_, 3);
                leanh::lean_inc(v_next_2056_);
                leanh::lean_dec_ref_known(v_iter_2047_, 4);
                leanh::lean_inc(v_upper_2049_);
                v___x_2057_ = leanh::lean_apply_2(v_inst_2045_, v_k_2053_, v_upper_2049_);
                v___x_2058_ = (leanh::lean_unbox(v___x_2057_) as u8);
                if v___x_2058_ == 0 {
                    v___x_2059_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                        v_tree_2055_,
                        v_next_2056_,
                    );
                    leanh::lean_dec(v_tree_2055_);
                    if v_isShared_2052_ == 0 {
                        leanh::lean_ctor_set(v___x_2051_, 0, v___x_2059_);
                        v___x_2061_ = v___x_2051_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2064_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2059_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_upper_2049_);
                        v___x_2061_ = v_reuseFailAlloc_2064_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_next_2056_);
                    leanh::lean_dec(v_tree_2055_);
                    leanh::lean_dec(v_v_2054_);
                    leanh::lean_dec(v_k_2053_);
                    leanh::lean_del_object(v___x_2051_);
                    leanh::lean_dec(v_upper_2049_);
                    v___x_2065_ = leanh::lean_box(2);
                    return v___x_2065_;
                }
            }
            2 => {
                v___x_2062_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2062_, 0, v_k_2053_);
                leanh::lean_ctor_set(v___x_2062_, 1, v_v_2054_);
                v___x_2063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                return v___x_2063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_RxoIterator_step(
    mut v_00_u03b1_2068_: *mut leanh::LeanObject,
    mut v_00_u03b2_2069_: *mut leanh::LeanObject,
    mut v_inst_2070_: *mut leanh::LeanObject,
    mut v_x_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_2070_, v_x_2071_);
    return v___x_2072_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(
    mut v_inst_2073_: *mut leanh::LeanObject,
    mut v_it_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_2073_, v_it_2074_);
    return v___x_2075_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(
    mut v_inst_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2077_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2077_, 0, v_inst_2076_);
    return v___f_2077_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(
    mut v_00_u03b1_2078_: *mut leanh::LeanObject,
    mut v_00_u03b2_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2081_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2081_, 0, v_inst_2080_);
    return v___f_2081_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(
    mut v_x_2082_: *mut leanh::LeanObject,
    mut v_h__1_2083_: *mut leanh::LeanObject,
    mut v_h__2_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_iter_2085_ = leanh::lean_ctor_get(v_x_2082_, 0);
    if leanh::lean_obj_tag(v_iter_2085_) == 0 {
        let mut v_upper_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2084_);
        v_upper_2086_ = leanh::lean_ctor_get(v_x_2082_, 1);
        leanh::lean_inc(v_upper_2086_);
        leanh::lean_dec_ref(v_x_2082_);
        v___x_2087_ = leanh::lean_apply_1(v_h__1_2083_, v_upper_2086_);
        return v___x_2087_;
    } else {
        let mut v_upper_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_iter_2085_);
        leanh::lean_dec(v_h__1_2083_);
        v_upper_2088_ = leanh::lean_ctor_get(v_x_2082_, 1);
        leanh::lean_inc(v_upper_2088_);
        leanh::lean_dec_ref(v_x_2082_);
        v_k_2089_ = leanh::lean_ctor_get(v_iter_2085_, 0);
        leanh::lean_inc(v_k_2089_);
        v_v_2090_ = leanh::lean_ctor_get(v_iter_2085_, 1);
        leanh::lean_inc(v_v_2090_);
        v_tree_2091_ = leanh::lean_ctor_get(v_iter_2085_, 2);
        leanh::lean_inc(v_tree_2091_);
        v_next_2092_ = leanh::lean_ctor_get(v_iter_2085_, 3);
        leanh::lean_inc(v_next_2092_);
        leanh::lean_dec_ref_known(v_iter_2085_, 4);
        v___x_2093_ = leanh::lean_apply_5(
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
    mut v_00_u03b1_2094_: *mut leanh::LeanObject,
    mut v_00_u03b2_2095_: *mut leanh::LeanObject,
    mut v_inst_2096_: *mut leanh::LeanObject,
    mut v_motive_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
    mut v_h__1_2099_: *mut leanh::LeanObject,
    mut v_h__2_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_iter_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_iter_2101_ = leanh::lean_ctor_get(v_x_2098_, 0);
    if leanh::lean_obj_tag(v_iter_2101_) == 0 {
        let mut v_upper_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2100_);
        v_upper_2102_ = leanh::lean_ctor_get(v_x_2098_, 1);
        leanh::lean_inc(v_upper_2102_);
        leanh::lean_dec_ref(v_x_2098_);
        v___x_2103_ = leanh::lean_apply_1(v_h__1_2099_, v_upper_2102_);
        return v___x_2103_;
    } else {
        let mut v_upper_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tree_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_next_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_iter_2101_);
        leanh::lean_dec(v_h__1_2099_);
        v_upper_2104_ = leanh::lean_ctor_get(v_x_2098_, 1);
        leanh::lean_inc(v_upper_2104_);
        leanh::lean_dec_ref(v_x_2098_);
        v_k_2105_ = leanh::lean_ctor_get(v_iter_2101_, 0);
        leanh::lean_inc(v_k_2105_);
        v_v_2106_ = leanh::lean_ctor_get(v_iter_2101_, 1);
        leanh::lean_inc(v_v_2106_);
        v_tree_2107_ = leanh::lean_ctor_get(v_iter_2101_, 2);
        leanh::lean_inc(v_tree_2107_);
        v_next_2108_ = leanh::lean_ctor_get(v_iter_2101_, 3);
        leanh::lean_inc(v_next_2108_);
        leanh::lean_dec_ref_known(v_iter_2101_, 4);
        v___x_2109_ = leanh::lean_apply_5(
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
    mut v_00_u03b1_2110_: *mut leanh::LeanObject,
    mut v_00_u03b2_2111_: *mut leanh::LeanObject,
    mut v_inst_2112_: *mut leanh::LeanObject,
    mut v_motive_2113_: *mut leanh::LeanObject,
    mut v_x_2114_: *mut leanh::LeanObject,
    mut v_h__1_2115_: *mut leanh::LeanObject,
    mut v_h__2_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2117_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_2110_, v_00_u03b2_2111_, v_inst_2112_, v_motive_2113_, v_x_2114_, v_h__1_2115_, v_h__2_2116_);
    leanh::lean_dec_ref(v_inst_2112_);
    return v_res_2117_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(
    mut v_00_u03b1_2118_: *mut leanh::LeanObject,
    mut v_00_u03b2_2119_: *mut leanh::LeanObject,
    mut v_inst_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = leanh::lean_box(0);
    return v___x_2121_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_2122_: *mut leanh::LeanObject,
    mut v_00_u03b2_2123_: *mut leanh::LeanObject,
    mut v_inst_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_2122_, v_00_u03b2_2123_, v_inst_2124_);
    leanh::lean_dec_ref(v_inst_2124_);
    return v_res_2125_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(
    mut v_carrier_2126_: *mut leanh::LeanObject,
    mut v_range_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2128_, 0, v_carrier_2126_);
    leanh::lean_ctor_set(v___x_2128_, 1, v_range_2127_);
    return v___x_2128_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice(
    mut v_00_u03b1_2130_: *mut leanh::LeanObject,
    mut v_00_u03b2_2131_: *mut leanh::LeanObject,
    mut v_inst_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2133_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0;
    return v___f_2133_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(
    mut v_00_u03b1_2134_: *mut leanh::LeanObject,
    mut v_00_u03b2_2135_: *mut leanh::LeanObject,
    mut v_inst_2136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(
        v_00_u03b1_2134_,
        v_00_u03b2_2135_,
        v_inst_2136_,
    );
    leanh::lean_dec_ref(v_inst_2136_);
    return v_res_2137_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(
    mut v_x_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2139_ = leanh::lean_ctor_get(v_x_2138_, 0);
                v_range_2140_ = leanh::lean_ctor_get(v_x_2138_, 1);
                v_isSharedCheck_2149_ = (!leanh::lean_is_exclusive(v_x_2138_)) as u8;
                if v_isSharedCheck_2149_ == 0 {
                    v___x_2142_ = v_x_2138_;
                    v_isShared_2143_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2140_);
                    leanh::lean_inc(v_treeMap_2139_);
                    leanh::lean_dec(v_x_2138_);
                    v___x_2142_ = leanh::lean_box(0);
                    v_isShared_2143_ = v_isSharedCheck_2149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2144_ = leanh::lean_box(0);
                v___x_2145_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2139_,
                    v___x_2144_,
                );
                leanh::lean_dec(v_treeMap_2139_);
                if v_isShared_2143_ == 0 {
                    leanh::lean_ctor_set(v___x_2142_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_range_2140_);
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
    mut v_00_u03b1_2151_: *mut leanh::LeanObject,
    mut v_00_u03b2_2152_: *mut leanh::LeanObject,
    mut v_inst_2153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2154_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0;
    return v___f_2154_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2155_: *mut leanh::LeanObject,
    mut v_00_u03b2_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(
        v_00_u03b1_2155_,
        v_00_u03b2_2156_,
        v_inst_2157_,
    );
    leanh::lean_dec_ref(v_inst_2157_);
    return v_res_2158_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(
    mut v_carrier_2159_: *mut leanh::LeanObject,
    mut v_range_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2161_, 0, v_carrier_2159_);
    leanh::lean_ctor_set(v___x_2161_, 1, v_range_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(
    mut v_00_u03b1_2163_: *mut leanh::LeanObject,
    mut v_inst_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2165_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0;
    return v___f_2165_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(
    mut v_00_u03b1_2166_: *mut leanh::LeanObject,
    mut v_inst_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_2166_, v_inst_2167_);
    leanh::lean_dec_ref(v_inst_2167_);
    return v_res_2168_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(
    mut v_x_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2170_ = leanh::lean_ctor_get(v_x_2169_, 0);
                v_range_2171_ = leanh::lean_ctor_get(v_x_2169_, 1);
                v_isSharedCheck_2180_ = (!leanh::lean_is_exclusive(v_x_2169_)) as u8;
                if v_isSharedCheck_2180_ == 0 {
                    v___x_2173_ = v_x_2169_;
                    v_isShared_2174_ = v_isSharedCheck_2180_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2171_);
                    leanh::lean_inc(v_treeMap_2170_);
                    leanh::lean_dec(v_x_2169_);
                    v___x_2173_ = leanh::lean_box(0);
                    v_isShared_2174_ = v_isSharedCheck_2180_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2175_ = leanh::lean_box(0);
                v___x_2176_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2170_,
                    v___x_2175_,
                );
                leanh::lean_dec(v_treeMap_2170_);
                if v_isShared_2174_ == 0 {
                    leanh::lean_ctor_set(v___x_2173_, 0, v___x_2176_);
                    v___x_2178_ = v___x_2173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_range_2171_);
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
    mut v_00_u03b1_2182_: *mut leanh::LeanObject,
    mut v_inst_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2184_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0;
    return v___f_2184_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2185_: *mut leanh::LeanObject,
    mut v_inst_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ =
        l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_2185_, v_inst_2186_);
    leanh::lean_dec_ref(v_inst_2186_);
    return v_res_2187_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(
    mut v_carrier_2188_: *mut leanh::LeanObject,
    mut v_range_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2190_, 0, v_carrier_2188_);
    leanh::lean_ctor_set(v___x_2190_, 1, v_range_2189_);
    return v___x_2190_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(
    mut v_00_u03b1_2192_: *mut leanh::LeanObject,
    mut v_00_u03b2_2193_: *mut leanh::LeanObject,
    mut v_inst_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2195_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0;
    return v___f_2195_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(
    mut v_00_u03b1_2196_: *mut leanh::LeanObject,
    mut v_00_u03b2_2197_: *mut leanh::LeanObject,
    mut v_inst_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(
        v_00_u03b1_2196_,
        v_00_u03b2_2197_,
        v_inst_2198_,
    );
    leanh::lean_dec_ref(v_inst_2198_);
    return v_res_2199_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(
    mut v_x_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2201_ = leanh::lean_ctor_get(v_x_2200_, 0);
                v_range_2202_ = leanh::lean_ctor_get(v_x_2200_, 1);
                v_isSharedCheck_2211_ = (!leanh::lean_is_exclusive(v_x_2200_)) as u8;
                if v_isSharedCheck_2211_ == 0 {
                    v___x_2204_ = v_x_2200_;
                    v_isShared_2205_ = v_isSharedCheck_2211_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2202_);
                    leanh::lean_inc(v_treeMap_2201_);
                    leanh::lean_dec(v_x_2200_);
                    v___x_2204_ = leanh::lean_box(0);
                    v_isShared_2205_ = v_isSharedCheck_2211_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2206_ = leanh::lean_box(0);
                v___x_2207_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2201_,
                    v___x_2206_,
                );
                leanh::lean_dec(v_treeMap_2201_);
                if v_isShared_2205_ == 0 {
                    leanh::lean_ctor_set(v___x_2204_, 0, v___x_2207_);
                    v___x_2209_ = v___x_2204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2210_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_range_2202_);
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
    mut v_00_u03b1_2213_: *mut leanh::LeanObject,
    mut v_00_u03b2_2214_: *mut leanh::LeanObject,
    mut v_inst_2215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2216_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0;
    return v___f_2216_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(
    mut v_00_u03b1_2217_: *mut leanh::LeanObject,
    mut v_00_u03b2_2218_: *mut leanh::LeanObject,
    mut v_inst_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(
        v_00_u03b1_2217_,
        v_00_u03b2_2218_,
        v_inst_2219_,
    );
    leanh::lean_dec_ref(v_inst_2219_);
    return v_res_2220_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(
    mut v_carrier_2221_: *mut leanh::LeanObject,
    mut v_range_2222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2223_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2223_, 0, v_carrier_2221_);
    leanh::lean_ctor_set(v___x_2223_, 1, v_range_2222_);
    return v___x_2223_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice(
    mut v_00_u03b1_2225_: *mut leanh::LeanObject,
    mut v_00_u03b2_2226_: *mut leanh::LeanObject,
    mut v_inst_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2228_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0;
    return v___f_2228_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(
    mut v_00_u03b1_2229_: *mut leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut leanh::LeanObject,
    mut v_inst_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(
        v_00_u03b1_2229_,
        v_00_u03b2_2230_,
        v_inst_2231_,
    );
    leanh::lean_dec_ref(v_inst_2231_);
    return v_res_2232_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(
    mut v_x_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2234_ = leanh::lean_ctor_get(v_x_2233_, 0);
                v_range_2235_ = leanh::lean_ctor_get(v_x_2233_, 1);
                v_isSharedCheck_2244_ = (!leanh::lean_is_exclusive(v_x_2233_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2237_ = v_x_2233_;
                    v_isShared_2238_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2235_);
                    leanh::lean_inc(v_treeMap_2234_);
                    leanh::lean_dec(v_x_2233_);
                    v___x_2237_ = leanh::lean_box(0);
                    v_isShared_2238_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2239_ = leanh::lean_box(0);
                v___x_2240_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2234_,
                    v___x_2239_,
                );
                leanh::lean_dec(v_treeMap_2234_);
                if v_isShared_2238_ == 0 {
                    leanh::lean_ctor_set(v___x_2237_, 0, v___x_2240_);
                    v___x_2242_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_range_2235_);
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
    mut v_00_u03b1_2246_: *mut leanh::LeanObject,
    mut v_00_u03b2_2247_: *mut leanh::LeanObject,
    mut v_inst_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2249_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0;
    return v___f_2249_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2250_: *mut leanh::LeanObject,
    mut v_00_u03b2_2251_: *mut leanh::LeanObject,
    mut v_inst_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(
        v_00_u03b1_2250_,
        v_00_u03b2_2251_,
        v_inst_2252_,
    );
    leanh::lean_dec_ref(v_inst_2252_);
    return v_res_2253_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(
    mut v_carrier_2254_: *mut leanh::LeanObject,
    mut v_range_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2256_, 0, v_carrier_2254_);
    leanh::lean_ctor_set(v___x_2256_, 1, v_range_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(
    mut v_00_u03b1_2258_: *mut leanh::LeanObject,
    mut v_inst_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2260_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0;
    return v___f_2260_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(
    mut v_00_u03b1_2261_: *mut leanh::LeanObject,
    mut v_inst_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2263_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_2261_, v_inst_2262_);
    leanh::lean_dec_ref(v_inst_2262_);
    return v_res_2263_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(
    mut v_x_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2265_ = leanh::lean_ctor_get(v_x_2264_, 0);
                v_range_2266_ = leanh::lean_ctor_get(v_x_2264_, 1);
                v_isSharedCheck_2275_ = (!leanh::lean_is_exclusive(v_x_2264_)) as u8;
                if v_isSharedCheck_2275_ == 0 {
                    v___x_2268_ = v_x_2264_;
                    v_isShared_2269_ = v_isSharedCheck_2275_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2266_);
                    leanh::lean_inc(v_treeMap_2265_);
                    leanh::lean_dec(v_x_2264_);
                    v___x_2268_ = leanh::lean_box(0);
                    v_isShared_2269_ = v_isSharedCheck_2275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2270_ = leanh::lean_box(0);
                v___x_2271_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2265_,
                    v___x_2270_,
                );
                leanh::lean_dec(v_treeMap_2265_);
                if v_isShared_2269_ == 0 {
                    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_range_2266_);
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
    mut v_00_u03b1_2277_: *mut leanh::LeanObject,
    mut v_inst_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2279_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0;
    return v___f_2279_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2280_: *mut leanh::LeanObject,
    mut v_inst_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ =
        l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_2280_, v_inst_2281_);
    leanh::lean_dec_ref(v_inst_2281_);
    return v_res_2282_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(
    mut v_carrier_2283_: *mut leanh::LeanObject,
    mut v_range_2284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2285_, 0, v_carrier_2283_);
    leanh::lean_ctor_set(v___x_2285_, 1, v_range_2284_);
    return v___x_2285_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(
    mut v_00_u03b1_2287_: *mut leanh::LeanObject,
    mut v_00_u03b2_2288_: *mut leanh::LeanObject,
    mut v_inst_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2290_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0;
    return v___f_2290_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(
    mut v_00_u03b1_2291_: *mut leanh::LeanObject,
    mut v_00_u03b2_2292_: *mut leanh::LeanObject,
    mut v_inst_2293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2294_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(
        v_00_u03b1_2291_,
        v_00_u03b2_2292_,
        v_inst_2293_,
    );
    leanh::lean_dec_ref(v_inst_2293_);
    return v_res_2294_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(
    mut v_x_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_treeMap_2296_ = leanh::lean_ctor_get(v_x_2295_, 0);
                v_range_2297_ = leanh::lean_ctor_get(v_x_2295_, 1);
                v_isSharedCheck_2306_ = (!leanh::lean_is_exclusive(v_x_2295_)) as u8;
                if v_isSharedCheck_2306_ == 0 {
                    v___x_2299_ = v_x_2295_;
                    v_isShared_2300_ = v_isSharedCheck_2306_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_range_2297_);
                    leanh::lean_inc(v_treeMap_2296_);
                    leanh::lean_dec(v_x_2295_);
                    v___x_2299_ = leanh::lean_box(0);
                    v_isShared_2300_ = v_isSharedCheck_2306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2301_ = leanh::lean_box(0);
                v___x_2302_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(
                    v_treeMap_2296_,
                    v___x_2301_,
                );
                leanh::lean_dec(v_treeMap_2296_);
                if v_isShared_2300_ == 0 {
                    leanh::lean_ctor_set(v___x_2299_, 0, v___x_2302_);
                    v___x_2304_ = v___x_2299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2305_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_range_2297_);
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
    mut v_00_u03b1_2308_: *mut leanh::LeanObject,
    mut v_00_u03b2_2309_: *mut leanh::LeanObject,
    mut v_inst_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2311_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0;
    return v___f_2311_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(
    mut v_00_u03b1_2312_: *mut leanh::LeanObject,
    mut v_00_u03b2_2313_: *mut leanh::LeanObject,
    mut v_inst_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(
        v_00_u03b1_2312_,
        v_00_u03b2_2313_,
        v_inst_2314_,
    );
    leanh::lean_dec_ref(v_inst_2314_);
    return v_res_2315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rccIterator___redArg(
    mut v_inst_2316_: *mut leanh::LeanObject,
    mut v_t_2317_: *mut leanh::LeanObject,
    mut v_lowerBound_2318_: *mut leanh::LeanObject,
    mut v_upperBound_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = leanh::lean_box(0);
    v___x_2321_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2316_,
        v_t_2317_,
        v_lowerBound_2318_,
        v___x_2320_,
    );
    v___x_2322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
    leanh::lean_ctor_set(v___x_2322_, 1, v_upperBound_2319_);
    return v___x_2322_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rccIterator(
    mut v_00_u03b1_2323_: *mut leanh::LeanObject,
    mut v_00_u03b2_2324_: *mut leanh::LeanObject,
    mut v_inst_2325_: *mut leanh::LeanObject,
    mut v_t_2326_: *mut leanh::LeanObject,
    mut v_lowerBound_2327_: *mut leanh::LeanObject,
    mut v_upperBound_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = leanh::lean_box(0);
    v___x_2330_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2325_,
        v_t_2326_,
        v_lowerBound_2327_,
        v___x_2329_,
    );
    v___x_2331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2331_, 0, v___x_2330_);
    leanh::lean_ctor_set(v___x_2331_, 1, v_upperBound_2328_);
    return v___x_2331_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(
    mut v_carrier_2332_: *mut leanh::LeanObject,
    mut v_range_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2334_, 0, v_carrier_2332_);
    leanh::lean_ctor_set(v___x_2334_, 1, v_range_2333_);
    return v___x_2334_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice(
    mut v_00_u03b1_2336_: *mut leanh::LeanObject,
    mut v_00_u03b2_2337_: *mut leanh::LeanObject,
    mut v_inst_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2339_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0;
    return v___f_2339_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(
    mut v_00_u03b1_2340_: *mut leanh::LeanObject,
    mut v_00_u03b2_2341_: *mut leanh::LeanObject,
    mut v_inst_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(
        v_00_u03b1_2340_,
        v_00_u03b2_2341_,
        v_inst_2342_,
    );
    leanh::lean_dec_ref(v_inst_2342_);
    return v_res_2343_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2344_: *mut leanh::LeanObject,
    mut v_x_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2346_ = leanh::lean_ctor_get(v_x_2345_, 1);
                leanh::lean_inc_ref(v_range_2346_);
                v_treeMap_2347_ = leanh::lean_ctor_get(v_x_2345_, 0);
                leanh::lean_inc(v_treeMap_2347_);
                leanh::lean_dec_ref(v_x_2345_);
                v_lower_2348_ = leanh::lean_ctor_get(v_range_2346_, 0);
                v_upper_2349_ = leanh::lean_ctor_get(v_range_2346_, 1);
                v_isSharedCheck_2358_ = (!leanh::lean_is_exclusive(v_range_2346_)) as u8;
                if v_isSharedCheck_2358_ == 0 {
                    v___x_2351_ = v_range_2346_;
                    v_isShared_2352_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2349_);
                    leanh::lean_inc(v_lower_2348_);
                    leanh::lean_dec(v_range_2346_);
                    v___x_2351_ = leanh::lean_box(0);
                    v_isShared_2352_ = v_isSharedCheck_2358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2353_ = leanh::lean_box(0);
                v___x_2354_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2344_,
                    v_treeMap_2347_,
                    v_lower_2348_,
                    v___x_2353_,
                );
                if v_isShared_2352_ == 0 {
                    leanh::lean_ctor_set(v___x_2351_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_upper_2349_);
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
    mut v_inst_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2360_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2360_, 0, v_inst_2359_);
    return v___f_2360_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RccSlice_instToIterator(
    mut v_00_u03b1_2361_: *mut leanh::LeanObject,
    mut v_00_u03b2_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2364_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2364_, 0, v_inst_2363_);
    return v___f_2364_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(
    mut v_carrier_2365_: *mut leanh::LeanObject,
    mut v_range_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2367_, 0, v_carrier_2365_);
    leanh::lean_ctor_set(v___x_2367_, 1, v_range_2366_);
    return v___x_2367_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(
    mut v_00_u03b1_2369_: *mut leanh::LeanObject,
    mut v_inst_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2371_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0;
    return v___f_2371_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(
    mut v_00_u03b1_2372_: *mut leanh::LeanObject,
    mut v_inst_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_2372_, v_inst_2373_);
    leanh::lean_dec_ref(v_inst_2373_);
    return v_res_2374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2375_: *mut leanh::LeanObject,
    mut v_x_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2377_ = leanh::lean_ctor_get(v_x_2376_, 1);
                leanh::lean_inc_ref(v_range_2377_);
                v_treeMap_2378_ = leanh::lean_ctor_get(v_x_2376_, 0);
                leanh::lean_inc(v_treeMap_2378_);
                leanh::lean_dec_ref(v_x_2376_);
                v_lower_2379_ = leanh::lean_ctor_get(v_range_2377_, 0);
                v_upper_2380_ = leanh::lean_ctor_get(v_range_2377_, 1);
                v_isSharedCheck_2389_ = (!leanh::lean_is_exclusive(v_range_2377_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v___x_2382_ = v_range_2377_;
                    v_isShared_2383_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2380_);
                    leanh::lean_inc(v_lower_2379_);
                    leanh::lean_dec(v_range_2377_);
                    v___x_2382_ = leanh::lean_box(0);
                    v_isShared_2383_ = v_isSharedCheck_2389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2384_ = leanh::lean_box(0);
                v___x_2385_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2375_,
                    v_treeMap_2378_,
                    v_lower_2379_,
                    v___x_2384_,
                );
                if v_isShared_2383_ == 0 {
                    leanh::lean_ctor_set(v___x_2382_, 0, v___x_2385_);
                    v___x_2387_ = v___x_2382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_upper_2380_);
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
    mut v_inst_2390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2391_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2391_, 0, v_inst_2390_);
    return v___f_2391_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(
    mut v_00_u03b1_2392_: *mut leanh::LeanObject,
    mut v_inst_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2394_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2394_, 0, v_inst_2393_);
    return v___f_2394_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(
    mut v_carrier_2395_: *mut leanh::LeanObject,
    mut v_range_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2397_, 0, v_carrier_2395_);
    leanh::lean_ctor_set(v___x_2397_, 1, v_range_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(
    mut v_00_u03b1_2399_: *mut leanh::LeanObject,
    mut v_00_u03b2_2400_: *mut leanh::LeanObject,
    mut v_inst_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2402_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0;
    return v___f_2402_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(
    mut v_00_u03b1_2403_: *mut leanh::LeanObject,
    mut v_00_u03b2_2404_: *mut leanh::LeanObject,
    mut v_inst_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(
        v_00_u03b1_2403_,
        v_00_u03b2_2404_,
        v_inst_2405_,
    );
    leanh::lean_dec_ref(v_inst_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(
    mut v_inst_2407_: *mut leanh::LeanObject,
    mut v_x_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2409_ = leanh::lean_ctor_get(v_x_2408_, 1);
                leanh::lean_inc_ref(v_range_2409_);
                v_treeMap_2410_ = leanh::lean_ctor_get(v_x_2408_, 0);
                leanh::lean_inc(v_treeMap_2410_);
                leanh::lean_dec_ref(v_x_2408_);
                v_lower_2411_ = leanh::lean_ctor_get(v_range_2409_, 0);
                v_upper_2412_ = leanh::lean_ctor_get(v_range_2409_, 1);
                v_isSharedCheck_2421_ = (!leanh::lean_is_exclusive(v_range_2409_)) as u8;
                if v_isSharedCheck_2421_ == 0 {
                    v___x_2414_ = v_range_2409_;
                    v_isShared_2415_ = v_isSharedCheck_2421_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2412_);
                    leanh::lean_inc(v_lower_2411_);
                    leanh::lean_dec(v_range_2409_);
                    v___x_2414_ = leanh::lean_box(0);
                    v_isShared_2415_ = v_isSharedCheck_2421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2416_ = leanh::lean_box(0);
                v___x_2417_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2407_,
                    v_treeMap_2410_,
                    v_lower_2411_,
                    v___x_2416_,
                );
                if v_isShared_2415_ == 0 {
                    leanh::lean_ctor_set(v___x_2414_, 0, v___x_2417_);
                    v___x_2419_ = v___x_2414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2420_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_upper_2412_);
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
    mut v_inst_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2423_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2423_, 0, v_inst_2422_);
    return v___f_2423_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(
    mut v_00_u03b1_2424_: *mut leanh::LeanObject,
    mut v_00_u03b2_2425_: *mut leanh::LeanObject,
    mut v_inst_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2427_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2427_, 0, v_inst_2426_);
    return v___f_2427_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rcoIterator___redArg(
    mut v_inst_2428_: *mut leanh::LeanObject,
    mut v_t_2429_: *mut leanh::LeanObject,
    mut v_lowerBound_2430_: *mut leanh::LeanObject,
    mut v_upperBound_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = leanh::lean_box(0);
    v___x_2433_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2428_,
        v_t_2429_,
        v_lowerBound_2430_,
        v___x_2432_,
    );
    v___x_2434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2434_, 0, v___x_2433_);
    leanh::lean_ctor_set(v___x_2434_, 1, v_upperBound_2431_);
    return v___x_2434_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rcoIterator(
    mut v_00_u03b1_2435_: *mut leanh::LeanObject,
    mut v_00_u03b2_2436_: *mut leanh::LeanObject,
    mut v_inst_2437_: *mut leanh::LeanObject,
    mut v_t_2438_: *mut leanh::LeanObject,
    mut v_lowerBound_2439_: *mut leanh::LeanObject,
    mut v_upperBound_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = leanh::lean_box(0);
    v___x_2442_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2437_,
        v_t_2438_,
        v_lowerBound_2439_,
        v___x_2441_,
    );
    v___x_2443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
    leanh::lean_ctor_set(v___x_2443_, 1, v_upperBound_2440_);
    return v___x_2443_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(
    mut v_carrier_2444_: *mut leanh::LeanObject,
    mut v_range_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2446_, 0, v_carrier_2444_);
    leanh::lean_ctor_set(v___x_2446_, 1, v_range_2445_);
    return v___x_2446_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(
    mut v_00_u03b1_2448_: *mut leanh::LeanObject,
    mut v_00_u03b2_2449_: *mut leanh::LeanObject,
    mut v_inst_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2451_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0;
    return v___f_2451_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(
    mut v_00_u03b1_2452_: *mut leanh::LeanObject,
    mut v_00_u03b2_2453_: *mut leanh::LeanObject,
    mut v_inst_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(
        v_00_u03b1_2452_,
        v_00_u03b2_2453_,
        v_inst_2454_,
    );
    leanh::lean_dec_ref(v_inst_2454_);
    return v_res_2455_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2456_: *mut leanh::LeanObject,
    mut v_x_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2458_ = leanh::lean_ctor_get(v_x_2457_, 1);
                leanh::lean_inc_ref(v_range_2458_);
                v_treeMap_2459_ = leanh::lean_ctor_get(v_x_2457_, 0);
                leanh::lean_inc(v_treeMap_2459_);
                leanh::lean_dec_ref(v_x_2457_);
                v_lower_2460_ = leanh::lean_ctor_get(v_range_2458_, 0);
                v_upper_2461_ = leanh::lean_ctor_get(v_range_2458_, 1);
                v_isSharedCheck_2470_ = (!leanh::lean_is_exclusive(v_range_2458_)) as u8;
                if v_isSharedCheck_2470_ == 0 {
                    v___x_2463_ = v_range_2458_;
                    v_isShared_2464_ = v_isSharedCheck_2470_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2461_);
                    leanh::lean_inc(v_lower_2460_);
                    leanh::lean_dec(v_range_2458_);
                    v___x_2463_ = leanh::lean_box(0);
                    v_isShared_2464_ = v_isSharedCheck_2470_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2465_ = leanh::lean_box(0);
                v___x_2466_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2456_,
                    v_treeMap_2459_,
                    v_lower_2460_,
                    v___x_2465_,
                );
                if v_isShared_2464_ == 0 {
                    leanh::lean_ctor_set(v___x_2463_, 0, v___x_2466_);
                    v___x_2468_ = v___x_2463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_upper_2461_);
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
    mut v_inst_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2472_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2472_, 0, v_inst_2471_);
    return v___f_2472_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RcoSlice_instToIterator(
    mut v_00_u03b1_2473_: *mut leanh::LeanObject,
    mut v_00_u03b2_2474_: *mut leanh::LeanObject,
    mut v_inst_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2476_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2476_, 0, v_inst_2475_);
    return v___f_2476_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(
    mut v_carrier_2477_: *mut leanh::LeanObject,
    mut v_range_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2479_, 0, v_carrier_2477_);
    leanh::lean_ctor_set(v___x_2479_, 1, v_range_2478_);
    return v___x_2479_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(
    mut v_00_u03b1_2481_: *mut leanh::LeanObject,
    mut v_inst_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2483_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0;
    return v___f_2483_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(
    mut v_00_u03b1_2484_: *mut leanh::LeanObject,
    mut v_inst_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2486_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_2484_, v_inst_2485_);
    leanh::lean_dec_ref(v_inst_2485_);
    return v_res_2486_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2487_: *mut leanh::LeanObject,
    mut v_x_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2495_: u8 = 0;
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2489_ = leanh::lean_ctor_get(v_x_2488_, 1);
                leanh::lean_inc_ref(v_range_2489_);
                v_treeMap_2490_ = leanh::lean_ctor_get(v_x_2488_, 0);
                leanh::lean_inc(v_treeMap_2490_);
                leanh::lean_dec_ref(v_x_2488_);
                v_lower_2491_ = leanh::lean_ctor_get(v_range_2489_, 0);
                v_upper_2492_ = leanh::lean_ctor_get(v_range_2489_, 1);
                v_isSharedCheck_2501_ = (!leanh::lean_is_exclusive(v_range_2489_)) as u8;
                if v_isSharedCheck_2501_ == 0 {
                    v___x_2494_ = v_range_2489_;
                    v_isShared_2495_ = v_isSharedCheck_2501_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2492_);
                    leanh::lean_inc(v_lower_2491_);
                    leanh::lean_dec(v_range_2489_);
                    v___x_2494_ = leanh::lean_box(0);
                    v_isShared_2495_ = v_isSharedCheck_2501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2496_ = leanh::lean_box(0);
                v___x_2497_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2487_,
                    v_treeMap_2490_,
                    v_lower_2491_,
                    v___x_2496_,
                );
                if v_isShared_2495_ == 0 {
                    leanh::lean_ctor_set(v___x_2494_, 0, v___x_2497_);
                    v___x_2499_ = v___x_2494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_upper_2492_);
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
    mut v_inst_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2503_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2503_, 0, v_inst_2502_);
    return v___f_2503_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(
    mut v_00_u03b1_2504_: *mut leanh::LeanObject,
    mut v_inst_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2506_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2506_, 0, v_inst_2505_);
    return v___f_2506_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(
    mut v_carrier_2507_: *mut leanh::LeanObject,
    mut v_range_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2509_, 0, v_carrier_2507_);
    leanh::lean_ctor_set(v___x_2509_, 1, v_range_2508_);
    return v___x_2509_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(
    mut v_00_u03b1_2511_: *mut leanh::LeanObject,
    mut v_00_u03b2_2512_: *mut leanh::LeanObject,
    mut v_inst_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2514_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0;
    return v___f_2514_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(
    mut v_00_u03b1_2515_: *mut leanh::LeanObject,
    mut v_00_u03b2_2516_: *mut leanh::LeanObject,
    mut v_inst_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2518_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(
        v_00_u03b1_2515_,
        v_00_u03b2_2516_,
        v_inst_2517_,
    );
    leanh::lean_dec_ref(v_inst_2517_);
    return v_res_2518_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_x_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2521_ = leanh::lean_ctor_get(v_x_2520_, 1);
                leanh::lean_inc_ref(v_range_2521_);
                v_treeMap_2522_ = leanh::lean_ctor_get(v_x_2520_, 0);
                leanh::lean_inc(v_treeMap_2522_);
                leanh::lean_dec_ref(v_x_2520_);
                v_lower_2523_ = leanh::lean_ctor_get(v_range_2521_, 0);
                v_upper_2524_ = leanh::lean_ctor_get(v_range_2521_, 1);
                v_isSharedCheck_2533_ = (!leanh::lean_is_exclusive(v_range_2521_)) as u8;
                if v_isSharedCheck_2533_ == 0 {
                    v___x_2526_ = v_range_2521_;
                    v_isShared_2527_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2524_);
                    leanh::lean_inc(v_lower_2523_);
                    leanh::lean_dec(v_range_2521_);
                    v___x_2526_ = leanh::lean_box(0);
                    v_isShared_2527_ = v_isSharedCheck_2533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2528_ = leanh::lean_box(0);
                v___x_2529_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
                    v_inst_2519_,
                    v_treeMap_2522_,
                    v_lower_2523_,
                    v___x_2528_,
                );
                if v_isShared_2527_ == 0 {
                    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_upper_2524_);
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
    mut v_inst_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2535_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2535_, 0, v_inst_2534_);
    return v___f_2535_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(
    mut v_00_u03b1_2536_: *mut leanh::LeanObject,
    mut v_00_u03b2_2537_: *mut leanh::LeanObject,
    mut v_inst_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2539_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2539_, 0, v_inst_2538_);
    return v___f_2539_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rooIterator___redArg(
    mut v_inst_2540_: *mut leanh::LeanObject,
    mut v_t_2541_: *mut leanh::LeanObject,
    mut v_lowerBound_2542_: *mut leanh::LeanObject,
    mut v_upperBound_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = leanh::lean_box(0);
    v___x_2545_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2540_,
        v_t_2541_,
        v_lowerBound_2542_,
        v___x_2544_,
    );
    v___x_2546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    leanh::lean_ctor_set(v___x_2546_, 1, v_upperBound_2543_);
    return v___x_2546_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rooIterator(
    mut v_00_u03b1_2547_: *mut leanh::LeanObject,
    mut v_00_u03b2_2548_: *mut leanh::LeanObject,
    mut v_inst_2549_: *mut leanh::LeanObject,
    mut v_t_2550_: *mut leanh::LeanObject,
    mut v_lowerBound_2551_: *mut leanh::LeanObject,
    mut v_upperBound_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = leanh::lean_box(0);
    v___x_2554_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2549_,
        v_t_2550_,
        v_lowerBound_2551_,
        v___x_2553_,
    );
    v___x_2555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2555_, 0, v___x_2554_);
    leanh::lean_ctor_set(v___x_2555_, 1, v_upperBound_2552_);
    return v___x_2555_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(
    mut v_carrier_2556_: *mut leanh::LeanObject,
    mut v_range_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2558_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2558_, 0, v_carrier_2556_);
    leanh::lean_ctor_set(v___x_2558_, 1, v_range_2557_);
    return v___x_2558_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice(
    mut v_00_u03b1_2560_: *mut leanh::LeanObject,
    mut v_00_u03b2_2561_: *mut leanh::LeanObject,
    mut v_inst_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2563_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0;
    return v___f_2563_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(
    mut v_00_u03b1_2564_: *mut leanh::LeanObject,
    mut v_00_u03b2_2565_: *mut leanh::LeanObject,
    mut v_inst_2566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(
        v_00_u03b1_2564_,
        v_00_u03b2_2565_,
        v_inst_2566_,
    );
    leanh::lean_dec_ref(v_inst_2566_);
    return v_res_2567_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2568_: *mut leanh::LeanObject,
    mut v_x_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2570_ = leanh::lean_ctor_get(v_x_2569_, 1);
                leanh::lean_inc_ref(v_range_2570_);
                v_treeMap_2571_ = leanh::lean_ctor_get(v_x_2569_, 0);
                leanh::lean_inc(v_treeMap_2571_);
                leanh::lean_dec_ref(v_x_2569_);
                v_lower_2572_ = leanh::lean_ctor_get(v_range_2570_, 0);
                v_upper_2573_ = leanh::lean_ctor_get(v_range_2570_, 1);
                v_isSharedCheck_2582_ = (!leanh::lean_is_exclusive(v_range_2570_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v___x_2575_ = v_range_2570_;
                    v_isShared_2576_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2573_);
                    leanh::lean_inc(v_lower_2572_);
                    leanh::lean_dec(v_range_2570_);
                    v___x_2575_ = leanh::lean_box(0);
                    v_isShared_2576_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2577_ = leanh::lean_box(0);
                v___x_2578_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2568_,
                    v_treeMap_2571_,
                    v_lower_2572_,
                    v___x_2577_,
                );
                if v_isShared_2576_ == 0 {
                    leanh::lean_ctor_set(v___x_2575_, 0, v___x_2578_);
                    v___x_2580_ = v___x_2575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_upper_2573_);
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
    mut v_inst_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2584_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2584_, 0, v_inst_2583_);
    return v___f_2584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RooSlice_instToIterator(
    mut v_00_u03b1_2585_: *mut leanh::LeanObject,
    mut v_00_u03b2_2586_: *mut leanh::LeanObject,
    mut v_inst_2587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2588_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2588_, 0, v_inst_2587_);
    return v___f_2588_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(
    mut v_carrier_2589_: *mut leanh::LeanObject,
    mut v_range_2590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2591_, 0, v_carrier_2589_);
    leanh::lean_ctor_set(v___x_2591_, 1, v_range_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(
    mut v_00_u03b1_2593_: *mut leanh::LeanObject,
    mut v_inst_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2595_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0;
    return v___f_2595_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(
    mut v_00_u03b1_2596_: *mut leanh::LeanObject,
    mut v_inst_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_2596_, v_inst_2597_);
    leanh::lean_dec_ref(v_inst_2597_);
    return v_res_2598_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2599_: *mut leanh::LeanObject,
    mut v_x_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2601_ = leanh::lean_ctor_get(v_x_2600_, 1);
                leanh::lean_inc_ref(v_range_2601_);
                v_treeMap_2602_ = leanh::lean_ctor_get(v_x_2600_, 0);
                leanh::lean_inc(v_treeMap_2602_);
                leanh::lean_dec_ref(v_x_2600_);
                v_lower_2603_ = leanh::lean_ctor_get(v_range_2601_, 0);
                v_upper_2604_ = leanh::lean_ctor_get(v_range_2601_, 1);
                v_isSharedCheck_2613_ = (!leanh::lean_is_exclusive(v_range_2601_)) as u8;
                if v_isSharedCheck_2613_ == 0 {
                    v___x_2606_ = v_range_2601_;
                    v_isShared_2607_ = v_isSharedCheck_2613_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2604_);
                    leanh::lean_inc(v_lower_2603_);
                    leanh::lean_dec(v_range_2601_);
                    v___x_2606_ = leanh::lean_box(0);
                    v_isShared_2607_ = v_isSharedCheck_2613_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2608_ = leanh::lean_box(0);
                v___x_2609_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2599_,
                    v_treeMap_2602_,
                    v_lower_2603_,
                    v___x_2608_,
                );
                if v_isShared_2607_ == 0 {
                    leanh::lean_ctor_set(v___x_2606_, 0, v___x_2609_);
                    v___x_2611_ = v___x_2606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2612_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_upper_2604_);
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
    mut v_inst_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2615_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2615_, 0, v_inst_2614_);
    return v___f_2615_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(
    mut v_00_u03b1_2616_: *mut leanh::LeanObject,
    mut v_inst_2617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2618_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2618_, 0, v_inst_2617_);
    return v___f_2618_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(
    mut v_carrier_2619_: *mut leanh::LeanObject,
    mut v_range_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2621_, 0, v_carrier_2619_);
    leanh::lean_ctor_set(v___x_2621_, 1, v_range_2620_);
    return v___x_2621_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(
    mut v_00_u03b1_2623_: *mut leanh::LeanObject,
    mut v_00_u03b2_2624_: *mut leanh::LeanObject,
    mut v_inst_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2626_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0;
    return v___f_2626_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(
    mut v_00_u03b1_2627_: *mut leanh::LeanObject,
    mut v_00_u03b2_2628_: *mut leanh::LeanObject,
    mut v_inst_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(
        v_00_u03b1_2627_,
        v_00_u03b2_2628_,
        v_inst_2629_,
    );
    leanh::lean_dec_ref(v_inst_2629_);
    return v_res_2630_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(
    mut v_inst_2631_: *mut leanh::LeanObject,
    mut v_x_2632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2633_ = leanh::lean_ctor_get(v_x_2632_, 1);
                leanh::lean_inc_ref(v_range_2633_);
                v_treeMap_2634_ = leanh::lean_ctor_get(v_x_2632_, 0);
                leanh::lean_inc(v_treeMap_2634_);
                leanh::lean_dec_ref(v_x_2632_);
                v_lower_2635_ = leanh::lean_ctor_get(v_range_2633_, 0);
                v_upper_2636_ = leanh::lean_ctor_get(v_range_2633_, 1);
                v_isSharedCheck_2645_ = (!leanh::lean_is_exclusive(v_range_2633_)) as u8;
                if v_isSharedCheck_2645_ == 0 {
                    v___x_2638_ = v_range_2633_;
                    v_isShared_2639_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2636_);
                    leanh::lean_inc(v_lower_2635_);
                    leanh::lean_dec(v_range_2633_);
                    v___x_2638_ = leanh::lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2640_ = leanh::lean_box(0);
                v___x_2641_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2631_,
                    v_treeMap_2634_,
                    v_lower_2635_,
                    v___x_2640_,
                );
                if v_isShared_2639_ == 0 {
                    leanh::lean_ctor_set(v___x_2638_, 0, v___x_2641_);
                    v___x_2643_ = v___x_2638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_upper_2636_);
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
    mut v_inst_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2647_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2647_, 0, v_inst_2646_);
    return v___f_2647_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(
    mut v_00_u03b1_2648_: *mut leanh::LeanObject,
    mut v_00_u03b2_2649_: *mut leanh::LeanObject,
    mut v_inst_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2651_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2651_, 0, v_inst_2650_);
    return v___f_2651_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rocIterator___redArg(
    mut v_inst_2652_: *mut leanh::LeanObject,
    mut v_t_2653_: *mut leanh::LeanObject,
    mut v_lowerBound_2654_: *mut leanh::LeanObject,
    mut v_upperBound_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = leanh::lean_box(0);
    v___x_2657_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2652_,
        v_t_2653_,
        v_lowerBound_2654_,
        v___x_2656_,
    );
    v___x_2658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2658_, 0, v___x_2657_);
    leanh::lean_ctor_set(v___x_2658_, 1, v_upperBound_2655_);
    return v___x_2658_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rocIterator(
    mut v_00_u03b1_2659_: *mut leanh::LeanObject,
    mut v_00_u03b2_2660_: *mut leanh::LeanObject,
    mut v_inst_2661_: *mut leanh::LeanObject,
    mut v_t_2662_: *mut leanh::LeanObject,
    mut v_lowerBound_2663_: *mut leanh::LeanObject,
    mut v_upperBound_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = leanh::lean_box(0);
    v___x_2666_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2661_,
        v_t_2662_,
        v_lowerBound_2663_,
        v___x_2665_,
    );
    v___x_2667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2667_, 0, v___x_2666_);
    leanh::lean_ctor_set(v___x_2667_, 1, v_upperBound_2664_);
    return v___x_2667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(
    mut v_carrier_2668_: *mut leanh::LeanObject,
    mut v_range_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2670_, 0, v_carrier_2668_);
    leanh::lean_ctor_set(v___x_2670_, 1, v_range_2669_);
    return v___x_2670_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice(
    mut v_00_u03b1_2672_: *mut leanh::LeanObject,
    mut v_00_u03b2_2673_: *mut leanh::LeanObject,
    mut v_inst_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2675_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0;
    return v___f_2675_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(
    mut v_00_u03b1_2676_: *mut leanh::LeanObject,
    mut v_00_u03b2_2677_: *mut leanh::LeanObject,
    mut v_inst_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(
        v_00_u03b1_2676_,
        v_00_u03b2_2677_,
        v_inst_2678_,
    );
    leanh::lean_dec_ref(v_inst_2678_);
    return v_res_2679_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2680_: *mut leanh::LeanObject,
    mut v_x_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2682_ = leanh::lean_ctor_get(v_x_2681_, 1);
                leanh::lean_inc_ref(v_range_2682_);
                v_treeMap_2683_ = leanh::lean_ctor_get(v_x_2681_, 0);
                leanh::lean_inc(v_treeMap_2683_);
                leanh::lean_dec_ref(v_x_2681_);
                v_lower_2684_ = leanh::lean_ctor_get(v_range_2682_, 0);
                v_upper_2685_ = leanh::lean_ctor_get(v_range_2682_, 1);
                v_isSharedCheck_2694_ = (!leanh::lean_is_exclusive(v_range_2682_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v___x_2687_ = v_range_2682_;
                    v_isShared_2688_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2685_);
                    leanh::lean_inc(v_lower_2684_);
                    leanh::lean_dec(v_range_2682_);
                    v___x_2687_ = leanh::lean_box(0);
                    v_isShared_2688_ = v_isSharedCheck_2694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2689_ = leanh::lean_box(0);
                v___x_2690_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2680_,
                    v_treeMap_2683_,
                    v_lower_2684_,
                    v___x_2689_,
                );
                if v_isShared_2688_ == 0 {
                    leanh::lean_ctor_set(v___x_2687_, 0, v___x_2690_);
                    v___x_2692_ = v___x_2687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_upper_2685_);
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
    mut v_inst_2695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2696_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2696_, 0, v_inst_2695_);
    return v___f_2696_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RocSlice_instToIterator(
    mut v_00_u03b1_2697_: *mut leanh::LeanObject,
    mut v_00_u03b2_2698_: *mut leanh::LeanObject,
    mut v_inst_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2700_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2700_, 0, v_inst_2699_);
    return v___f_2700_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(
    mut v_carrier_2701_: *mut leanh::LeanObject,
    mut v_range_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2703_, 0, v_carrier_2701_);
    leanh::lean_ctor_set(v___x_2703_, 1, v_range_2702_);
    return v___x_2703_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(
    mut v_00_u03b1_2705_: *mut leanh::LeanObject,
    mut v_inst_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2707_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0;
    return v___f_2707_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(
    mut v_00_u03b1_2708_: *mut leanh::LeanObject,
    mut v_inst_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_2708_, v_inst_2709_);
    leanh::lean_dec_ref(v_inst_2709_);
    return v_res_2710_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2711_: *mut leanh::LeanObject,
    mut v_x_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2713_ = leanh::lean_ctor_get(v_x_2712_, 1);
                leanh::lean_inc_ref(v_range_2713_);
                v_treeMap_2714_ = leanh::lean_ctor_get(v_x_2712_, 0);
                leanh::lean_inc(v_treeMap_2714_);
                leanh::lean_dec_ref(v_x_2712_);
                v_lower_2715_ = leanh::lean_ctor_get(v_range_2713_, 0);
                v_upper_2716_ = leanh::lean_ctor_get(v_range_2713_, 1);
                v_isSharedCheck_2725_ = (!leanh::lean_is_exclusive(v_range_2713_)) as u8;
                if v_isSharedCheck_2725_ == 0 {
                    v___x_2718_ = v_range_2713_;
                    v_isShared_2719_ = v_isSharedCheck_2725_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2716_);
                    leanh::lean_inc(v_lower_2715_);
                    leanh::lean_dec(v_range_2713_);
                    v___x_2718_ = leanh::lean_box(0);
                    v_isShared_2719_ = v_isSharedCheck_2725_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2720_ = leanh::lean_box(0);
                v___x_2721_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2711_,
                    v_treeMap_2714_,
                    v_lower_2715_,
                    v___x_2720_,
                );
                if v_isShared_2719_ == 0 {
                    leanh::lean_ctor_set(v___x_2718_, 0, v___x_2721_);
                    v___x_2723_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_upper_2716_);
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
    mut v_inst_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2727_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2727_, 0, v_inst_2726_);
    return v___f_2727_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(
    mut v_00_u03b1_2728_: *mut leanh::LeanObject,
    mut v_inst_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2730_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2730_, 0, v_inst_2729_);
    return v___f_2730_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(
    mut v_carrier_2731_: *mut leanh::LeanObject,
    mut v_range_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2733_, 0, v_carrier_2731_);
    leanh::lean_ctor_set(v___x_2733_, 1, v_range_2732_);
    return v___x_2733_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(
    mut v_00_u03b1_2735_: *mut leanh::LeanObject,
    mut v_00_u03b2_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2738_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0;
    return v___f_2738_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(
    mut v_00_u03b1_2739_: *mut leanh::LeanObject,
    mut v_00_u03b2_2740_: *mut leanh::LeanObject,
    mut v_inst_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2742_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(
        v_00_u03b1_2739_,
        v_00_u03b2_2740_,
        v_inst_2741_,
    );
    leanh::lean_dec_ref(v_inst_2741_);
    return v_res_2742_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(
    mut v_inst_2743_: *mut leanh::LeanObject,
    mut v_x_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_treeMap_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_2745_ = leanh::lean_ctor_get(v_x_2744_, 1);
                leanh::lean_inc_ref(v_range_2745_);
                v_treeMap_2746_ = leanh::lean_ctor_get(v_x_2744_, 0);
                leanh::lean_inc(v_treeMap_2746_);
                leanh::lean_dec_ref(v_x_2744_);
                v_lower_2747_ = leanh::lean_ctor_get(v_range_2745_, 0);
                v_upper_2748_ = leanh::lean_ctor_get(v_range_2745_, 1);
                v_isSharedCheck_2757_ = (!leanh::lean_is_exclusive(v_range_2745_)) as u8;
                if v_isSharedCheck_2757_ == 0 {
                    v___x_2750_ = v_range_2745_;
                    v_isShared_2751_ = v_isSharedCheck_2757_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_2748_);
                    leanh::lean_inc(v_lower_2747_);
                    leanh::lean_dec(v_range_2745_);
                    v___x_2750_ = leanh::lean_box(0);
                    v_isShared_2751_ = v_isSharedCheck_2757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2752_ = leanh::lean_box(0);
                v___x_2753_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
                    v_inst_2743_,
                    v_treeMap_2746_,
                    v_lower_2747_,
                    v___x_2752_,
                );
                if v_isShared_2751_ == 0 {
                    leanh::lean_ctor_set(v___x_2750_, 0, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_upper_2748_);
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
    mut v_inst_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2759_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2759_, 0, v_inst_2758_);
    return v___f_2759_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(
    mut v_00_u03b1_2760_: *mut leanh::LeanObject,
    mut v_00_u03b2_2761_: *mut leanh::LeanObject,
    mut v_inst_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2763_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2763_, 0, v_inst_2762_);
    return v___f_2763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rciIterator___redArg(
    mut v_inst_2764_: *mut leanh::LeanObject,
    mut v_t_2765_: *mut leanh::LeanObject,
    mut v_lowerBound_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = leanh::lean_box(0);
    v___x_2768_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2764_,
        v_t_2765_,
        v_lowerBound_2766_,
        v___x_2767_,
    );
    return v___x_2768_;
}
pub unsafe fn l_Std_DTreeMap_Internal_rciIterator(
    mut v_00_u03b1_2769_: *mut leanh::LeanObject,
    mut v_00_u03b2_2770_: *mut leanh::LeanObject,
    mut v_inst_2771_: *mut leanh::LeanObject,
    mut v_t_2772_: *mut leanh::LeanObject,
    mut v_lowerBound_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = leanh::lean_box(0);
    v___x_2775_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2771_,
        v_t_2772_,
        v_lowerBound_2773_,
        v___x_2774_,
    );
    return v___x_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(
    mut v_carrier_2776_: *mut leanh::LeanObject,
    mut v_range_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2778_, 0, v_carrier_2776_);
    leanh::lean_ctor_set(v___x_2778_, 1, v_range_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice(
    mut v_00_u03b1_2780_: *mut leanh::LeanObject,
    mut v_00_u03b2_2781_: *mut leanh::LeanObject,
    mut v_inst_2782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2783_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0;
    return v___f_2783_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(
    mut v_00_u03b1_2784_: *mut leanh::LeanObject,
    mut v_00_u03b2_2785_: *mut leanh::LeanObject,
    mut v_inst_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(
        v_00_u03b1_2784_,
        v_00_u03b2_2785_,
        v_inst_2786_,
    );
    leanh::lean_dec_ref(v_inst_2786_);
    return v_res_2787_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2788_: *mut leanh::LeanObject,
    mut v_x_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2790_ = leanh::lean_ctor_get(v_x_2789_, 0);
    leanh::lean_inc(v_treeMap_2790_);
    v_range_2791_ = leanh::lean_ctor_get(v_x_2789_, 1);
    leanh::lean_inc(v_range_2791_);
    leanh::lean_dec_ref(v_x_2789_);
    v___x_2792_ = leanh::lean_box(0);
    v___x_2793_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2788_,
        v_treeMap_2790_,
        v_range_2791_,
        v___x_2792_,
    );
    return v___x_2793_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(
    mut v_inst_2794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2795_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2795_, 0, v_inst_2794_);
    return v___f_2795_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RciSlice_instToIterator(
    mut v_00_u03b1_2796_: *mut leanh::LeanObject,
    mut v_00_u03b2_2797_: *mut leanh::LeanObject,
    mut v_inst_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2799_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2799_, 0, v_inst_2798_);
    return v___f_2799_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(
    mut v_carrier_2800_: *mut leanh::LeanObject,
    mut v_range_2801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2802_, 0, v_carrier_2800_);
    leanh::lean_ctor_set(v___x_2802_, 1, v_range_2801_);
    return v___x_2802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(
    mut v_00_u03b1_2804_: *mut leanh::LeanObject,
    mut v_inst_2805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2806_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0;
    return v___f_2806_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(
    mut v_00_u03b1_2807_: *mut leanh::LeanObject,
    mut v_inst_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_2807_, v_inst_2808_);
    leanh::lean_dec_ref(v_inst_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2810_: *mut leanh::LeanObject,
    mut v_x_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2812_ = leanh::lean_ctor_get(v_x_2811_, 0);
    leanh::lean_inc(v_treeMap_2812_);
    v_range_2813_ = leanh::lean_ctor_get(v_x_2811_, 1);
    leanh::lean_inc(v_range_2813_);
    leanh::lean_dec_ref(v_x_2811_);
    v___x_2814_ = leanh::lean_box(0);
    v___x_2815_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2810_,
        v_treeMap_2812_,
        v_range_2813_,
        v___x_2814_,
    );
    return v___x_2815_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(
    mut v_inst_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2817_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2817_, 0, v_inst_2816_);
    return v___f_2817_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(
    mut v_00_u03b1_2818_: *mut leanh::LeanObject,
    mut v_inst_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2820_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2820_, 0, v_inst_2819_);
    return v___f_2820_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(
    mut v_carrier_2821_: *mut leanh::LeanObject,
    mut v_range_2822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2823_, 0, v_carrier_2821_);
    leanh::lean_ctor_set(v___x_2823_, 1, v_range_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(
    mut v_00_u03b1_2825_: *mut leanh::LeanObject,
    mut v_00_u03b2_2826_: *mut leanh::LeanObject,
    mut v_inst_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2828_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0;
    return v___f_2828_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(
    mut v_00_u03b1_2829_: *mut leanh::LeanObject,
    mut v_00_u03b2_2830_: *mut leanh::LeanObject,
    mut v_inst_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(
        v_00_u03b1_2829_,
        v_00_u03b2_2830_,
        v_inst_2831_,
    );
    leanh::lean_dec_ref(v_inst_2831_);
    return v_res_2832_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(
    mut v_inst_2833_: *mut leanh::LeanObject,
    mut v_x_2834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2835_ = leanh::lean_ctor_get(v_x_2834_, 0);
    leanh::lean_inc(v_treeMap_2835_);
    v_range_2836_ = leanh::lean_ctor_get(v_x_2834_, 1);
    leanh::lean_inc(v_range_2836_);
    leanh::lean_dec_ref(v_x_2834_);
    v___x_2837_ = leanh::lean_box(0);
    v___x_2838_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(
        v_inst_2833_,
        v_treeMap_2835_,
        v_range_2836_,
        v___x_2837_,
    );
    return v___x_2838_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(
    mut v_inst_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2840_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2840_, 0, v_inst_2839_);
    return v___f_2840_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(
    mut v_00_u03b1_2841_: *mut leanh::LeanObject,
    mut v_00_u03b2_2842_: *mut leanh::LeanObject,
    mut v_inst_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2844_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2844_, 0, v_inst_2843_);
    return v___f_2844_;
}
pub unsafe fn l_Std_DTreeMap_Internal_roiIterator___redArg(
    mut v_inst_2845_: *mut leanh::LeanObject,
    mut v_t_2846_: *mut leanh::LeanObject,
    mut v_lowerBound_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = leanh::lean_box(0);
    v___x_2849_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2845_,
        v_t_2846_,
        v_lowerBound_2847_,
        v___x_2848_,
    );
    return v___x_2849_;
}
pub unsafe fn l_Std_DTreeMap_Internal_roiIterator(
    mut v_00_u03b1_2850_: *mut leanh::LeanObject,
    mut v_00_u03b2_2851_: *mut leanh::LeanObject,
    mut v_inst_2852_: *mut leanh::LeanObject,
    mut v_t_2853_: *mut leanh::LeanObject,
    mut v_lowerBound_2854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2855_ = leanh::lean_box(0);
    v___x_2856_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2852_,
        v_t_2853_,
        v_lowerBound_2854_,
        v___x_2855_,
    );
    return v___x_2856_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(
    mut v_carrier_2857_: *mut leanh::LeanObject,
    mut v_range_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2859_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2859_, 0, v_carrier_2857_);
    leanh::lean_ctor_set(v___x_2859_, 1, v_range_2858_);
    return v___x_2859_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(
    mut v_00_u03b1_2861_: *mut leanh::LeanObject,
    mut v_00_u03b2_2862_: *mut leanh::LeanObject,
    mut v_inst_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2864_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0;
    return v___f_2864_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(
    mut v_00_u03b1_2865_: *mut leanh::LeanObject,
    mut v_00_u03b2_2866_: *mut leanh::LeanObject,
    mut v_inst_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(
        v_00_u03b1_2865_,
        v_00_u03b2_2866_,
        v_inst_2867_,
    );
    leanh::lean_dec_ref(v_inst_2867_);
    return v_res_2868_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2869_: *mut leanh::LeanObject,
    mut v_x_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2871_ = leanh::lean_ctor_get(v_x_2870_, 0);
    leanh::lean_inc(v_treeMap_2871_);
    v_range_2872_ = leanh::lean_ctor_get(v_x_2870_, 1);
    leanh::lean_inc(v_range_2872_);
    leanh::lean_dec_ref(v_x_2870_);
    v___x_2873_ = leanh::lean_box(0);
    v___x_2874_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2869_,
        v_treeMap_2871_,
        v_range_2872_,
        v___x_2873_,
    );
    return v___x_2874_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(
    mut v_inst_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2876_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2876_, 0, v_inst_2875_);
    return v___f_2876_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RoiSlice_instToIterator(
    mut v_00_u03b1_2877_: *mut leanh::LeanObject,
    mut v_00_u03b2_2878_: *mut leanh::LeanObject,
    mut v_inst_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2880_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2880_, 0, v_inst_2879_);
    return v___f_2880_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(
    mut v_carrier_2881_: *mut leanh::LeanObject,
    mut v_range_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2883_, 0, v_carrier_2881_);
    leanh::lean_ctor_set(v___x_2883_, 1, v_range_2882_);
    return v___x_2883_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(
    mut v_00_u03b1_2885_: *mut leanh::LeanObject,
    mut v_inst_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2887_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0;
    return v___f_2887_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(
    mut v_00_u03b1_2888_: *mut leanh::LeanObject,
    mut v_inst_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ =
        l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_2888_, v_inst_2889_);
    leanh::lean_dec_ref(v_inst_2889_);
    return v_res_2890_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2891_: *mut leanh::LeanObject,
    mut v_x_2892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2893_ = leanh::lean_ctor_get(v_x_2892_, 0);
    leanh::lean_inc(v_treeMap_2893_);
    v_range_2894_ = leanh::lean_ctor_get(v_x_2892_, 1);
    leanh::lean_inc(v_range_2894_);
    leanh::lean_dec_ref(v_x_2892_);
    v___x_2895_ = leanh::lean_box(0);
    v___x_2896_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2891_,
        v_treeMap_2893_,
        v_range_2894_,
        v___x_2895_,
    );
    return v___x_2896_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(
    mut v_inst_2897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2898_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2898_, 0, v_inst_2897_);
    return v___f_2898_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(
    mut v_00_u03b1_2899_: *mut leanh::LeanObject,
    mut v_inst_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2901_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2901_, 0, v_inst_2900_);
    return v___f_2901_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(
    mut v_carrier_2902_: *mut leanh::LeanObject,
    mut v_range_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2904_, 0, v_carrier_2902_);
    leanh::lean_ctor_set(v___x_2904_, 1, v_range_2903_);
    return v___x_2904_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(
    mut v_00_u03b1_2906_: *mut leanh::LeanObject,
    mut v_00_u03b2_2907_: *mut leanh::LeanObject,
    mut v_inst_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2909_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0;
    return v___f_2909_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(
    mut v_00_u03b1_2910_: *mut leanh::LeanObject,
    mut v_00_u03b2_2911_: *mut leanh::LeanObject,
    mut v_inst_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(
        v_00_u03b1_2910_,
        v_00_u03b2_2911_,
        v_inst_2912_,
    );
    leanh::lean_dec_ref(v_inst_2912_);
    return v_res_2913_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(
    mut v_inst_2914_: *mut leanh::LeanObject,
    mut v_x_2915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2916_ = leanh::lean_ctor_get(v_x_2915_, 0);
    leanh::lean_inc(v_treeMap_2916_);
    v_range_2917_ = leanh::lean_ctor_get(v_x_2915_, 1);
    leanh::lean_inc(v_range_2917_);
    leanh::lean_dec_ref(v_x_2915_);
    v___x_2918_ = leanh::lean_box(0);
    v___x_2919_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(
        v_inst_2914_,
        v_treeMap_2916_,
        v_range_2917_,
        v___x_2918_,
    );
    return v___x_2919_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(
    mut v_inst_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2921_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2921_, 0, v_inst_2920_);
    return v___f_2921_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(
    mut v_00_u03b1_2922_: *mut leanh::LeanObject,
    mut v_00_u03b2_2923_: *mut leanh::LeanObject,
    mut v_inst_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2925_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2925_, 0, v_inst_2924_);
    return v___f_2925_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___redArg(
    mut v_t_2926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = leanh::lean_box(0);
    v___x_2928_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_2926_, v___x_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(
    mut v_t_2929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_2929_);
    leanh::lean_dec(v_t_2929_);
    return v_res_2930_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator(
    mut v_00_u03b1_2931_: *mut leanh::LeanObject,
    mut v_00_u03b2_2932_: *mut leanh::LeanObject,
    mut v_t_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_2933_);
    return v___x_2934_;
}
pub unsafe fn l_Std_DTreeMap_Internal_riiIterator___boxed(
    mut v_00_u03b1_2935_: *mut leanh::LeanObject,
    mut v_00_u03b2_2936_: *mut leanh::LeanObject,
    mut v_t_2937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2938_ =
        l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_2935_, v_00_u03b2_2936_, v_t_2937_);
    leanh::lean_dec(v_t_2937_);
    return v_res_2938_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(
    mut v_carrier_2939_: *mut leanh::LeanObject,
    mut v_range_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2941_, 0, v_carrier_2939_);
    leanh::lean_ctor_set(v___x_2941_, 1, v_range_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(
    mut v_00_u03b1_2943_: *mut leanh::LeanObject,
    mut v_00_u03b2_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2945_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0;
    return v___f_2945_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(
    mut v_x_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2947_ = leanh::lean_ctor_get(v_x_2946_, 0);
    v___x_2948_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_2947_);
    return v___x_2948_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(v_x_2949_);
    leanh::lean_dec_ref(v_x_2949_);
    return v_res_2950_;
}
pub unsafe fn l_Std_DTreeMap_Internal_RiiSlice_instToIterator(
    mut v_00_u03b1_2952_: *mut leanh::LeanObject,
    mut v_00_u03b2_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2954_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0;
    return v___f_2954_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(
    mut v_carrier_2955_: *mut leanh::LeanObject,
    mut v_range_2956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2957_, 0, v_carrier_2955_);
    leanh::lean_ctor_set(v___x_2957_, 1, v_range_2956_);
    return v___x_2957_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(
    mut v_00_u03b1_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2960_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0;
    return v___f_2960_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(
    mut v_x_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2962_ = leanh::lean_ctor_get(v_x_2961_, 0);
    v___x_2963_ = leanh::lean_box(0);
    v___x_2964_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_2962_, v___x_2963_);
    return v___x_2964_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(v_x_2965_);
    leanh::lean_dec_ref(v_x_2965_);
    return v_res_2966_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(
    mut v_00_u03b1_2968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2969_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0;
    return v___f_2969_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(
    mut v_carrier_2970_: *mut leanh::LeanObject,
    mut v_range_2971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2972_, 0, v_carrier_2970_);
    leanh::lean_ctor_set(v___x_2972_, 1, v_range_2971_);
    return v___x_2972_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(
    mut v_00_u03b1_2974_: *mut leanh::LeanObject,
    mut v_00_u03b2_2975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2976_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0;
    return v___f_2976_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(
    mut v_x_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_treeMap_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_treeMap_2978_ = leanh::lean_ctor_get(v_x_2977_, 0);
    v___x_2979_ = leanh::lean_box(0);
    v___x_2980_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(
    mut v_x_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(v_x_2981_);
    leanh::lean_dec_ref(v_x_2981_);
    return v_res_2982_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(
    mut v_00_u03b1_2984_: *mut leanh::LeanObject,
    mut v_00_u03b2_2985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2986_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0;
    return v___f_2986_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_InternalLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Zipper(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Zipper(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_InternalLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
}