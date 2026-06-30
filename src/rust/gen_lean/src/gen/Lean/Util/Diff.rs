// Lean compiler output
// Module: Lean.Util.Diff
// Imports: Init.Data.Array.Subarray.Split Init.Data.Slice.Array.Iterator Init.Data.Range Std.Data.HashMap.Basic Init.Data.String.Basic Init.Data.Range.Polymorphic.RangeIterator Init.While Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Data.ToString.Macro Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_size, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_string_append, lean_string_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::Split::{
    initialize_Init_Data_Array_Subarray_Split, l_Subarray_drop___redArg, l_Subarray_split___redArg,
    l_Subarray_take___redArg, runtime_initialize_Init_Data_Array_Subarray_Split,
};
use crate::r#gen::Init::Data::Array::Subarray::{
    l_Array_toSubarray___redArg, l_Subarray_get___redArg,
};
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Range::Polymorphic::RangeIterator::{
    initialize_Init_Data_Range_Polymorphic_RangeIterator,
    runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::Slice::Array::Iterator::{
    initialize_Init_Data_Slice_Array_Iterator, runtime_initialize_Init_Data_Slice_Array_Iterator,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::{
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    l_WellFounded_opaqueFix_u2083___redArg,
};
use crate::r#gen::Init::While::{
    initialize_Init_While, l___private_Init_While_0__whileM_erased___redArg,
    runtime_initialize_Init_While,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldrM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
pub static l_Lean_Diff_instReprAction_repr___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 68, 105, 102, 102, 46, 65, 99, 116, 105, 111, 110, 46, 105, 110,
            115, 101, 114, 116, 0,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instReprAction_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instReprAction_repr___closed__2_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 68, 105, 102, 102, 46, 65, 99, 116, 105, 111, 110, 46, 100, 101,
            108, 101, 116, 101, 0,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instReprAction_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instReprAction_repr___closed__4_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 68, 105, 102, 102, 46, 65, 99, 116, 105, 111, 110, 46, 115, 107,
            105, 112, 0,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instReprAction_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_instReprAction_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Diff_instReprAction_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Diff_instReprAction_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Diff_instReprAction_repr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Diff_instReprAction_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Diff_instReprAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_instReprAction_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_instReprAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Diff_instReprAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instReprAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instBEqAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_instBEqAction_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_instBEqAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instBEqAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Diff_instBEqAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instBEqAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instHashableAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_instHashableAction_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_instHashableAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instHashableAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Diff_instHashableAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instHashableAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Diff_instInhabitedAction_default: u8 = 0;
pub static mut l_Lean_Diff_instInhabitedAction: u8 = 0;
pub static l_Lean_Diff_instToStringAction___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 115, 101, 114, 116, 0],
};
static mut l_Lean_Diff_instToStringAction___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instToStringAction___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instToStringAction___lam__0___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 101, 108, 101, 116, 101, 0],
};
static mut l_Lean_Diff_instToStringAction___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instToStringAction___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instToStringAction___lam__0___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 107, 105, 112, 0],
};
static mut l_Lean_Diff_instToStringAction___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instToStringAction___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_instToStringAction___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_instToStringAction___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_instToStringAction___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instToStringAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Diff_instToStringAction: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_instToStringAction___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_Action_linePrefix___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [43, 0],
    };
static mut l_Lean_Diff_Action_linePrefix___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_Action_linePrefix___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_Action_linePrefix___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Lean_Diff_Action_linePrefix___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_Action_linePrefix___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_Action_linePrefix___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_Lean_Diff_Action_linePrefix___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_Action_linePrefix___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_matchPrefix___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Diff_matchPrefix___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_matchPrefix___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_lcs___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_lcs___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_lcs___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Diff_lcs___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Diff_lcs___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Diff_lcs___redArg___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Diff_lcs___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Diff_lcs___redArg___closed__12_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_lcs___redArg___lam__2 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__13_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_lcs___redArg___lam__3 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_lcs___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_lcs___redArg___closed__14_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_lcs___redArg___lam__4 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_lcs___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_lcs___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_diff___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_diff___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_diff___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_diff___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Diff_diff___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Diff_diff___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_diff___redArg___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Diff_diff___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_diff___redArg___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_diff___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_diff___redArg___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Diff_diff___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_diff___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_linesToString___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lean_Diff_linesToString___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_linesToString___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Diff_linesToString___redArg___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Diff_linesToString___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Diff_linesToString___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Diff_Action_ctorIdx(mut v_x_959_: u8) -> *mut leanh::LeanObject {
    match v_x_959_ {
        0 => {
            let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_960_ = leanh::lean_unsigned_to_nat(0);
            return v___x_960_;
        }
        1 => {
            let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_961_ = leanh::lean_unsigned_to_nat(1);
            return v___x_961_;
        }
        _ => {
            let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_962_ = leanh::lean_unsigned_to_nat(2);
            return v___x_962_;
        }
    }
}
pub unsafe fn l_Lean_Diff_Action_ctorIdx___boxed(
    mut v_x_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_964_: u8 = 0;
    let mut v_res_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_964_ = (leanh::lean_unbox(v_x_963_) as u8);
    v_res_965_ = l_Lean_Diff_Action_ctorIdx(v_x_boxed_964_);
    return v_res_965_;
}
pub unsafe fn l_Lean_Diff_Action_toCtorIdx(mut v_x_966_: u8) -> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Diff_Action_ctorIdx(v_x_966_);
    return v___x_967_;
}
pub unsafe fn l_Lean_Diff_Action_toCtorIdx___boxed(
    mut v_x_968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_969_: u8 = 0;
    let mut v_res_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_969_ = (leanh::lean_unbox(v_x_968_) as u8);
    v_res_970_ = l_Lean_Diff_Action_toCtorIdx(v_x_4__boxed_969_);
    return v_res_970_;
}
pub unsafe fn l_Lean_Diff_Action_ctorElim___redArg(
    mut v_k_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_971_);
    return v_k_971_;
}
pub unsafe fn l_Lean_Diff_Action_ctorElim___redArg___boxed(
    mut v_k_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ = l_Lean_Diff_Action_ctorElim___redArg(v_k_972_);
    leanh::lean_dec(v_k_972_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Diff_Action_ctorElim(
    mut v_motive_974_: *mut leanh::LeanObject,
    mut v_ctorIdx_975_: *mut leanh::LeanObject,
    mut v_t_976_: u8,
    mut v_h_977_: *mut leanh::LeanObject,
    mut v_k_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_978_);
    return v_k_978_;
}
pub unsafe fn l_Lean_Diff_Action_ctorElim___boxed(
    mut v_motive_979_: *mut leanh::LeanObject,
    mut v_ctorIdx_980_: *mut leanh::LeanObject,
    mut v_t_981_: *mut leanh::LeanObject,
    mut v_h_982_: *mut leanh::LeanObject,
    mut v_k_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_984_: u8 = 0;
    let mut v_res_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_984_ = (leanh::lean_unbox(v_t_981_) as u8);
    v_res_985_ = l_Lean_Diff_Action_ctorElim(
        v_motive_979_,
        v_ctorIdx_980_,
        v_t_boxed_984_,
        v_h_982_,
        v_k_983_,
    );
    leanh::lean_dec(v_k_983_);
    leanh::lean_dec(v_ctorIdx_980_);
    return v_res_985_;
}
pub unsafe fn l_Lean_Diff_Action_insert_elim___redArg(
    mut v_insert_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_insert_986_);
    return v_insert_986_;
}
pub unsafe fn l_Lean_Diff_Action_insert_elim___redArg___boxed(
    mut v_insert_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_Diff_Action_insert_elim___redArg(v_insert_987_);
    leanh::lean_dec(v_insert_987_);
    return v_res_988_;
}
pub unsafe fn l_Lean_Diff_Action_insert_elim(
    mut v_motive_989_: *mut leanh::LeanObject,
    mut v_t_990_: u8,
    mut v_h_991_: *mut leanh::LeanObject,
    mut v_insert_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_insert_992_);
    return v_insert_992_;
}
pub unsafe fn l_Lean_Diff_Action_insert_elim___boxed(
    mut v_motive_993_: *mut leanh::LeanObject,
    mut v_t_994_: *mut leanh::LeanObject,
    mut v_h_995_: *mut leanh::LeanObject,
    mut v_insert_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_997_: u8 = 0;
    let mut v_res_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_997_ = (leanh::lean_unbox(v_t_994_) as u8);
    v_res_998_ =
        l_Lean_Diff_Action_insert_elim(v_motive_993_, v_t_boxed_997_, v_h_995_, v_insert_996_);
    leanh::lean_dec(v_insert_996_);
    return v_res_998_;
}
pub unsafe fn l_Lean_Diff_Action_delete_elim___redArg(
    mut v_delete_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_delete_999_);
    return v_delete_999_;
}
pub unsafe fn l_Lean_Diff_Action_delete_elim___redArg___boxed(
    mut v_delete_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_Diff_Action_delete_elim___redArg(v_delete_1000_);
    leanh::lean_dec(v_delete_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Lean_Diff_Action_delete_elim(
    mut v_motive_1002_: *mut leanh::LeanObject,
    mut v_t_1003_: u8,
    mut v_h_1004_: *mut leanh::LeanObject,
    mut v_delete_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_delete_1005_);
    return v_delete_1005_;
}
pub unsafe fn l_Lean_Diff_Action_delete_elim___boxed(
    mut v_motive_1006_: *mut leanh::LeanObject,
    mut v_t_1007_: *mut leanh::LeanObject,
    mut v_h_1008_: *mut leanh::LeanObject,
    mut v_delete_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1010_: u8 = 0;
    let mut v_res_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1010_ = (leanh::lean_unbox(v_t_1007_) as u8);
    v_res_1011_ =
        l_Lean_Diff_Action_delete_elim(v_motive_1006_, v_t_boxed_1010_, v_h_1008_, v_delete_1009_);
    leanh::lean_dec(v_delete_1009_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_Diff_Action_skip_elim___redArg(
    mut v_skip_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_skip_1012_);
    return v_skip_1012_;
}
pub unsafe fn l_Lean_Diff_Action_skip_elim___redArg___boxed(
    mut v_skip_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Lean_Diff_Action_skip_elim___redArg(v_skip_1013_);
    leanh::lean_dec(v_skip_1013_);
    return v_res_1014_;
}
pub unsafe fn l_Lean_Diff_Action_skip_elim(
    mut v_motive_1015_: *mut leanh::LeanObject,
    mut v_t_1016_: u8,
    mut v_h_1017_: *mut leanh::LeanObject,
    mut v_skip_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_skip_1018_);
    return v_skip_1018_;
}
pub unsafe fn l_Lean_Diff_Action_skip_elim___boxed(
    mut v_motive_1019_: *mut leanh::LeanObject,
    mut v_t_1020_: *mut leanh::LeanObject,
    mut v_h_1021_: *mut leanh::LeanObject,
    mut v_skip_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1023_: u8 = 0;
    let mut v_res_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1023_ = (leanh::lean_unbox(v_t_1020_) as u8);
    v_res_1024_ =
        l_Lean_Diff_Action_skip_elim(v_motive_1019_, v_t_boxed_1023_, v_h_1021_, v_skip_1022_);
    leanh::lean_dec(v_skip_1022_);
    return v_res_1024_;
}
pub unsafe fn _init_l_Lean_Diff_instReprAction_repr___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = leanh::lean_unsigned_to_nat(2);
    v___x_1035_ = lean_nat_to_int(v___x_1034_);
    return v___x_1035_;
}
pub unsafe fn _init_l_Lean_Diff_instReprAction_repr___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = leanh::lean_unsigned_to_nat(1);
    v___x_1037_ = lean_nat_to_int(v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Lean_Diff_instReprAction_repr(
    mut v_x_1038_: u8,
    mut v_prec_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u8 = 0;
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1038_ {
                0 => {
                    v___x_1061_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1062_ = lean_nat_dec_le(v___x_1061_, v_prec_1039_);
                    if v___x_1062_ == 0 {
                        v___x_1063_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__6_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__6,
                        );
                        v___y_1041_ = v___x_1063_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1064_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__7_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__7,
                        );
                        v___y_1041_ = v___x_1064_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1065_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1066_ = lean_nat_dec_le(v___x_1065_, v_prec_1039_);
                    if v___x_1066_ == 0 {
                        v___x_1067_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__6_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__6,
                        );
                        v___y_1048_ = v___x_1067_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1068_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__7_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__7,
                        );
                        v___y_1048_ = v___x_1068_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1069_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1070_ = lean_nat_dec_le(v___x_1069_, v_prec_1039_);
                    if v___x_1070_ == 0 {
                        v___x_1071_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__6_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__6,
                        );
                        v___y_1055_ = v___x_1071_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1072_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Diff_instReprAction_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Diff_instReprAction_repr___closed__7_once
                            ),
                            _init_l_Lean_Diff_instReprAction_repr___closed__7,
                        );
                        v___y_1055_ = v___x_1072_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1042_ = l_Lean_Diff_instReprAction_repr___closed__1;
                leanh::lean_inc(v___y_1041_);
                v___x_1043_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1043_, 0, v___y_1041_);
                leanh::lean_ctor_set(v___x_1043_, 1, v___x_1042_);
                v___x_1044_ = 0;
                v___x_1045_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1045_, 0, v___x_1043_);
                leanh::lean_ctor_set_uint8(
                    v___x_1045_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1044_,
                );
                v___x_1046_ = l_Repr_addAppParen(v___x_1045_, v_prec_1039_);
                return v___x_1046_;
            }
            2 => {
                v___x_1049_ = l_Lean_Diff_instReprAction_repr___closed__3;
                leanh::lean_inc(v___y_1048_);
                v___x_1050_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1050_, 0, v___y_1048_);
                leanh::lean_ctor_set(v___x_1050_, 1, v___x_1049_);
                v___x_1051_ = 0;
                v___x_1052_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1052_, 0, v___x_1050_);
                leanh::lean_ctor_set_uint8(
                    v___x_1052_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1051_,
                );
                v___x_1053_ = l_Repr_addAppParen(v___x_1052_, v_prec_1039_);
                return v___x_1053_;
            }
            3 => {
                v___x_1056_ = l_Lean_Diff_instReprAction_repr___closed__5;
                leanh::lean_inc(v___y_1055_);
                v___x_1057_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1057_, 0, v___y_1055_);
                leanh::lean_ctor_set(v___x_1057_, 1, v___x_1056_);
                v___x_1058_ = 0;
                v___x_1059_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1059_, 0, v___x_1057_);
                leanh::lean_ctor_set_uint8(
                    v___x_1059_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1058_,
                );
                v___x_1060_ = l_Repr_addAppParen(v___x_1059_, v_prec_1039_);
                return v___x_1060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_instReprAction_repr___boxed(
    mut v_x_1073_: *mut leanh::LeanObject,
    mut v_prec_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_1075_: u8 = 0;
    let mut v_res_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1075_ = (leanh::lean_unbox(v_x_1073_) as u8);
    v_res_1076_ = l_Lean_Diff_instReprAction_repr(v_x_177__boxed_1075_, v_prec_1074_);
    leanh::lean_dec(v_prec_1074_);
    return v_res_1076_;
}
pub unsafe fn l_Lean_Diff_instBEqAction_beq(mut v_x_1079_: u8, mut v_y_1080_: u8) -> u8 {
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: u8 = 0;
    v___x_1081_ = l_Lean_Diff_Action_ctorIdx(v_x_1079_);
    v___x_1082_ = l_Lean_Diff_Action_ctorIdx(v_y_1080_);
    v___x_1083_ = lean_nat_dec_eq(v___x_1081_, v___x_1082_);
    leanh::lean_dec(v___x_1082_);
    leanh::lean_dec(v___x_1081_);
    return v___x_1083_;
}
pub unsafe fn l_Lean_Diff_instBEqAction_beq___boxed(
    mut v_x_1084_: *mut leanh::LeanObject,
    mut v_y_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_1086_: u8 = 0;
    let mut v_y_18__boxed_1087_: u8 = 0;
    let mut v_res_1088_: u8 = 0;
    let mut v_r_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1086_ = (leanh::lean_unbox(v_x_1084_) as u8);
    v_y_18__boxed_1087_ = (leanh::lean_unbox(v_y_1085_) as u8);
    v_res_1088_ = l_Lean_Diff_instBEqAction_beq(v_x_17__boxed_1086_, v_y_18__boxed_1087_);
    v_r_1089_ = leanh::lean_box((v_res_1088_) as usize);
    return v_r_1089_;
}
pub unsafe fn l_Lean_Diff_instHashableAction_hash(mut v_x_1092_: u8) -> u64 {
    match v_x_1092_ {
        0 => {
            let mut v___x_1093_: u64 = 0;
            v___x_1093_ = 0u64;
            return v___x_1093_;
        }
        1 => {
            let mut v___x_1094_: u64 = 0;
            v___x_1094_ = 1u64;
            return v___x_1094_;
        }
        _ => {
            let mut v___x_1095_: u64 = 0;
            v___x_1095_ = 2u64;
            return v___x_1095_;
        }
    }
}
pub unsafe fn l_Lean_Diff_instHashableAction_hash___boxed(
    mut v_x_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_40__boxed_1097_: u8 = 0;
    let mut v_res_1098_: u64 = 0;
    let mut v_r_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_1097_ = (leanh::lean_unbox(v_x_1096_) as u8);
    v_res_1098_ = l_Lean_Diff_instHashableAction_hash(v_x_40__boxed_1097_);
    v_r_1099_ = leanh::lean_box_uint64(v_res_1098_);
    return v_r_1099_;
}
pub unsafe fn _init_l_Lean_Diff_instInhabitedAction_default() -> u8 {
    let mut v___x_1102_: u8 = 0;
    v___x_1102_ = 0;
    return v___x_1102_;
}
pub unsafe fn _init_l_Lean_Diff_instInhabitedAction() -> u8 {
    let mut v___x_1103_: u8 = 0;
    v___x_1103_ = 0;
    return v___x_1103_;
}
pub unsafe fn l_Lean_Diff_instToStringAction___lam__0(
    mut v_x_1107_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1107_ {
        0 => {
            let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1108_ = l_Lean_Diff_instToStringAction___lam__0___closed__0;
            return v___x_1108_;
        }
        1 => {
            let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1109_ = l_Lean_Diff_instToStringAction___lam__0___closed__1;
            return v___x_1109_;
        }
        _ => {
            let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1110_ = l_Lean_Diff_instToStringAction___lam__0___closed__2;
            return v___x_1110_;
        }
    }
}
pub unsafe fn l_Lean_Diff_instToStringAction___lam__0___boxed(
    mut v_x_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1112_: u8 = 0;
    let mut v_res_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1112_ = (leanh::lean_unbox(v_x_1111_) as u8);
    v_res_1113_ = l_Lean_Diff_instToStringAction___lam__0(v_x_36__boxed_1112_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_Diff_Action_linePrefix(mut v_x_1119_: u8) -> *mut leanh::LeanObject {
    match v_x_1119_ {
        0 => {
            let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1120_ = l_Lean_Diff_Action_linePrefix___closed__0;
            return v___x_1120_;
        }
        1 => {
            let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1121_ = l_Lean_Diff_Action_linePrefix___closed__1;
            return v___x_1121_;
        }
        _ => {
            let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1122_ = l_Lean_Diff_Action_linePrefix___closed__2;
            return v___x_1122_;
        }
    }
}
pub unsafe fn l_Lean_Diff_Action_linePrefix___boxed(
    mut v_x_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_31__boxed_1124_: u8 = 0;
    let mut v_res_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_31__boxed_1124_ = (leanh::lean_unbox(v_x_1123_) as u8);
    v_res_1125_ = l_Lean_Diff_Action_linePrefix(v_x_31__boxed_1124_);
    return v_res_1125_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___redArg(
    mut v_inst_1126_: *mut leanh::LeanObject,
    mut v_inst_1127_: *mut leanh::LeanObject,
    mut v_histogram_1128_: *mut leanh::LeanObject,
    mut v_index_1129_: *mut leanh::LeanObject,
    mut v_val_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1141_: u8 = 0;
    let mut v_leftCount_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v_unused_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_val_1130_);
                leanh::lean_inc_ref(v_inst_1127_);
                leanh::lean_inc_ref(v_inst_1126_);
                v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_1126_,
                    v_inst_1127_,
                    v_histogram_1128_,
                    v_val_1130_,
                );
                if leanh::lean_obj_tag(v___x_1131_) == 0 {
                    v___x_1132_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1133_, 0, v_index_1129_);
                    v___x_1134_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1135_ = leanh::lean_box(0);
                    v___x_1136_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1136_, 0, v___x_1132_);
                    leanh::lean_ctor_set(v___x_1136_, 1, v___x_1133_);
                    leanh::lean_ctor_set(v___x_1136_, 2, v___x_1134_);
                    leanh::lean_ctor_set(v___x_1136_, 3, v___x_1135_);
                    v___x_1137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_1126_,
                        v_inst_1127_,
                        v_histogram_1128_,
                        v_val_1130_,
                        v___x_1136_,
                    );
                    return v___x_1137_;
                } else {
                    v_val_1138_ = leanh::lean_ctor_get(v___x_1131_, 0);
                    v_isSharedCheck_1159_ = (!leanh::lean_is_exclusive(v___x_1131_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v___x_1140_ = v___x_1131_;
                        v_isShared_1141_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1138_);
                        leanh::lean_dec(v___x_1131_);
                        v___x_1140_ = leanh::lean_box(0);
                        v_isShared_1141_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_1142_ = leanh::lean_ctor_get(v_val_1138_, 0);
                v_rightCount_1143_ = leanh::lean_ctor_get(v_val_1138_, 2);
                v_rightIndex_1144_ = leanh::lean_ctor_get(v_val_1138_, 3);
                v_isSharedCheck_1157_ = (!leanh::lean_is_exclusive(v_val_1138_)) as u8;
                if v_isSharedCheck_1157_ == 0 {
                    v_unused_1158_ = leanh::lean_ctor_get(v_val_1138_, 1);
                    leanh::lean_dec(v_unused_1158_);
                    v___x_1146_ = v_val_1138_;
                    v_isShared_1147_ = v_isSharedCheck_1157_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_rightIndex_1144_);
                    leanh::lean_inc(v_rightCount_1143_);
                    leanh::lean_inc(v_leftCount_1142_);
                    leanh::lean_dec(v_val_1138_);
                    v___x_1146_ = leanh::lean_box(0);
                    v_isShared_1147_ = v_isSharedCheck_1157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1148_ = leanh::lean_unsigned_to_nat(1);
                v___x_1149_ = lean_nat_add(v_leftCount_1142_, v___x_1148_);
                leanh::lean_dec(v_leftCount_1142_);
                if v_isShared_1141_ == 0 {
                    leanh::lean_ctor_set(v___x_1140_, 0, v_index_1129_);
                    v___x_1151_ = v___x_1140_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_index_1129_);
                    v___x_1151_ = v_reuseFailAlloc_1156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1147_ == 0 {
                    leanh::lean_ctor_set(v___x_1146_, 1, v___x_1151_);
                    leanh::lean_ctor_set(v___x_1146_, 0, v___x_1149_);
                    v___x_1153_ = v___x_1146_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1149_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_rightCount_1143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_rightIndex_1144_);
                    v___x_1153_ = v_reuseFailAlloc_1155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_1126_,
                    v_inst_1127_,
                    v_histogram_1128_,
                    v_val_1130_,
                    v___x_1153_,
                );
                return v___x_1154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft(
    mut v_00_u03b1_1160_: *mut leanh::LeanObject,
    mut v_inst_1161_: *mut leanh::LeanObject,
    mut v_inst_1162_: *mut leanh::LeanObject,
    mut v_lsize_1163_: *mut leanh::LeanObject,
    mut v_rsize_1164_: *mut leanh::LeanObject,
    mut v_histogram_1165_: *mut leanh::LeanObject,
    mut v_index_1166_: *mut leanh::LeanObject,
    mut v_val_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = l_Lean_Diff_Histogram_addLeft___redArg(
        v_inst_1161_,
        v_inst_1162_,
        v_histogram_1165_,
        v_index_1166_,
        v_val_1167_,
    );
    return v___x_1168_;
}
pub unsafe fn l_Lean_Diff_Histogram_addLeft___boxed(
    mut v_00_u03b1_1169_: *mut leanh::LeanObject,
    mut v_inst_1170_: *mut leanh::LeanObject,
    mut v_inst_1171_: *mut leanh::LeanObject,
    mut v_lsize_1172_: *mut leanh::LeanObject,
    mut v_rsize_1173_: *mut leanh::LeanObject,
    mut v_histogram_1174_: *mut leanh::LeanObject,
    mut v_index_1175_: *mut leanh::LeanObject,
    mut v_val_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_Lean_Diff_Histogram_addLeft(
        v_00_u03b1_1169_,
        v_inst_1170_,
        v_inst_1171_,
        v_lsize_1172_,
        v_rsize_1173_,
        v_histogram_1174_,
        v_index_1175_,
        v_val_1176_,
    );
    leanh::lean_dec(v_rsize_1173_);
    leanh::lean_dec(v_lsize_1172_);
    return v_res_1177_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___redArg(
    mut v_inst_1178_: *mut leanh::LeanObject,
    mut v_inst_1179_: *mut leanh::LeanObject,
    mut v_histogram_1180_: *mut leanh::LeanObject,
    mut v_index_1181_: *mut leanh::LeanObject,
    mut v_val_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v_leftCount_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_unused_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_val_1182_);
                leanh::lean_inc_ref(v_inst_1179_);
                leanh::lean_inc_ref(v_inst_1178_);
                v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_1178_,
                    v_inst_1179_,
                    v_histogram_1180_,
                    v_val_1182_,
                );
                if leanh::lean_obj_tag(v___x_1183_) == 0 {
                    v___x_1184_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1185_ = leanh::lean_box(0);
                    v___x_1186_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1187_, 0, v_index_1181_);
                    v___x_1188_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1188_, 0, v___x_1184_);
                    leanh::lean_ctor_set(v___x_1188_, 1, v___x_1185_);
                    leanh::lean_ctor_set(v___x_1188_, 2, v___x_1186_);
                    leanh::lean_ctor_set(v___x_1188_, 3, v___x_1187_);
                    v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v_inst_1178_,
                        v_inst_1179_,
                        v_histogram_1180_,
                        v_val_1182_,
                        v___x_1188_,
                    );
                    return v___x_1189_;
                } else {
                    v_val_1190_ = leanh::lean_ctor_get(v___x_1183_, 0);
                    v_isSharedCheck_1211_ = (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                    if v_isSharedCheck_1211_ == 0 {
                        v___x_1192_ = v___x_1183_;
                        v_isShared_1193_ = v_isSharedCheck_1211_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1190_);
                        leanh::lean_dec(v___x_1183_);
                        v___x_1192_ = leanh::lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_leftCount_1194_ = leanh::lean_ctor_get(v_val_1190_, 0);
                v_leftIndex_1195_ = leanh::lean_ctor_get(v_val_1190_, 1);
                v_isSharedCheck_1208_ = (!leanh::lean_is_exclusive(v_val_1190_)) as u8;
                if v_isSharedCheck_1208_ == 0 {
                    v_unused_1209_ = leanh::lean_ctor_get(v_val_1190_, 3);
                    leanh::lean_dec(v_unused_1209_);
                    v_unused_1210_ = leanh::lean_ctor_get(v_val_1190_, 2);
                    leanh::lean_dec(v_unused_1210_);
                    v___x_1197_ = v_val_1190_;
                    v_isShared_1198_ = v_isSharedCheck_1208_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_leftIndex_1195_);
                    leanh::lean_inc(v_leftCount_1194_);
                    leanh::lean_dec(v_val_1190_);
                    v___x_1197_ = leanh::lean_box(0);
                    v_isShared_1198_ = v_isSharedCheck_1208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1199_ = leanh::lean_unsigned_to_nat(1);
                v___x_1200_ = lean_nat_add(v_leftCount_1194_, v___x_1199_);
                if v_isShared_1193_ == 0 {
                    leanh::lean_ctor_set(v___x_1192_, 0, v_index_1181_);
                    v___x_1202_ = v___x_1192_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_index_1181_);
                    v___x_1202_ = v_reuseFailAlloc_1207_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1198_ == 0 {
                    leanh::lean_ctor_set(v___x_1197_, 3, v___x_1202_);
                    leanh::lean_ctor_set(v___x_1197_, 2, v___x_1200_);
                    v___x_1204_ = v___x_1197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_leftCount_1194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_leftIndex_1195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 2, v___x_1200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 3, v___x_1202_);
                    v___x_1204_ = v_reuseFailAlloc_1206_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v_inst_1178_,
                    v_inst_1179_,
                    v_histogram_1180_,
                    v_val_1182_,
                    v___x_1204_,
                );
                return v___x_1205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_Histogram_addRight(
    mut v_00_u03b1_1212_: *mut leanh::LeanObject,
    mut v_inst_1213_: *mut leanh::LeanObject,
    mut v_inst_1214_: *mut leanh::LeanObject,
    mut v_lsize_1215_: *mut leanh::LeanObject,
    mut v_rsize_1216_: *mut leanh::LeanObject,
    mut v_histogram_1217_: *mut leanh::LeanObject,
    mut v_index_1218_: *mut leanh::LeanObject,
    mut v_val_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = l_Lean_Diff_Histogram_addRight___redArg(
        v_inst_1213_,
        v_inst_1214_,
        v_histogram_1217_,
        v_index_1218_,
        v_val_1219_,
    );
    return v___x_1220_;
}
pub unsafe fn l_Lean_Diff_Histogram_addRight___boxed(
    mut v_00_u03b1_1221_: *mut leanh::LeanObject,
    mut v_inst_1222_: *mut leanh::LeanObject,
    mut v_inst_1223_: *mut leanh::LeanObject,
    mut v_lsize_1224_: *mut leanh::LeanObject,
    mut v_rsize_1225_: *mut leanh::LeanObject,
    mut v_histogram_1226_: *mut leanh::LeanObject,
    mut v_index_1227_: *mut leanh::LeanObject,
    mut v_val_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Lean_Diff_Histogram_addRight(
        v_00_u03b1_1221_,
        v_inst_1222_,
        v_inst_1223_,
        v_lsize_1224_,
        v_rsize_1225_,
        v_histogram_1226_,
        v_index_1227_,
        v_val_1228_,
    );
    leanh::lean_dec(v_rsize_1225_);
    leanh::lean_dec(v_lsize_1224_);
    return v_res_1229_;
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(
    mut v_inst_1230_: *mut leanh::LeanObject,
    mut v_left_1231_: *mut leanh::LeanObject,
    mut v_right_1232_: *mut leanh::LeanObject,
    mut v_pref_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v_start_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1234_ = leanh::lean_ctor_get(v_left_1231_, 1);
                v_stop_1235_ = leanh::lean_ctor_get(v_left_1231_, 2);
                v_i_1236_ = lean_array_get_size(v_pref_1233_);
                v___x_1242_ = lean_nat_sub(v_stop_1235_, v_start_1234_);
                v___x_1243_ = lean_nat_dec_lt(v_i_1236_, v___x_1242_);
                leanh::lean_dec(v___x_1242_);
                if v___x_1243_ == 0 {
                    leanh::lean_dec_ref(v_inst_1230_);
                    state = 1;
                    continue;
                } else {
                    v_start_1244_ = leanh::lean_ctor_get(v_right_1232_, 1);
                    v_stop_1245_ = leanh::lean_ctor_get(v_right_1232_, 2);
                    v___x_1246_ = lean_nat_sub(v_stop_1245_, v_start_1244_);
                    v___x_1247_ = lean_nat_dec_lt(v_i_1236_, v___x_1246_);
                    leanh::lean_dec(v___x_1246_);
                    if v___x_1247_ == 0 {
                        leanh::lean_dec_ref(v_inst_1230_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1248_ = l_Subarray_get___redArg(v_left_1231_, v_i_1236_);
                        v___x_1249_ = l_Subarray_get___redArg(v_right_1232_, v_i_1236_);
                        leanh::lean_inc_ref(v_inst_1230_);
                        leanh::lean_inc(v___x_1248_);
                        v___x_1250_ =
                            leanh::lean_apply_2(v_inst_1230_, v___x_1248_, v___x_1249_);
                        v___x_1251_ = (leanh::lean_unbox(v___x_1250_) as u8);
                        if v___x_1251_ == 0 {
                            leanh::lean_dec(v___x_1248_);
                            leanh::lean_dec_ref(v_inst_1230_);
                            v___x_1252_ = l_Subarray_drop___redArg(v_left_1231_, v_i_1236_);
                            v___x_1253_ = l_Subarray_drop___redArg(v_right_1232_, v_i_1236_);
                            v___x_1254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1254_, 0, v___x_1252_);
                            leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
                            v___x_1255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1255_, 0, v_pref_1233_);
                            leanh::lean_ctor_set(v___x_1255_, 1, v___x_1254_);
                            return v___x_1255_;
                        } else {
                            v___x_1256_ = lean_array_push(v_pref_1233_, v___x_1248_);
                            v_pref_1233_ = v___x_1256_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1238_ = l_Subarray_drop___redArg(v_left_1231_, v_i_1236_);
                v___x_1239_ = l_Subarray_drop___redArg(v_right_1232_, v_i_1236_);
                v___x_1240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v___x_1238_);
                leanh::lean_ctor_set(v___x_1240_, 1, v___x_1239_);
                v___x_1241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1241_, 0, v_pref_1233_);
                leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
                return v___x_1241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go(
    mut v_00_u03b1_1258_: *mut leanh::LeanObject,
    mut v_inst_1259_: *mut leanh::LeanObject,
    mut v_left_1260_: *mut leanh::LeanObject,
    mut v_right_1261_: *mut leanh::LeanObject,
    mut v_pref_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(
        v_inst_1259_,
        v_left_1260_,
        v_right_1261_,
        v_pref_1262_,
    );
    return v___x_1263_;
}
pub unsafe fn l_Lean_Diff_matchPrefix___redArg(
    mut v_inst_1266_: *mut leanh::LeanObject,
    mut v_left_1267_: *mut leanh::LeanObject,
    mut v_right_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Lean_Diff_matchPrefix___redArg___closed__0;
    v___x_1270_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___redArg(
        v_inst_1266_,
        v_left_1267_,
        v_right_1268_,
        v___x_1269_,
    );
    return v___x_1270_;
}
pub unsafe fn l_Lean_Diff_matchPrefix(
    mut v_00_u03b1_1271_: *mut leanh::LeanObject,
    mut v_inst_1272_: *mut leanh::LeanObject,
    mut v_left_1273_: *mut leanh::LeanObject,
    mut v_right_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_Lean_Diff_matchPrefix___redArg(v_inst_1272_, v_left_1273_, v_right_1274_);
    return v___x_1275_;
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___lam__0(
    mut v_it_1276_: *mut leanh::LeanObject,
    mut v_acc_1277_: *mut leanh::LeanObject,
    mut v_recur_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1284_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1279_ = leanh::lean_ctor_get(v_it_1276_, 0);
                v_start_1280_ = leanh::lean_ctor_get(v_it_1276_, 1);
                v_stop_1281_ = leanh::lean_ctor_get(v_it_1276_, 2);
                v_isSharedCheck_1294_ = (!leanh::lean_is_exclusive(v_it_1276_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v___x_1283_ = v_it_1276_;
                    v_isShared_1284_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_1281_);
                    leanh::lean_inc(v_start_1280_);
                    leanh::lean_inc(v_array_1279_);
                    leanh::lean_dec(v_it_1276_);
                    v___x_1283_ = leanh::lean_box(0);
                    v_isShared_1284_ = v_isSharedCheck_1294_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1285_ = lean_nat_dec_lt(v_start_1280_, v_stop_1281_);
                if v___x_1285_ == 0 {
                    leanh::lean_del_object(v___x_1283_);
                    leanh::lean_dec(v_stop_1281_);
                    leanh::lean_dec(v_start_1280_);
                    leanh::lean_dec_ref(v_array_1279_);
                    leanh::lean_dec_ref(v_recur_1278_);
                    return v_acc_1277_;
                } else {
                    v___x_1286_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1287_ = lean_nat_add(v_start_1280_, v___x_1286_);
                    leanh::lean_inc_ref(v_array_1279_);
                    if v_isShared_1284_ == 0 {
                        leanh::lean_ctor_set(v___x_1283_, 1, v___x_1287_);
                        v___x_1289_ = v___x_1283_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1293_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_array_1279_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1287_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_stop_1281_);
                        v___x_1289_ = v_reuseFailAlloc_1293_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1290_ = lean_array_fget(v_array_1279_, v_start_1280_);
                leanh::lean_dec(v_start_1280_);
                leanh::lean_dec_ref(v_array_1279_);
                v___x_1291_ = lean_array_push(v_acc_1277_, v___x_1290_);
                v___x_1292_ = leanh::lean_apply_3(
                    v_recur_1278_,
                    v___x_1289_,
                    v___x_1291_,
                    leanh::lean_box(0),
                );
                return v___x_1292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(
    mut v_inst_1296_: *mut leanh::LeanObject,
    mut v_left_1297_: *mut leanh::LeanObject,
    mut v_right_1298_: *mut leanh::LeanObject,
    mut v_i_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u8 = 0;
    let mut v_start_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: u8 = 0;
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1300_ = leanh::lean_ctor_get(v_left_1297_, 1);
                v_stop_1301_ = leanh::lean_ctor_get(v_left_1297_, 2);
                v___f_1302_ =
                    l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg___closed__0;
                v___x_1303_ = lean_nat_sub(v_stop_1301_, v_start_1300_);
                v___x_1317_ = lean_nat_dec_lt(v_i_1299_, v___x_1303_);
                if v___x_1317_ == 0 {
                    leanh::lean_dec_ref(v_inst_1296_);
                    state = 1;
                    continue;
                } else {
                    v_start_1318_ = leanh::lean_ctor_get(v_right_1298_, 1);
                    v_stop_1319_ = leanh::lean_ctor_get(v_right_1298_, 2);
                    v___x_1320_ = lean_nat_sub(v_stop_1319_, v_start_1318_);
                    v___x_1321_ = lean_nat_dec_lt(v_i_1299_, v___x_1320_);
                    if v___x_1321_ == 0 {
                        leanh::lean_dec(v___x_1320_);
                        leanh::lean_dec_ref(v_inst_1296_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1322_ = lean_nat_sub(v___x_1303_, v_i_1299_);
                        leanh::lean_dec(v___x_1303_);
                        v___x_1323_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1324_ = lean_nat_sub(v___x_1322_, v___x_1323_);
                        v___x_1325_ = l_Subarray_get___redArg(v_left_1297_, v___x_1324_);
                        leanh::lean_dec(v___x_1324_);
                        v___x_1326_ = lean_nat_sub(v___x_1320_, v_i_1299_);
                        leanh::lean_dec(v___x_1320_);
                        v___x_1327_ = lean_nat_sub(v___x_1326_, v___x_1323_);
                        v___x_1328_ = l_Subarray_get___redArg(v_right_1298_, v___x_1327_);
                        leanh::lean_dec(v___x_1327_);
                        leanh::lean_inc_ref(v_inst_1296_);
                        v___x_1329_ =
                            leanh::lean_apply_2(v_inst_1296_, v___x_1325_, v___x_1328_);
                        v___x_1330_ = (leanh::lean_unbox(v___x_1329_) as u8);
                        if v___x_1330_ == 0 {
                            leanh::lean_dec(v_i_1299_);
                            leanh::lean_dec_ref(v_inst_1296_);
                            leanh::lean_inc_ref(v_left_1297_);
                            v___x_1331_ = l_Subarray_take___redArg(v_left_1297_, v___x_1322_);
                            v___x_1332_ = l_Subarray_take___redArg(v_right_1298_, v___x_1326_);
                            leanh::lean_dec(v___x_1326_);
                            v___x_1333_ = l_Subarray_drop___redArg(v_left_1297_, v___x_1322_);
                            leanh::lean_dec(v___x_1322_);
                            v___x_1334_ = l_Lean_Diff_matchPrefix___redArg___closed__0;
                            v___x_1335_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_1302_, v___x_1333_, v___x_1334_);
                            v___x_1336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1336_, 0, v___x_1332_);
                            leanh::lean_ctor_set(v___x_1336_, 1, v___x_1335_);
                            v___x_1337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1337_, 0, v___x_1331_);
                            leanh::lean_ctor_set(v___x_1337_, 1, v___x_1336_);
                            return v___x_1337_;
                        } else {
                            leanh::lean_dec(v___x_1326_);
                            leanh::lean_dec(v___x_1322_);
                            v___x_1338_ = lean_nat_add(v_i_1299_, v___x_1323_);
                            leanh::lean_dec(v_i_1299_);
                            v_i_1299_ = v___x_1338_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_start_1305_ = leanh::lean_ctor_get(v_right_1298_, 1);
                v_stop_1306_ = leanh::lean_ctor_get(v_right_1298_, 2);
                v___x_1307_ = lean_nat_sub(v___x_1303_, v_i_1299_);
                leanh::lean_dec(v___x_1303_);
                leanh::lean_inc_ref(v_left_1297_);
                v___x_1308_ = l_Subarray_take___redArg(v_left_1297_, v___x_1307_);
                v___x_1309_ = lean_nat_sub(v_stop_1306_, v_start_1305_);
                v___x_1310_ = lean_nat_sub(v___x_1309_, v_i_1299_);
                leanh::lean_dec(v_i_1299_);
                leanh::lean_dec(v___x_1309_);
                v___x_1311_ = l_Subarray_take___redArg(v_right_1298_, v___x_1310_);
                leanh::lean_dec(v___x_1310_);
                v___x_1312_ = l_Subarray_drop___redArg(v_left_1297_, v___x_1307_);
                leanh::lean_dec(v___x_1307_);
                v___x_1313_ = l_Lean_Diff_matchPrefix___redArg___closed__0;
                v___x_1314_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_1302_,
                        v___x_1312_,
                        v___x_1313_,
                    );
                v___x_1315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1315_, 0, v___x_1311_);
                leanh::lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                v___x_1316_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1316_, 0, v___x_1308_);
                leanh::lean_ctor_set(v___x_1316_, 1, v___x_1315_);
                return v___x_1316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go(
    mut v_00_u03b1_1340_: *mut leanh::LeanObject,
    mut v_inst_1341_: *mut leanh::LeanObject,
    mut v_left_1342_: *mut leanh::LeanObject,
    mut v_right_1343_: *mut leanh::LeanObject,
    mut v_i_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(
        v_inst_1341_,
        v_left_1342_,
        v_right_1343_,
        v_i_1344_,
    );
    return v___x_1345_;
}
pub unsafe fn l_Lean_Diff_matchSuffix___redArg(
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_left_1347_: *mut leanh::LeanObject,
    mut v_right_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = leanh::lean_unsigned_to_nat(0);
    v___x_1350_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___redArg(
        v_inst_1346_,
        v_left_1347_,
        v_right_1348_,
        v___x_1349_,
    );
    return v___x_1350_;
}
pub unsafe fn l_Lean_Diff_matchSuffix(
    mut v_00_u03b1_1351_: *mut leanh::LeanObject,
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_left_1353_: *mut leanh::LeanObject,
    mut v_right_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Diff_matchSuffix___redArg(v_inst_1352_, v_left_1353_, v_right_1354_);
    return v___x_1355_;
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__0(
    mut v___x_1356_: *mut leanh::LeanObject,
    mut v_fst_1357_: *mut leanh::LeanObject,
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
    mut v_next_1360_: *mut leanh::LeanObject,
    mut v_acc_1361_: *mut leanh::LeanObject,
    mut v_h_1362_: *mut leanh::LeanObject,
    mut v_G_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1364_: u8 = 0;
    v___x_1364_ = lean_nat_dec_lt(v_next_1360_, v___x_1356_);
    if v___x_1364_ == 0 {
        leanh::lean_dec_ref(v_G_1363_);
        leanh::lean_dec(v_next_1360_);
        leanh::lean_dec_ref(v_inst_1359_);
        leanh::lean_dec_ref(v_inst_1358_);
        return v_acc_1361_;
    } else {
        let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1365_ = l_Subarray_get___redArg(v_fst_1357_, v_next_1360_);
        leanh::lean_inc(v_next_1360_);
        v___x_1366_ = l_Lean_Diff_Histogram_addLeft___redArg(
            v_inst_1358_,
            v_inst_1359_,
            v_acc_1361_,
            v_next_1360_,
            v___x_1365_,
        );
        v___x_1367_ = leanh::lean_unsigned_to_nat(1);
        v___x_1368_ = lean_nat_add(v_next_1360_, v___x_1367_);
        leanh::lean_dec(v_next_1360_);
        v___x_1369_ = leanh::lean_apply_4(
            v_G_1363_,
            v___x_1368_,
            v___x_1366_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1369_;
    }
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__0___boxed(
    mut v___x_1370_: *mut leanh::LeanObject,
    mut v_fst_1371_: *mut leanh::LeanObject,
    mut v_inst_1372_: *mut leanh::LeanObject,
    mut v_inst_1373_: *mut leanh::LeanObject,
    mut v_next_1374_: *mut leanh::LeanObject,
    mut v_acc_1375_: *mut leanh::LeanObject,
    mut v_h_1376_: *mut leanh::LeanObject,
    mut v_G_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1378_ = l_Lean_Diff_lcs___redArg___lam__0(
        v___x_1370_,
        v_fst_1371_,
        v_inst_1372_,
        v_inst_1373_,
        v_next_1374_,
        v_acc_1375_,
        v_h_1376_,
        v_G_1377_,
    );
    leanh::lean_dec_ref(v_fst_1371_);
    leanh::lean_dec(v___x_1370_);
    return v_res_1378_;
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__1(
    mut v___x_1379_: *mut leanh::LeanObject,
    mut v_fst_1380_: *mut leanh::LeanObject,
    mut v_inst_1381_: *mut leanh::LeanObject,
    mut v_inst_1382_: *mut leanh::LeanObject,
    mut v_next_1383_: *mut leanh::LeanObject,
    mut v_acc_1384_: *mut leanh::LeanObject,
    mut v_h_1385_: *mut leanh::LeanObject,
    mut v_G_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1387_: u8 = 0;
    v___x_1387_ = lean_nat_dec_lt(v_next_1383_, v___x_1379_);
    if v___x_1387_ == 0 {
        leanh::lean_dec_ref(v_G_1386_);
        leanh::lean_dec(v_next_1383_);
        leanh::lean_dec_ref(v_inst_1382_);
        leanh::lean_dec_ref(v_inst_1381_);
        return v_acc_1384_;
    } else {
        let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1388_ = l_Subarray_get___redArg(v_fst_1380_, v_next_1383_);
        leanh::lean_inc(v_next_1383_);
        v___x_1389_ = l_Lean_Diff_Histogram_addRight___redArg(
            v_inst_1381_,
            v_inst_1382_,
            v_acc_1384_,
            v_next_1383_,
            v___x_1388_,
        );
        v___x_1390_ = leanh::lean_unsigned_to_nat(1);
        v___x_1391_ = lean_nat_add(v_next_1383_, v___x_1390_);
        leanh::lean_dec(v_next_1383_);
        v___x_1392_ = leanh::lean_apply_4(
            v_G_1386_,
            v___x_1391_,
            v___x_1389_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1392_;
    }
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__1___boxed(
    mut v___x_1393_: *mut leanh::LeanObject,
    mut v_fst_1394_: *mut leanh::LeanObject,
    mut v_inst_1395_: *mut leanh::LeanObject,
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_next_1397_: *mut leanh::LeanObject,
    mut v_acc_1398_: *mut leanh::LeanObject,
    mut v_h_1399_: *mut leanh::LeanObject,
    mut v_G_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_Diff_lcs___redArg___lam__1(
        v___x_1393_,
        v_fst_1394_,
        v_inst_1395_,
        v_inst_1396_,
        v_next_1397_,
        v_acc_1398_,
        v_h_1399_,
        v_G_1400_,
    );
    leanh::lean_dec_ref(v_fst_1394_);
    leanh::lean_dec(v___x_1393_);
    return v_res_1401_;
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__2(
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_x_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leftIndex_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightIndex_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_leftCount_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v_val_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v_leftCount_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rightCount_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v_val_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1475_: u8 = 0;
    let mut v_unused_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_unused_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut v_unused_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_unused_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1405_ = leanh::lean_ctor_get(v_a_1402_, 1);
                leanh::lean_inc(v_snd_1405_);
                v_leftIndex_1406_ = leanh::lean_ctor_get(v_snd_1405_, 1);
                leanh::lean_inc(v_leftIndex_1406_);
                if leanh::lean_obj_tag(v_leftIndex_1406_) == 1 {
                    v_rightIndex_1407_ = leanh::lean_ctor_get(v_snd_1405_, 3);
                    leanh::lean_inc(v_rightIndex_1407_);
                    if leanh::lean_obj_tag(v_rightIndex_1407_) == 1 {
                        if leanh::lean_obj_tag(v___y_1404_) == 0 {
                            v_fst_1408_ = leanh::lean_ctor_get(v_a_1402_, 0);
                            v_isSharedCheck_1436_ =
                                (!leanh::lean_is_exclusive(v_a_1402_)) as u8;
                            if v_isSharedCheck_1436_ == 0 {
                                v_unused_1437_ = leanh::lean_ctor_get(v_a_1402_, 1);
                                leanh::lean_dec(v_unused_1437_);
                                v___x_1410_ = v_a_1402_;
                                v_isShared_1411_ = v_isSharedCheck_1436_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_1408_);
                                leanh::lean_dec(v_a_1402_);
                                v___x_1410_ = leanh::lean_box(0);
                                v_isShared_1411_ = v_isSharedCheck_1436_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_val_1438_ = leanh::lean_ctor_get(v___y_1404_, 0);
                            leanh::lean_inc(v_val_1438_);
                            v_fst_1439_ = leanh::lean_ctor_get(v_a_1402_, 0);
                            v_isSharedCheck_1480_ =
                                (!leanh::lean_is_exclusive(v_a_1402_)) as u8;
                            if v_isSharedCheck_1480_ == 0 {
                                v_unused_1481_ = leanh::lean_ctor_get(v_a_1402_, 1);
                                leanh::lean_dec(v_unused_1481_);
                                v___x_1441_ = v_a_1402_;
                                v_isShared_1442_ = v_isSharedCheck_1480_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_1439_);
                                leanh::lean_dec(v_a_1402_);
                                v___x_1441_ = leanh::lean_box(0);
                                v_isShared_1442_ = v_isSharedCheck_1480_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_rightIndex_1407_);
                        leanh::lean_dec(v_snd_1405_);
                        leanh::lean_dec_ref(v_a_1402_);
                        v_isSharedCheck_1488_ =
                            (!leanh::lean_is_exclusive(v_leftIndex_1406_)) as u8;
                        if v_isSharedCheck_1488_ == 0 {
                            v_unused_1489_ = leanh::lean_ctor_get(v_leftIndex_1406_, 0);
                            leanh::lean_dec(v_unused_1489_);
                            v___x_1483_ = v_leftIndex_1406_;
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_dec(v_leftIndex_1406_);
                            v___x_1483_ = leanh::lean_box(0);
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_leftIndex_1406_);
                    leanh::lean_dec(v_snd_1405_);
                    leanh::lean_dec_ref(v_a_1402_);
                    v___x_1490_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1490_, 0, v___y_1404_);
                    return v___x_1490_;
                }
            }
            1 => {
                v_leftCount_1412_ = leanh::lean_ctor_get(v_snd_1405_, 0);
                leanh::lean_inc(v_leftCount_1412_);
                v_rightCount_1413_ = leanh::lean_ctor_get(v_snd_1405_, 2);
                leanh::lean_inc(v_rightCount_1413_);
                leanh::lean_dec(v_snd_1405_);
                v_val_1414_ = leanh::lean_ctor_get(v_leftIndex_1406_, 0);
                v_isSharedCheck_1435_ = (!leanh::lean_is_exclusive(v_leftIndex_1406_)) as u8;
                if v_isSharedCheck_1435_ == 0 {
                    v___x_1416_ = v_leftIndex_1406_;
                    v_isShared_1417_ = v_isSharedCheck_1435_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1414_);
                    leanh::lean_dec(v_leftIndex_1406_);
                    v___x_1416_ = leanh::lean_box(0);
                    v_isShared_1417_ = v_isSharedCheck_1435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1418_ = leanh::lean_ctor_get(v_rightIndex_1407_, 0);
                v_isSharedCheck_1434_ =
                    (!leanh::lean_is_exclusive(v_rightIndex_1407_)) as u8;
                if v_isSharedCheck_1434_ == 0 {
                    v___x_1420_ = v_rightIndex_1407_;
                    v_isShared_1421_ = v_isSharedCheck_1434_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1418_);
                    leanh::lean_dec(v_rightIndex_1407_);
                    v___x_1420_ = leanh::lean_box(0);
                    v_isShared_1421_ = v_isSharedCheck_1434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1422_ = lean_nat_add(v_leftCount_1412_, v_rightCount_1413_);
                leanh::lean_dec(v_rightCount_1413_);
                leanh::lean_dec(v_leftCount_1412_);
                if v_isShared_1411_ == 0 {
                    leanh::lean_ctor_set(v___x_1410_, 1, v_val_1418_);
                    leanh::lean_ctor_set(v___x_1410_, 0, v_val_1414_);
                    v___x_1424_ = v___x_1410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_val_1414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_val_1418_);
                    v___x_1424_ = v_reuseFailAlloc_1433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1425_, 0, v_fst_1408_);
                leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
                v___x_1426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1426_, 0, v___x_1422_);
                leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
                if v_isShared_1421_ == 0 {
                    leanh::lean_ctor_set(v___x_1420_, 0, v___x_1426_);
                    v___x_1428_ = v___x_1420_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1426_);
                    v___x_1428_ = v_reuseFailAlloc_1432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1417_ == 0 {
                    leanh::lean_ctor_set(v___x_1416_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1430_;
            }
            7 => {
                v_leftCount_1443_ = leanh::lean_ctor_get(v_snd_1405_, 0);
                leanh::lean_inc(v_leftCount_1443_);
                v_rightCount_1444_ = leanh::lean_ctor_get(v_snd_1405_, 2);
                leanh::lean_inc(v_rightCount_1444_);
                leanh::lean_dec(v_snd_1405_);
                v_val_1445_ = leanh::lean_ctor_get(v_leftIndex_1406_, 0);
                v_isSharedCheck_1479_ = (!leanh::lean_is_exclusive(v_leftIndex_1406_)) as u8;
                if v_isSharedCheck_1479_ == 0 {
                    v___x_1447_ = v_leftIndex_1406_;
                    v_isShared_1448_ = v_isSharedCheck_1479_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1445_);
                    leanh::lean_dec(v_leftIndex_1406_);
                    v___x_1447_ = leanh::lean_box(0);
                    v_isShared_1448_ = v_isSharedCheck_1479_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_val_1449_ = leanh::lean_ctor_get(v_rightIndex_1407_, 0);
                leanh::lean_inc(v_val_1449_);
                leanh::lean_dec_ref_known(v_rightIndex_1407_, 1);
                v_fst_1450_ = leanh::lean_ctor_get(v_val_1438_, 0);
                v_isSharedCheck_1477_ = (!leanh::lean_is_exclusive(v_val_1438_)) as u8;
                if v_isSharedCheck_1477_ == 0 {
                    v_unused_1478_ = leanh::lean_ctor_get(v_val_1438_, 1);
                    leanh::lean_dec(v_unused_1478_);
                    v___x_1452_ = v_val_1438_;
                    v_isShared_1453_ = v_isSharedCheck_1477_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1450_);
                    leanh::lean_dec(v_val_1438_);
                    v___x_1452_ = leanh::lean_box(0);
                    v_isShared_1453_ = v_isSharedCheck_1477_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1454_ = lean_nat_add(v_leftCount_1443_, v_rightCount_1444_);
                leanh::lean_dec(v_rightCount_1444_);
                leanh::lean_dec(v_leftCount_1443_);
                v___x_1455_ = lean_nat_dec_lt(v___x_1454_, v_fst_1450_);
                leanh::lean_dec(v_fst_1450_);
                if v___x_1455_ == 0 {
                    leanh::lean_dec(v___x_1454_);
                    leanh::lean_del_object(v___x_1452_);
                    leanh::lean_dec(v_val_1449_);
                    leanh::lean_dec(v_val_1445_);
                    leanh::lean_del_object(v___x_1441_);
                    leanh::lean_dec(v_fst_1439_);
                    if v_isShared_1448_ == 0 {
                        leanh::lean_ctor_set(v___x_1447_, 0, v___y_1404_);
                        v___x_1457_ = v___x_1447_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___y_1404_);
                        v___x_1457_ = v_reuseFailAlloc_1458_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1475_ = (!leanh::lean_is_exclusive(v___y_1404_)) as u8;
                    if v_isSharedCheck_1475_ == 0 {
                        v_unused_1476_ = leanh::lean_ctor_get(v___y_1404_, 0);
                        leanh::lean_dec(v_unused_1476_);
                        v___x_1460_ = v___y_1404_;
                        v_isShared_1461_ = v_isSharedCheck_1475_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1404_);
                        v___x_1460_ = leanh::lean_box(0);
                        v_isShared_1461_ = v_isSharedCheck_1475_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1457_;
            }
            11 => {
                if v_isShared_1453_ == 0 {
                    leanh::lean_ctor_set(v___x_1452_, 1, v_val_1449_);
                    leanh::lean_ctor_set(v___x_1452_, 0, v_val_1445_);
                    v___x_1463_ = v___x_1452_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_val_1445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_val_1449_);
                    v___x_1463_ = v_reuseFailAlloc_1474_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1442_ == 0 {
                    leanh::lean_ctor_set(v___x_1441_, 1, v___x_1463_);
                    v___x_1465_ = v___x_1441_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1473_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_fst_1439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1463_);
                    v___x_1465_ = v_reuseFailAlloc_1473_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1466_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1466_, 0, v___x_1454_);
                leanh::lean_ctor_set(v___x_1466_, 1, v___x_1465_);
                if v_isShared_1461_ == 0 {
                    leanh::lean_ctor_set(v___x_1460_, 0, v___x_1466_);
                    v___x_1468_ = v___x_1460_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1466_);
                    v___x_1468_ = v_reuseFailAlloc_1472_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1448_ == 0 {
                    leanh::lean_ctor_set(v___x_1447_, 0, v___x_1468_);
                    v___x_1470_ = v___x_1447_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
                    v___x_1470_ = v_reuseFailAlloc_1471_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1470_;
            }
            16 => {
                if v_isShared_1484_ == 0 {
                    leanh::lean_ctor_set(v___x_1483_, 0, v___y_1404_);
                    v___x_1486_ = v___x_1483_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___y_1404_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__3(
    mut v_a_1491_: *mut leanh::LeanObject,
    mut v_b_1492_: *mut leanh::LeanObject,
    mut v_d_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1494_, 0, v_a_1491_);
    leanh::lean_ctor_set(v___x_1494_, 1, v_b_1492_);
    v___x_1495_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    leanh::lean_ctor_set(v___x_1495_, 1, v_d_1493_);
    return v___x_1495_;
}
pub unsafe fn l_Lean_Diff_lcs___redArg___lam__4(
    mut v___x_1496_: *mut leanh::LeanObject,
    mut v___f_1497_: *mut leanh::LeanObject,
    mut v_l_1498_: *mut leanh::LeanObject,
    mut v_acc_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(
        v___x_1496_,
        v___f_1497_,
        v_acc_1499_,
        v_l_1498_,
    );
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___redArg___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = leanh::lean_box(0);
    v___x_1521_ = leanh::lean_unsigned_to_nat(16);
    v___x_1522_ = lean_mk_array(v___x_1521_, v___x_1520_);
    return v___x_1522_;
}
pub unsafe fn _init_l_Lean_Diff_lcs___redArg___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Diff_lcs___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Diff_lcs___redArg___closed__10_once),
        _init_l_Lean_Diff_lcs___redArg___closed__10,
    );
    v___x_1524_ = leanh::lean_unsigned_to_nat(0);
    v_hist_1525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_hist_1525_, 0, v___x_1524_);
    leanh::lean_ctor_set(v_hist_1525_, 1, v___x_1523_);
    return v_hist_1525_;
}
pub unsafe fn l_Lean_Diff_lcs___redArg(
    mut v_inst_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_left_1533_: *mut leanh::LeanObject,
    mut v_right_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hist_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: u8 = 0;
    let mut v___f_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: usize = 0;
    let mut v___x_1593_: usize = 0;
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1535_ = l_Lean_Diff_lcs___redArg___closed__9;
                leanh::lean_inc_ref_n(v_inst_1531_, 4);
                v___x_1536_ =
                    l_Lean_Diff_matchPrefix___redArg(v_inst_1531_, v_left_1533_, v_right_1534_);
                v_snd_1537_ = leanh::lean_ctor_get(v___x_1536_, 1);
                leanh::lean_inc(v_snd_1537_);
                v_fst_1538_ = leanh::lean_ctor_get(v___x_1536_, 0);
                leanh::lean_inc(v_fst_1538_);
                leanh::lean_dec_ref(v___x_1536_);
                v_fst_1539_ = leanh::lean_ctor_get(v_snd_1537_, 0);
                leanh::lean_inc(v_fst_1539_);
                v_snd_1540_ = leanh::lean_ctor_get(v_snd_1537_, 1);
                leanh::lean_inc(v_snd_1540_);
                leanh::lean_dec(v_snd_1537_);
                v___x_1541_ =
                    l_Lean_Diff_matchSuffix___redArg(v_inst_1531_, v_fst_1539_, v_snd_1540_);
                v_snd_1542_ = leanh::lean_ctor_get(v___x_1541_, 1);
                leanh::lean_inc(v_snd_1542_);
                v_fst_1543_ = leanh::lean_ctor_get(v___x_1541_, 0);
                leanh::lean_inc_n(v_fst_1543_, 2);
                leanh::lean_dec_ref(v___x_1541_);
                v_fst_1544_ = leanh::lean_ctor_get(v_snd_1542_, 0);
                leanh::lean_inc_n(v_fst_1544_, 2);
                v_snd_1545_ = leanh::lean_ctor_get(v_snd_1542_, 1);
                leanh::lean_inc(v_snd_1545_);
                leanh::lean_dec(v_snd_1542_);
                v_start_1546_ = leanh::lean_ctor_get(v_fst_1543_, 1);
                v_stop_1547_ = leanh::lean_ctor_get(v_fst_1543_, 2);
                v_start_1548_ = leanh::lean_ctor_get(v_fst_1544_, 1);
                v_stop_1549_ = leanh::lean_ctor_get(v_fst_1544_, 2);
                v___x_1550_ = leanh::lean_unsigned_to_nat(0);
                v_hist_1551_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Diff_lcs___redArg___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Diff_lcs___redArg___closed__11_once),
                    _init_l_Lean_Diff_lcs___redArg___closed__11,
                );
                v___x_1552_ = lean_nat_sub(v_stop_1547_, v_start_1546_);
                leanh::lean_inc_ref_n(v_inst_1532_, 2);
                v___f_1553_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_lcs___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    8,
                    4,
                );
                leanh::lean_closure_set(v___f_1553_, 0, v___x_1552_);
                leanh::lean_closure_set(v___f_1553_, 1, v_fst_1543_);
                leanh::lean_closure_set(v___f_1553_, 2, v_inst_1531_);
                leanh::lean_closure_set(v___f_1553_, 3, v_inst_1532_);
                v___x_1554_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1553_,
                    v___x_1550_,
                    v_hist_1551_,
                    leanh::lean_box(0),
                );
                v___x_1555_ = lean_nat_sub(v_stop_1549_, v_start_1548_);
                v___f_1556_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_lcs___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    8,
                    4,
                );
                leanh::lean_closure_set(v___f_1556_, 0, v___x_1555_);
                leanh::lean_closure_set(v___f_1556_, 1, v_fst_1544_);
                leanh::lean_closure_set(v___f_1556_, 2, v_inst_1531_);
                leanh::lean_closure_set(v___f_1556_, 3, v_inst_1532_);
                v___x_1557_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1556_,
                    v___x_1550_,
                    v___x_1554_,
                    leanh::lean_box(0),
                );
                v_buckets_1558_ = leanh::lean_ctor_get(v___x_1557_, 1);
                leanh::lean_inc_ref(v_buckets_1558_);
                leanh::lean_dec(v___x_1557_);
                v___f_1559_ = l_Lean_Diff_lcs___redArg___closed__12;
                v___x_1560_ = leanh::lean_box(0);
                v___x_1588_ = leanh::lean_box(0);
                v___x_1589_ = lean_array_get_size(v_buckets_1558_);
                v___x_1590_ = lean_nat_dec_lt(v___x_1550_, v___x_1589_);
                if v___x_1590_ == 0 {
                    leanh::lean_dec_ref(v_buckets_1558_);
                    v___y_1562_ = v___x_1588_;
                    state = 1;
                    continue;
                } else {
                    v___f_1591_ = l_Lean_Diff_lcs___redArg___closed__14;
                    v___x_1592_ = lean_usize_of_nat(v___x_1589_);
                    v___x_1593_ = 0usize;
                    v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1535_,
                        v___f_1591_,
                        v_buckets_1558_,
                        v___x_1592_,
                        v___x_1593_,
                        v___x_1588_,
                    );
                    v___y_1562_ = v___x_1594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1563_ = l_List_forIn_x27_loop___redArg(
                    v___x_1535_,
                    v___f_1559_,
                    v___y_1562_,
                    v___x_1560_,
                );
                leanh::lean_dec(v___y_1562_);
                if leanh::lean_obj_tag(v___x_1563_) == 1 {
                    v_val_1564_ = leanh::lean_ctor_get(v___x_1563_, 0);
                    leanh::lean_inc(v_val_1564_);
                    leanh::lean_dec_ref_known(v___x_1563_, 1);
                    v_snd_1565_ = leanh::lean_ctor_get(v_val_1564_, 1);
                    leanh::lean_inc(v_snd_1565_);
                    leanh::lean_dec(v_val_1564_);
                    v_snd_1566_ = leanh::lean_ctor_get(v_snd_1565_, 1);
                    leanh::lean_inc(v_snd_1566_);
                    v_fst_1567_ = leanh::lean_ctor_get(v_snd_1565_, 0);
                    leanh::lean_inc(v_fst_1567_);
                    leanh::lean_dec(v_snd_1565_);
                    v_fst_1568_ = leanh::lean_ctor_get(v_snd_1566_, 0);
                    leanh::lean_inc(v_fst_1568_);
                    v_snd_1569_ = leanh::lean_ctor_get(v_snd_1566_, 1);
                    leanh::lean_inc(v_snd_1569_);
                    leanh::lean_dec(v_snd_1566_);
                    v___x_1570_ = l_Subarray_split___redArg(v_fst_1543_, v_fst_1568_);
                    leanh::lean_dec(v_fst_1568_);
                    v_fst_1571_ = leanh::lean_ctor_get(v___x_1570_, 0);
                    leanh::lean_inc(v_fst_1571_);
                    v_snd_1572_ = leanh::lean_ctor_get(v___x_1570_, 1);
                    leanh::lean_inc(v_snd_1572_);
                    leanh::lean_dec_ref(v___x_1570_);
                    v___x_1573_ = l_Subarray_split___redArg(v_fst_1544_, v_snd_1569_);
                    leanh::lean_dec(v_snd_1569_);
                    v_fst_1574_ = leanh::lean_ctor_get(v___x_1573_, 0);
                    leanh::lean_inc(v_fst_1574_);
                    v_snd_1575_ = leanh::lean_ctor_get(v___x_1573_, 1);
                    leanh::lean_inc(v_snd_1575_);
                    leanh::lean_dec_ref(v___x_1573_);
                    leanh::lean_inc_ref(v_inst_1532_);
                    leanh::lean_inc_ref(v_inst_1531_);
                    v___x_1576_ = l_Lean_Diff_lcs___redArg(
                        v_inst_1531_,
                        v_inst_1532_,
                        v_fst_1571_,
                        v_fst_1574_,
                    );
                    v___x_1577_ = l_Array_append___redArg(v_fst_1538_, v___x_1576_);
                    leanh::lean_dec_ref(v___x_1576_);
                    v___x_1578_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1579_ = lean_mk_empty_array_with_capacity(v___x_1578_);
                    v___x_1580_ = lean_array_push(v___x_1579_, v_fst_1567_);
                    v___x_1581_ = l_Array_append___redArg(v___x_1577_, v___x_1580_);
                    leanh::lean_dec_ref(v___x_1580_);
                    v___x_1582_ = l_Subarray_drop___redArg(v_snd_1572_, v___x_1578_);
                    v___x_1583_ = l_Subarray_drop___redArg(v_snd_1575_, v___x_1578_);
                    v___x_1584_ = l_Lean_Diff_lcs___redArg(
                        v_inst_1531_,
                        v_inst_1532_,
                        v___x_1582_,
                        v___x_1583_,
                    );
                    v___x_1585_ = l_Array_append___redArg(v___x_1581_, v___x_1584_);
                    leanh::lean_dec_ref(v___x_1584_);
                    v___x_1586_ = l_Array_append___redArg(v___x_1585_, v_snd_1545_);
                    leanh::lean_dec(v_snd_1545_);
                    return v___x_1586_;
                } else {
                    leanh::lean_dec(v___x_1563_);
                    leanh::lean_dec(v_fst_1544_);
                    leanh::lean_dec(v_fst_1543_);
                    leanh::lean_dec_ref(v_inst_1532_);
                    leanh::lean_dec_ref(v_inst_1531_);
                    v___x_1587_ = l_Array_append___redArg(v_fst_1538_, v_snd_1545_);
                    leanh::lean_dec(v_snd_1545_);
                    return v___x_1587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_lcs(
    mut v_00_u03b1_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
    mut v_inst_1597_: *mut leanh::LeanObject,
    mut v_left_1598_: *mut leanh::LeanObject,
    mut v_right_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_Diff_lcs___redArg(v_inst_1596_, v_inst_1597_, v_left_1598_, v_right_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__0(
    mut v_x_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = 0;
    v___x_1603_ = leanh::lean_box((v___x_1602_) as usize);
    v___x_1604_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1604_, 0, v___x_1603_);
    leanh::lean_ctor_set(v___x_1604_, 1, v_x_1601_);
    return v___x_1604_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__1(
    mut v_x_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = 1;
    v___x_1607_ = leanh::lean_box((v___x_1606_) as usize);
    v___x_1608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1608_, 0, v___x_1607_);
    leanh::lean_ctor_set(v___x_1608_, 1, v_x_1605_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__2(
    mut v_inst_1609_: *mut leanh::LeanObject,
    mut v_original_1610_: *mut leanh::LeanObject,
    mut v___x_1611_: *mut leanh::LeanObject,
    mut v_inst_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
    mut v_b_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1626_: u8 = 0;
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    let mut v_isSharedCheck_1640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1615_ = leanh::lean_ctor_get(v_b_1614_, 0);
                v_snd_1616_ = leanh::lean_ctor_get(v_b_1614_, 1);
                v_isSharedCheck_1640_ = (!leanh::lean_is_exclusive(v_b_1614_)) as u8;
                if v_isSharedCheck_1640_ == 0 {
                    v___x_1618_ = v_b_1614_;
                    v_isShared_1619_ = v_isSharedCheck_1640_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1616_);
                    leanh::lean_inc(v_fst_1615_);
                    leanh::lean_dec(v_b_1614_);
                    v___x_1618_ = leanh::lean_box(0);
                    v_isShared_1619_ = v_isSharedCheck_1640_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1636_ = lean_nat_dec_lt(v_snd_1616_, v___x_1611_);
                if v___x_1636_ == 0 {
                    leanh::lean_dec(v_a_1613_);
                    leanh::lean_dec_ref(v_inst_1612_);
                    v___y_1626_ = v___x_1636_;
                    state = 4;
                    continue;
                } else {
                    v___x_1637_ =
                        lean_array_get_borrowed(v_inst_1609_, v_original_1610_, v_snd_1616_);
                    leanh::lean_inc(v___x_1637_);
                    v___x_1638_ = leanh::lean_apply_2(v_inst_1612_, v___x_1637_, v_a_1613_);
                    v___x_1639_ = (leanh::lean_unbox(v___x_1638_) as u8);
                    if v___x_1639_ == 0 {
                        v___y_1626_ = v___x_1636_;
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1619_ == 0 {
                    v___x_1622_ = v___x_1618_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_fst_1615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_snd_1616_);
                    v___x_1622_ = v_reuseFailAlloc_1624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1623_, 0, v___x_1622_);
                return v___x_1623_;
            }
            4 => {
                if v___y_1626_ == 0 {
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1618_);
                    v___x_1627_ = 1;
                    v___x_1628_ =
                        lean_array_get_borrowed(v_inst_1609_, v_original_1610_, v_snd_1616_);
                    v___x_1629_ = leanh::lean_box((v___x_1627_) as usize);
                    leanh::lean_inc(v___x_1628_);
                    v___x_1630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1630_, 0, v___x_1629_);
                    leanh::lean_ctor_set(v___x_1630_, 1, v___x_1628_);
                    v___x_1631_ = lean_array_push(v_fst_1615_, v___x_1630_);
                    v___x_1632_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1633_ = lean_nat_add(v_snd_1616_, v___x_1632_);
                    leanh::lean_dec(v_snd_1616_);
                    v___x_1634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1634_, 0, v___x_1631_);
                    leanh::lean_ctor_set(v___x_1634_, 1, v___x_1633_);
                    v___x_1635_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1635_, 0, v___x_1634_);
                    return v___x_1635_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__2___boxed(
    mut v_inst_1641_: *mut leanh::LeanObject,
    mut v_original_1642_: *mut leanh::LeanObject,
    mut v___x_1643_: *mut leanh::LeanObject,
    mut v_inst_1644_: *mut leanh::LeanObject,
    mut v_a_1645_: *mut leanh::LeanObject,
    mut v_b_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Lean_Diff_diff___redArg___lam__2(
        v_inst_1641_,
        v_original_1642_,
        v___x_1643_,
        v_inst_1644_,
        v_a_1645_,
        v_b_1646_,
    );
    leanh::lean_dec(v___x_1643_);
    leanh::lean_dec_ref(v_original_1642_);
    leanh::lean_dec(v_inst_1641_);
    return v_res_1647_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__3(
    mut v_inst_1648_: *mut leanh::LeanObject,
    mut v_edited_1649_: *mut leanh::LeanObject,
    mut v___x_1650_: *mut leanh::LeanObject,
    mut v_inst_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_b_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1654_ = leanh::lean_ctor_get(v_b_1653_, 0);
                v_snd_1655_ = leanh::lean_ctor_get(v_b_1653_, 1);
                v_isSharedCheck_1679_ = (!leanh::lean_is_exclusive(v_b_1653_)) as u8;
                if v_isSharedCheck_1679_ == 0 {
                    v___x_1657_ = v_b_1653_;
                    v_isShared_1658_ = v_isSharedCheck_1679_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1655_);
                    leanh::lean_inc(v_fst_1654_);
                    leanh::lean_dec(v_b_1653_);
                    v___x_1657_ = leanh::lean_box(0);
                    v_isShared_1658_ = v_isSharedCheck_1679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1675_ = lean_nat_dec_lt(v_snd_1655_, v___x_1650_);
                if v___x_1675_ == 0 {
                    leanh::lean_dec(v_a_1652_);
                    leanh::lean_dec_ref(v_inst_1651_);
                    v___y_1665_ = v___x_1675_;
                    state = 4;
                    continue;
                } else {
                    v___x_1676_ =
                        lean_array_get_borrowed(v_inst_1648_, v_edited_1649_, v_snd_1655_);
                    leanh::lean_inc(v___x_1676_);
                    v___x_1677_ = leanh::lean_apply_2(v_inst_1651_, v___x_1676_, v_a_1652_);
                    v___x_1678_ = (leanh::lean_unbox(v___x_1677_) as u8);
                    if v___x_1678_ == 0 {
                        v___y_1665_ = v___x_1675_;
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1658_ == 0 {
                    v___x_1661_ = v___x_1657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_fst_1654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_snd_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1663_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
                return v___x_1662_;
            }
            4 => {
                if v___y_1665_ == 0 {
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1657_);
                    v___x_1666_ = 0;
                    v___x_1667_ =
                        lean_array_get_borrowed(v_inst_1648_, v_edited_1649_, v_snd_1655_);
                    v___x_1668_ = leanh::lean_box((v___x_1666_) as usize);
                    leanh::lean_inc(v___x_1667_);
                    v___x_1669_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
                    leanh::lean_ctor_set(v___x_1669_, 1, v___x_1667_);
                    v___x_1670_ = lean_array_push(v_fst_1654_, v___x_1669_);
                    v___x_1671_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1672_ = lean_nat_add(v_snd_1655_, v___x_1671_);
                    leanh::lean_dec(v_snd_1655_);
                    v___x_1673_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1673_, 0, v___x_1670_);
                    leanh::lean_ctor_set(v___x_1673_, 1, v___x_1672_);
                    v___x_1674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1674_, 0, v___x_1673_);
                    return v___x_1674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__3___boxed(
    mut v_inst_1680_: *mut leanh::LeanObject,
    mut v_edited_1681_: *mut leanh::LeanObject,
    mut v___x_1682_: *mut leanh::LeanObject,
    mut v_inst_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_b_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Diff_diff___redArg___lam__3(
        v_inst_1680_,
        v_edited_1681_,
        v___x_1682_,
        v_inst_1683_,
        v_a_1684_,
        v_b_1685_,
    );
    leanh::lean_dec(v___x_1682_);
    leanh::lean_dec_ref(v_edited_1681_);
    leanh::lean_dec(v_inst_1680_);
    return v_res_1686_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__4(
    mut v_inst_1687_: *mut leanh::LeanObject,
    mut v_original_1688_: *mut leanh::LeanObject,
    mut v___x_1689_: *mut leanh::LeanObject,
    mut v_inst_1690_: *mut leanh::LeanObject,
    mut v___x_1691_: *mut leanh::LeanObject,
    mut v_edited_1692_: *mut leanh::LeanObject,
    mut v___x_1693_: *mut leanh::LeanObject,
    mut v_a_1694_: *mut leanh::LeanObject,
    mut v_x_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v_fst_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___f_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1715_: u8 = 0;
    let mut v___f_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1697_ = leanh::lean_ctor_get(v___y_1696_, 1);
                v_fst_1698_ = leanh::lean_ctor_get(v___y_1696_, 0);
                v_isSharedCheck_1744_ = (!leanh::lean_is_exclusive(v___y_1696_)) as u8;
                if v_isSharedCheck_1744_ == 0 {
                    v___x_1700_ = v___y_1696_;
                    v_isShared_1701_ = v_isSharedCheck_1744_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1697_);
                    leanh::lean_inc(v_fst_1698_);
                    leanh::lean_dec(v___y_1696_);
                    v___x_1700_ = leanh::lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1744_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1702_ = leanh::lean_ctor_get(v_snd_1697_, 0);
                v_snd_1703_ = leanh::lean_ctor_get(v_snd_1697_, 1);
                v_isSharedCheck_1743_ = (!leanh::lean_is_exclusive(v_snd_1697_)) as u8;
                if v_isSharedCheck_1743_ == 0 {
                    v___x_1705_ = v_snd_1697_;
                    v_isShared_1706_ = v_isSharedCheck_1743_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1703_);
                    leanh::lean_inc(v_fst_1702_);
                    leanh::lean_dec(v_snd_1697_);
                    v___x_1705_ = leanh::lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_a_1694_);
                leanh::lean_inc_ref(v_inst_1690_);
                leanh::lean_inc(v_inst_1687_);
                v___f_1707_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_diff___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___f_1707_, 0, v_inst_1687_);
                leanh::lean_closure_set(v___f_1707_, 1, v_original_1688_);
                leanh::lean_closure_set(v___f_1707_, 2, v___x_1689_);
                leanh::lean_closure_set(v___f_1707_, 3, v_inst_1690_);
                leanh::lean_closure_set(v___f_1707_, 4, v_a_1694_);
                if v_isShared_1706_ == 0 {
                    leanh::lean_ctor_set(v___x_1705_, 1, v_fst_1702_);
                    leanh::lean_ctor_set(v___x_1705_, 0, v_fst_1698_);
                    v___x_1709_ = v___x_1705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fst_1698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_fst_1702_);
                    v___x_1709_ = v_reuseFailAlloc_1742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_1691_);
                v___x_1710_ = l___private_Init_While_0__whileM_erased___redArg(
                    v___x_1691_,
                    v___f_1707_,
                    v___x_1709_,
                );
                v_fst_1711_ = leanh::lean_ctor_get(v___x_1710_, 0);
                v_snd_1712_ = leanh::lean_ctor_get(v___x_1710_, 1);
                v_isSharedCheck_1741_ = (!leanh::lean_is_exclusive(v___x_1710_)) as u8;
                if v_isSharedCheck_1741_ == 0 {
                    v___x_1714_ = v___x_1710_;
                    v_isShared_1715_ = v_isSharedCheck_1741_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1712_);
                    leanh::lean_inc(v_fst_1711_);
                    leanh::lean_dec(v___x_1710_);
                    v___x_1714_ = leanh::lean_box(0);
                    v_isShared_1715_ = v_isSharedCheck_1741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_a_1694_);
                v___f_1716_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_diff___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___f_1716_, 0, v_inst_1687_);
                leanh::lean_closure_set(v___f_1716_, 1, v_edited_1692_);
                leanh::lean_closure_set(v___f_1716_, 2, v___x_1693_);
                leanh::lean_closure_set(v___f_1716_, 3, v_inst_1690_);
                leanh::lean_closure_set(v___f_1716_, 4, v_a_1694_);
                if v_isShared_1715_ == 0 {
                    leanh::lean_ctor_set(v___x_1714_, 1, v_snd_1703_);
                    v___x_1718_ = v___x_1714_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_fst_1711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_snd_1703_);
                    v___x_1718_ = v_reuseFailAlloc_1740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1719_ = l___private_Init_While_0__whileM_erased___redArg(
                    v___x_1691_,
                    v___f_1716_,
                    v___x_1718_,
                );
                v_fst_1720_ = leanh::lean_ctor_get(v___x_1719_, 0);
                v_snd_1721_ = leanh::lean_ctor_get(v___x_1719_, 1);
                v_isSharedCheck_1739_ = (!leanh::lean_is_exclusive(v___x_1719_)) as u8;
                if v_isSharedCheck_1739_ == 0 {
                    v___x_1723_ = v___x_1719_;
                    v_isShared_1724_ = v_isSharedCheck_1739_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1721_);
                    leanh::lean_inc(v_fst_1720_);
                    leanh::lean_dec(v___x_1719_);
                    v___x_1723_ = leanh::lean_box(0);
                    v_isShared_1724_ = v_isSharedCheck_1739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1725_ = 2;
                v___x_1726_ = leanh::lean_box((v___x_1725_) as usize);
                if v_isShared_1724_ == 0 {
                    leanh::lean_ctor_set(v___x_1723_, 1, v_a_1694_);
                    leanh::lean_ctor_set(v___x_1723_, 0, v___x_1726_);
                    v___x_1728_ = v___x_1723_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_a_1694_);
                    v___x_1728_ = v_reuseFailAlloc_1738_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1729_ = lean_array_push(v_fst_1720_, v___x_1728_);
                v___x_1730_ = leanh::lean_unsigned_to_nat(1);
                v___x_1731_ = lean_nat_add(v_snd_1712_, v___x_1730_);
                leanh::lean_dec(v_snd_1712_);
                v___x_1732_ = lean_nat_add(v_snd_1721_, v___x_1730_);
                leanh::lean_dec(v_snd_1721_);
                if v_isShared_1701_ == 0 {
                    leanh::lean_ctor_set(v___x_1700_, 1, v___x_1732_);
                    leanh::lean_ctor_set(v___x_1700_, 0, v___x_1731_);
                    v___x_1734_ = v___x_1700_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1732_);
                    v___x_1734_ = v_reuseFailAlloc_1737_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1735_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1735_, 0, v___x_1729_);
                leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                v___x_1736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                return v___x_1736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__5(
    mut v___x_1745_: *mut leanh::LeanObject,
    mut v_original_1746_: *mut leanh::LeanObject,
    mut v_b_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1748_ = leanh::lean_ctor_get(v_b_1747_, 0);
                v_snd_1749_ = leanh::lean_ctor_get(v_b_1747_, 1);
                v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v_b_1747_)) as u8;
                if v_isSharedCheck_1769_ == 0 {
                    v___x_1751_ = v_b_1747_;
                    v_isShared_1752_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1749_);
                    leanh::lean_inc(v_fst_1748_);
                    leanh::lean_dec(v_b_1747_);
                    v___x_1751_ = leanh::lean_box(0);
                    v_isShared_1752_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1753_ = lean_nat_dec_lt(v_snd_1749_, v___x_1745_);
                if v___x_1753_ == 0 {
                    if v_isShared_1752_ == 0 {
                        v___x_1755_ = v___x_1751_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1757_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_fst_1748_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_snd_1749_);
                        v___x_1755_ = v_reuseFailAlloc_1757_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1758_ = 1;
                    v___x_1759_ = lean_array_fget_borrowed(v_original_1746_, v_snd_1749_);
                    v___x_1760_ = leanh::lean_box((v___x_1758_) as usize);
                    leanh::lean_inc(v___x_1759_);
                    if v_isShared_1752_ == 0 {
                        leanh::lean_ctor_set(v___x_1751_, 1, v___x_1759_);
                        leanh::lean_ctor_set(v___x_1751_, 0, v___x_1760_);
                        v___x_1762_ = v___x_1751_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1760_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1759_);
                        v___x_1762_ = v_reuseFailAlloc_1768_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
                return v___x_1756_;
            }
            3 => {
                v___x_1763_ = lean_array_push(v_fst_1748_, v___x_1762_);
                v___x_1764_ = leanh::lean_unsigned_to_nat(1);
                v___x_1765_ = lean_nat_add(v_snd_1749_, v___x_1764_);
                leanh::lean_dec(v_snd_1749_);
                v___x_1766_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1766_, 0, v___x_1763_);
                leanh::lean_ctor_set(v___x_1766_, 1, v___x_1765_);
                v___x_1767_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__5___boxed(
    mut v___x_1770_: *mut leanh::LeanObject,
    mut v_original_1771_: *mut leanh::LeanObject,
    mut v_b_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1773_ = l_Lean_Diff_diff___redArg___lam__5(v___x_1770_, v_original_1771_, v_b_1772_);
    leanh::lean_dec_ref(v_original_1771_);
    leanh::lean_dec(v___x_1770_);
    return v_res_1773_;
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__6(
    mut v___x_1774_: *mut leanh::LeanObject,
    mut v_edited_1775_: *mut leanh::LeanObject,
    mut v_b_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1777_ = leanh::lean_ctor_get(v_b_1776_, 0);
                v_snd_1778_ = leanh::lean_ctor_get(v_b_1776_, 1);
                v_isSharedCheck_1798_ = (!leanh::lean_is_exclusive(v_b_1776_)) as u8;
                if v_isSharedCheck_1798_ == 0 {
                    v___x_1780_ = v_b_1776_;
                    v_isShared_1781_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1778_);
                    leanh::lean_inc(v_fst_1777_);
                    leanh::lean_dec(v_b_1776_);
                    v___x_1780_ = leanh::lean_box(0);
                    v_isShared_1781_ = v_isSharedCheck_1798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1782_ = lean_nat_dec_lt(v_snd_1778_, v___x_1774_);
                if v___x_1782_ == 0 {
                    if v_isShared_1781_ == 0 {
                        v___x_1784_ = v___x_1780_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_fst_1777_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_snd_1778_);
                        v___x_1784_ = v_reuseFailAlloc_1786_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1787_ = 0;
                    v___x_1788_ = lean_array_fget_borrowed(v_edited_1775_, v_snd_1778_);
                    v___x_1789_ = leanh::lean_box((v___x_1787_) as usize);
                    leanh::lean_inc(v___x_1788_);
                    if v_isShared_1781_ == 0 {
                        leanh::lean_ctor_set(v___x_1780_, 1, v___x_1788_);
                        leanh::lean_ctor_set(v___x_1780_, 0, v___x_1789_);
                        v___x_1791_ = v___x_1780_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1789_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1788_);
                        v___x_1791_ = v_reuseFailAlloc_1797_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                return v___x_1785_;
            }
            3 => {
                v___x_1792_ = lean_array_push(v_fst_1777_, v___x_1791_);
                v___x_1793_ = leanh::lean_unsigned_to_nat(1);
                v___x_1794_ = lean_nat_add(v_snd_1778_, v___x_1793_);
                leanh::lean_dec(v_snd_1778_);
                v___x_1795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1795_, 0, v___x_1792_);
                leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                v___x_1796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1796_, 0, v___x_1795_);
                return v___x_1796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff___redArg___lam__6___boxed(
    mut v___x_1799_: *mut leanh::LeanObject,
    mut v_edited_1800_: *mut leanh::LeanObject,
    mut v_b_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Lean_Diff_diff___redArg___lam__6(v___x_1799_, v_edited_1800_, v_b_1801_);
    leanh::lean_dec_ref(v_edited_1800_);
    leanh::lean_dec(v___x_1799_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_Diff_diff___redArg(
    mut v_inst_1812_: *mut leanh::LeanObject,
    mut v_inst_1813_: *mut leanh::LeanObject,
    mut v_inst_1814_: *mut leanh::LeanObject,
    mut v_original_1815_: *mut leanh::LeanObject,
    mut v_edited_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___f_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1822_: usize = 0;
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___f_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1829_: usize = 0;
    let mut v___x_1830_: usize = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ds_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1838_: usize = 0;
    let mut v___x_1839_: usize = 0;
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1847_: u8 = 0;
    let mut v___f_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v___f_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_unused_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_i_1817_ = leanh::lean_unsigned_to_nat(0);
                v___x_1818_ = lean_array_get_size(v_original_1815_);
                v___x_1819_ = lean_nat_dec_lt(v_i_1817_, v___x_1818_);
                if v___x_1819_ == 0 {
                    leanh::lean_dec_ref(v_original_1815_);
                    leanh::lean_dec(v_inst_1814_);
                    leanh::lean_dec_ref(v_inst_1813_);
                    leanh::lean_dec_ref(v_inst_1812_);
                    v___f_1820_ = l_Lean_Diff_diff___redArg___closed__0;
                    v___x_1821_ = l_Lean_Diff_lcs___redArg___closed__9;
                    v_sz_1822_ = lean_array_size(v_edited_1816_);
                    v___x_1823_ = 0usize;
                    v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1821_,
                        v___f_1820_,
                        v_sz_1822_,
                        v___x_1823_,
                        v_edited_1816_,
                    );
                    return v___x_1824_;
                } else {
                    v___x_1825_ = lean_array_get_size(v_edited_1816_);
                    v___x_1826_ = lean_nat_dec_lt(v_i_1817_, v___x_1825_);
                    if v___x_1826_ == 0 {
                        leanh::lean_dec_ref(v_edited_1816_);
                        leanh::lean_dec(v_inst_1814_);
                        leanh::lean_dec_ref(v_inst_1813_);
                        leanh::lean_dec_ref(v_inst_1812_);
                        v___f_1827_ = l_Lean_Diff_diff___redArg___closed__1;
                        v___x_1828_ = l_Lean_Diff_lcs___redArg___closed__9;
                        v_sz_1829_ = lean_array_size(v_original_1815_);
                        v___x_1830_ = 0usize;
                        v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1828_,
                            v___f_1827_,
                            v_sz_1829_,
                            v___x_1830_,
                            v_original_1815_,
                        );
                        return v___x_1831_;
                    } else {
                        leanh::lean_inc_ref_n(v_original_1815_, 2);
                        v___x_1832_ =
                            l_Array_toSubarray___redArg(v_original_1815_, v_i_1817_, v___x_1818_);
                        leanh::lean_inc_ref_n(v_edited_1816_, 2);
                        v___x_1833_ =
                            l_Array_toSubarray___redArg(v_edited_1816_, v_i_1817_, v___x_1825_);
                        leanh::lean_inc_ref(v_inst_1812_);
                        v_ds_1834_ = l_Lean_Diff_lcs___redArg(
                            v_inst_1812_,
                            v_inst_1813_,
                            v___x_1832_,
                            v___x_1833_,
                        );
                        v___x_1835_ = l_Lean_Diff_lcs___redArg___closed__9;
                        v___f_1836_ = leanh::lean_alloc_closure(
                            l_Lean_Diff_diff___redArg___lam__4 as *mut core::ffi::c_void,
                            10,
                            7,
                        );
                        leanh::lean_closure_set(v___f_1836_, 0, v_inst_1814_);
                        leanh::lean_closure_set(v___f_1836_, 1, v_original_1815_);
                        leanh::lean_closure_set(v___f_1836_, 2, v___x_1818_);
                        leanh::lean_closure_set(v___f_1836_, 3, v_inst_1812_);
                        leanh::lean_closure_set(v___f_1836_, 4, v___x_1835_);
                        leanh::lean_closure_set(v___f_1836_, 5, v_edited_1816_);
                        leanh::lean_closure_set(v___f_1836_, 6, v___x_1825_);
                        v___x_1837_ = l_Lean_Diff_diff___redArg___closed__4;
                        v_sz_1838_ = lean_array_size(v_ds_1834_);
                        v___x_1839_ = 0usize;
                        v___x_1840_ =
                            l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1835_,
                                v_ds_1834_,
                                v___f_1836_,
                                v_sz_1838_,
                                v___x_1839_,
                                v___x_1837_,
                            );
                        v_snd_1841_ = leanh::lean_ctor_get(v___x_1840_, 1);
                        leanh::lean_inc(v_snd_1841_);
                        v_fst_1842_ = leanh::lean_ctor_get(v___x_1840_, 0);
                        leanh::lean_inc(v_fst_1842_);
                        leanh::lean_dec(v___x_1840_);
                        v_fst_1843_ = leanh::lean_ctor_get(v_snd_1841_, 0);
                        v_snd_1844_ = leanh::lean_ctor_get(v_snd_1841_, 1);
                        v_isSharedCheck_1865_ =
                            (!leanh::lean_is_exclusive(v_snd_1841_)) as u8;
                        if v_isSharedCheck_1865_ == 0 {
                            v___x_1846_ = v_snd_1841_;
                            v_isShared_1847_ = v_isSharedCheck_1865_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1844_);
                            leanh::lean_inc(v_fst_1843_);
                            leanh::lean_dec(v_snd_1841_);
                            v___x_1846_ = leanh::lean_box(0);
                            v_isShared_1847_ = v_isSharedCheck_1865_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___f_1848_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_diff___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1848_, 0, v___x_1818_);
                leanh::lean_closure_set(v___f_1848_, 1, v_original_1815_);
                if v_isShared_1847_ == 0 {
                    leanh::lean_ctor_set(v___x_1846_, 1, v_fst_1843_);
                    leanh::lean_ctor_set(v___x_1846_, 0, v_fst_1842_);
                    v___x_1850_ = v___x_1846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1864_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_fst_1842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_fst_1843_);
                    v___x_1850_ = v_reuseFailAlloc_1864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1851_ = l___private_Init_While_0__whileM_erased___redArg(
                    v___x_1835_,
                    v___f_1848_,
                    v___x_1850_,
                );
                v_fst_1852_ = leanh::lean_ctor_get(v___x_1851_, 0);
                v_isSharedCheck_1862_ = (!leanh::lean_is_exclusive(v___x_1851_)) as u8;
                if v_isSharedCheck_1862_ == 0 {
                    v_unused_1863_ = leanh::lean_ctor_get(v___x_1851_, 1);
                    leanh::lean_dec(v_unused_1863_);
                    v___x_1854_ = v___x_1851_;
                    v_isShared_1855_ = v_isSharedCheck_1862_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1852_);
                    leanh::lean_dec(v___x_1851_);
                    v___x_1854_ = leanh::lean_box(0);
                    v_isShared_1855_ = v_isSharedCheck_1862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___f_1856_ = leanh::lean_alloc_closure(
                    l_Lean_Diff_diff___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1856_, 0, v___x_1825_);
                leanh::lean_closure_set(v___f_1856_, 1, v_edited_1816_);
                if v_isShared_1855_ == 0 {
                    leanh::lean_ctor_set(v___x_1854_, 1, v_snd_1844_);
                    v___x_1858_ = v___x_1854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_fst_1852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_snd_1844_);
                    v___x_1858_ = v_reuseFailAlloc_1861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1859_ = l___private_Init_While_0__whileM_erased___redArg(
                    v___x_1835_,
                    v___f_1856_,
                    v___x_1858_,
                );
                v_fst_1860_ = leanh::lean_ctor_get(v___x_1859_, 0);
                leanh::lean_inc(v_fst_1860_);
                leanh::lean_dec(v___x_1859_);
                return v_fst_1860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Diff_diff(
    mut v_00_u03b1_1866_: *mut leanh::LeanObject,
    mut v_inst_1867_: *mut leanh::LeanObject,
    mut v_inst_1868_: *mut leanh::LeanObject,
    mut v_inst_1869_: *mut leanh::LeanObject,
    mut v_original_1870_: *mut leanh::LeanObject,
    mut v_edited_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = l_Lean_Diff_diff___redArg(
        v_inst_1867_,
        v_inst_1868_,
        v_inst_1869_,
        v_original_1870_,
        v_edited_1871_,
    );
    return v___x_1872_;
}
pub unsafe fn l_Lean_Diff_linesToString___redArg___lam__0(
    mut v_inst_1874_: *mut leanh::LeanObject,
    mut v_out_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_x_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    v_fst_1879_ = leanh::lean_ctor_get(v_a_1876_, 0);
    leanh::lean_inc(v_fst_1879_);
    v_snd_1880_ = leanh::lean_ctor_get(v_a_1876_, 1);
    leanh::lean_inc(v_snd_1880_);
    leanh::lean_dec_ref(v_a_1876_);
    v___x_1881_ = leanh::lean_apply_1(v_inst_1874_, v_snd_1880_);
    v___x_1882_ = lean_string_dec_eq(v___x_1881_, v_out_1875_);
    if v___x_1882_ == 0 {
        let mut v___x_1883_: u8 = 0;
        let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1883_ = (leanh::lean_unbox(v_fst_1879_) as u8);
        leanh::lean_dec(v_fst_1879_);
        v___x_1884_ = l_Lean_Diff_Action_linePrefix(v___x_1883_);
        v___x_1885_ = l_Lean_Diff_Action_linePrefix___closed__2;
        v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
        v___x_1887_ = lean_string_append(v___x_1886_, v___x_1881_);
        leanh::lean_dec_ref(v___x_1881_);
        v___x_1888_ = l_Lean_Diff_linesToString___redArg___lam__0___closed__0;
        v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
        v___x_1890_ = lean_string_append(v___y_1878_, v___x_1889_);
        leanh::lean_dec_ref(v___x_1889_);
        v___x_1891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1891_, 0, v___x_1890_);
        return v___x_1891_;
    } else {
        let mut v___x_1892_: u8 = 0;
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1881_);
        v___x_1892_ = (leanh::lean_unbox(v_fst_1879_) as u8);
        leanh::lean_dec(v_fst_1879_);
        v___x_1893_ = l_Lean_Diff_Action_linePrefix(v___x_1892_);
        v___x_1894_ = l_Lean_Diff_linesToString___redArg___lam__0___closed__0;
        v___x_1895_ = lean_string_append(v___x_1893_, v___x_1894_);
        v___x_1896_ = lean_string_append(v___y_1878_, v___x_1895_);
        leanh::lean_dec_ref(v___x_1895_);
        v___x_1897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
        return v___x_1897_;
    }
}
pub unsafe fn l_Lean_Diff_linesToString___redArg___lam__0___boxed(
    mut v_inst_1898_: *mut leanh::LeanObject,
    mut v_out_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_x_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lean_Diff_linesToString___redArg___lam__0(
        v_inst_1898_,
        v_out_1899_,
        v_a_1900_,
        v_x_1901_,
        v___y_1902_,
    );
    leanh::lean_dec_ref(v_out_1899_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_Diff_linesToString___redArg(
    mut v_inst_1905_: *mut leanh::LeanObject,
    mut v_lines_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1910_: usize = 0;
    let mut v___x_1911_: usize = 0;
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lean_Diff_lcs___redArg___closed__9;
    v_out_1908_ = l_Lean_Diff_linesToString___redArg___closed__0;
    v___f_1909_ = leanh::lean_alloc_closure(
        l_Lean_Diff_linesToString___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1909_, 0, v_inst_1905_);
    leanh::lean_closure_set(v___f_1909_, 1, v_out_1908_);
    v_sz_1910_ = lean_array_size(v_lines_1906_);
    v___x_1911_ = 0usize;
    v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1907_,
        v_lines_1906_,
        v___f_1909_,
        v_sz_1910_,
        v___x_1911_,
        v_out_1908_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Lean_Diff_linesToString(
    mut v_00_u03b1_1913_: *mut leanh::LeanObject,
    mut v_inst_1914_: *mut leanh::LeanObject,
    mut v_lines_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lean_Diff_linesToString___redArg(v_inst_1914_, v_lines_1915_);
    return v___x_1916_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Diff(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Diff_instInhabitedAction_default = _init_l_Lean_Diff_instInhabitedAction_default();
    l_Lean_Diff_instInhabitedAction = _init_l_Lean_Diff_instInhabitedAction();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Diff(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Diff(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Diff(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Diff(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Diff(builtin);
}