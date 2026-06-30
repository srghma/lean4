// Lean compiler output
// Module: Init.Data.Array.Subarray
// Imports: Init.Data.Array.Basic Init.Data.Slice.Operations
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Subarray_instSliceSizeSubarrayData___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Subarray_instSliceSizeSubarrayData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Subarray_instSliceSizeSubarrayData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_instSliceSizeSubarrayData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value:
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
    m_fun: l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_empty___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Subarray_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_empty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Subarray_empty___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Subarray_empty___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Subarray_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_empty___closed__1_value) as *mut leanh::LeanObject;
static mut l_Subarray_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Subarray_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Subarray_foldr___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_Subarray_foldr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [65, 114, 114, 97, 121, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__1_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 58, 95, 93, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__1_value)
        as *mut leanh::LeanObject;
static l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b___x3a___x5d___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__1_value)
                as *mut leanh::LeanObject,
            15207914032045756441 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__5_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__5_value)
                as *mut leanh::LeanObject,
            1581446985683836252 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__8_value: leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__11_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__11_value)
                as *mut leanh::LeanObject,
            1164644006045091397 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__13_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__13_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__14_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__16_value: leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__20_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__21_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__22_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__23_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__21_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__25_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__25_value)
        as *mut leanh::LeanObject;
pub static mut l_Array_term_____x5b___x3a___x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 58, 93, 0],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__0_value)
        as *mut leanh::LeanObject;
static l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b___x3a_x5d___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__0_value)
                as *mut leanh::LeanObject,
            14055661608840943147 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Array_term_____x5b___x3a_x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [116, 101, 114, 109, 95, 95, 91, 58, 95, 93, 0],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__0_value)
        as *mut leanh::LeanObject;
static l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b_x3a___x5d___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            8389090204557134608 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__6_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Array_term_____x5b_x3a___x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [65, 114, 114, 97, 121, 46, 116, 111, 83, 117, 98, 97, 114, 114, 97, 121, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 117, 98, 97, 114, 114, 97, 121, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value) as *mut leanh::LeanObject,4159008167141249932 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value) as *mut leanh::LeanObject,146480343229376155 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value) as *mut leanh::LeanObject,17404204824591055365 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value) as *mut leanh::LeanObject,8036185514257755965 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value) as *mut leanh::LeanObject,17116161260408496210 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value) as *mut leanh::LeanObject,13708106407786339395 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 46, 115, 105, 122, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 122, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value) as *mut leanh::LeanObject,2164234508552290018 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value) as *mut leanh::LeanObject;
pub unsafe fn l_Subarray_array___redArg(
    mut v_xs_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_array_1088_ = leanh::lean_ctor_get(v_xs_1087_, 0);
    leanh::lean_inc_ref(v_array_1088_);
    return v_array_1088_;
}
pub unsafe fn l_Subarray_array___redArg___boxed(
    mut v_xs_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Subarray_array___redArg(v_xs_1089_);
    leanh::lean_dec_ref(v_xs_1089_);
    return v_res_1090_;
}
pub unsafe fn l_Subarray_array(
    mut v_00_u03b1_1091_: *mut leanh::LeanObject,
    mut v_xs_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_array_1093_ = leanh::lean_ctor_get(v_xs_1092_, 0);
    leanh::lean_inc_ref(v_array_1093_);
    return v_array_1093_;
}
pub unsafe fn l_Subarray_array___boxed(
    mut v_00_u03b1_1094_: *mut leanh::LeanObject,
    mut v_xs_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Subarray_array(v_00_u03b1_1094_, v_xs_1095_);
    leanh::lean_dec_ref(v_xs_1095_);
    return v_res_1096_;
}
pub unsafe fn l_Subarray_start___redArg(
    mut v_xs_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_1098_ = leanh::lean_ctor_get(v_xs_1097_, 1);
    leanh::lean_inc(v_start_1098_);
    return v_start_1098_;
}
pub unsafe fn l_Subarray_start___redArg___boxed(
    mut v_xs_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1100_ = l_Subarray_start___redArg(v_xs_1099_);
    leanh::lean_dec_ref(v_xs_1099_);
    return v_res_1100_;
}
pub unsafe fn l_Subarray_start(
    mut v_00_u03b1_1101_: *mut leanh::LeanObject,
    mut v_xs_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_1103_ = leanh::lean_ctor_get(v_xs_1102_, 1);
    leanh::lean_inc(v_start_1103_);
    return v_start_1103_;
}
pub unsafe fn l_Subarray_start___boxed(
    mut v_00_u03b1_1104_: *mut leanh::LeanObject,
    mut v_xs_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Subarray_start(v_00_u03b1_1104_, v_xs_1105_);
    leanh::lean_dec_ref(v_xs_1105_);
    return v_res_1106_;
}
pub unsafe fn l_Subarray_stop___redArg(
    mut v_xs_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stop_1108_ = leanh::lean_ctor_get(v_xs_1107_, 2);
    leanh::lean_inc(v_stop_1108_);
    return v_stop_1108_;
}
pub unsafe fn l_Subarray_stop___redArg___boxed(
    mut v_xs_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Subarray_stop___redArg(v_xs_1109_);
    leanh::lean_dec_ref(v_xs_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Subarray_stop(
    mut v_00_u03b1_1111_: *mut leanh::LeanObject,
    mut v_xs_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stop_1113_ = leanh::lean_ctor_get(v_xs_1112_, 2);
    leanh::lean_inc(v_stop_1113_);
    return v_stop_1113_;
}
pub unsafe fn l_Subarray_stop___boxed(
    mut v_00_u03b1_1114_: *mut leanh::LeanObject,
    mut v_xs_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Subarray_stop(v_00_u03b1_1114_, v_xs_1115_);
    leanh::lean_dec_ref(v_xs_1115_);
    return v_res_1116_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData___lam__0(
    mut v_s_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_1118_ = leanh::lean_ctor_get(v_s_1117_, 1);
    v_stop_1119_ = leanh::lean_ctor_get(v_s_1117_, 2);
    v___x_1120_ = lean_nat_sub(v_stop_1119_, v_start_1118_);
    return v___x_1120_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData___lam__0___boxed(
    mut v_s_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Subarray_instSliceSizeSubarrayData___lam__0(v_s_1121_);
    leanh::lean_dec_ref(v_s_1121_);
    return v_res_1122_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData(
    mut v_00_u03b1_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1125_ = l_Subarray_instSliceSizeSubarrayData___closed__0;
    return v___f_1125_;
}
pub unsafe fn l_Subarray_get___redArg(
    mut v_s_1126_: *mut leanh::LeanObject,
    mut v_i_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_array_1128_ = leanh::lean_ctor_get(v_s_1126_, 0);
    v_start_1129_ = leanh::lean_ctor_get(v_s_1126_, 1);
    v___x_1130_ = lean_nat_add(v_start_1129_, v_i_1127_);
    v___x_1131_ = lean_array_fget_borrowed(v_array_1128_, v___x_1130_);
    leanh::lean_dec(v___x_1130_);
    leanh::lean_inc(v___x_1131_);
    return v___x_1131_;
}
pub unsafe fn l_Subarray_get___redArg___boxed(
    mut v_s_1132_: *mut leanh::LeanObject,
    mut v_i_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Subarray_get___redArg(v_s_1132_, v_i_1133_);
    leanh::lean_dec(v_i_1133_);
    leanh::lean_dec_ref(v_s_1132_);
    return v_res_1134_;
}
pub unsafe fn l_Subarray_get(
    mut v_00_u03b1_1135_: *mut leanh::LeanObject,
    mut v_s_1136_: *mut leanh::LeanObject,
    mut v_i_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = l_Subarray_get___redArg(v_s_1136_, v_i_1137_);
    return v___x_1138_;
}
pub unsafe fn l_Subarray_get___boxed(
    mut v_00_u03b1_1139_: *mut leanh::LeanObject,
    mut v_s_1140_: *mut leanh::LeanObject,
    mut v_i_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Subarray_get(v_00_u03b1_1139_, v_s_1140_, v_i_1141_);
    leanh::lean_dec(v_i_1141_);
    leanh::lean_dec_ref(v_s_1140_);
    return v_res_1142_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(
    mut v_xs_1143_: *mut leanh::LeanObject,
    mut v_i_1144_: *mut leanh::LeanObject,
    mut v_h_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Subarray_get___redArg(v_xs_1143_, v_i_1144_);
    return v___x_1146_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed(
    mut v_xs_1147_: *mut leanh::LeanObject,
    mut v_i_1148_: *mut leanh::LeanObject,
    mut v_h_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ =
        l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(v_xs_1147_, v_i_1148_, v_h_1149_);
    leanh::lean_dec(v_i_1148_);
    leanh::lean_dec_ref(v_xs_1147_);
    return v_res_1150_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData(
    mut v_00_u03b1_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1153_ = l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0;
    return v___f_1153_;
}
pub unsafe fn l_Subarray_getD___redArg(
    mut v_s_1154_: *mut leanh::LeanObject,
    mut v_i_1155_: *mut leanh::LeanObject,
    mut v_v_u2080_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    v_start_1157_ = leanh::lean_ctor_get(v_s_1154_, 1);
    v_stop_1158_ = leanh::lean_ctor_get(v_s_1154_, 2);
    v___x_1159_ = lean_nat_sub(v_stop_1158_, v_start_1157_);
    v___x_1160_ = lean_nat_dec_lt(v_i_1155_, v___x_1159_);
    leanh::lean_dec(v___x_1159_);
    if v___x_1160_ == 0 {
        leanh::lean_inc(v_v_u2080_1156_);
        return v_v_u2080_1156_;
    } else {
        let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1161_ = l_Subarray_get___redArg(v_s_1154_, v_i_1155_);
        return v___x_1161_;
    }
}
pub unsafe fn l_Subarray_getD___redArg___boxed(
    mut v_s_1162_: *mut leanh::LeanObject,
    mut v_i_1163_: *mut leanh::LeanObject,
    mut v_v_u2080_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Subarray_getD___redArg(v_s_1162_, v_i_1163_, v_v_u2080_1164_);
    leanh::lean_dec(v_v_u2080_1164_);
    leanh::lean_dec(v_i_1163_);
    leanh::lean_dec_ref(v_s_1162_);
    return v_res_1165_;
}
pub unsafe fn l_Subarray_getD(
    mut v_00_u03b1_1166_: *mut leanh::LeanObject,
    mut v_s_1167_: *mut leanh::LeanObject,
    mut v_i_1168_: *mut leanh::LeanObject,
    mut v_v_u2080_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: u8 = 0;
    v_start_1170_ = leanh::lean_ctor_get(v_s_1167_, 1);
    v_stop_1171_ = leanh::lean_ctor_get(v_s_1167_, 2);
    v___x_1172_ = lean_nat_sub(v_stop_1171_, v_start_1170_);
    v___x_1173_ = lean_nat_dec_lt(v_i_1168_, v___x_1172_);
    leanh::lean_dec(v___x_1172_);
    if v___x_1173_ == 0 {
        leanh::lean_inc(v_v_u2080_1169_);
        return v_v_u2080_1169_;
    } else {
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1174_ = l_Subarray_get___redArg(v_s_1167_, v_i_1168_);
        return v___x_1174_;
    }
}
pub unsafe fn l_Subarray_getD___boxed(
    mut v_00_u03b1_1175_: *mut leanh::LeanObject,
    mut v_s_1176_: *mut leanh::LeanObject,
    mut v_i_1177_: *mut leanh::LeanObject,
    mut v_v_u2080_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Subarray_getD(v_00_u03b1_1175_, v_s_1176_, v_i_1177_, v_v_u2080_1178_);
    leanh::lean_dec(v_v_u2080_1178_);
    leanh::lean_dec(v_i_1177_);
    leanh::lean_dec_ref(v_s_1176_);
    return v_res_1179_;
}
pub unsafe fn l_Subarray_get_x21___redArg(
    mut v_inst_1180_: *mut leanh::LeanObject,
    mut v_s_1181_: *mut leanh::LeanObject,
    mut v_i_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: u8 = 0;
    v_start_1183_ = leanh::lean_ctor_get(v_s_1181_, 1);
    v_stop_1184_ = leanh::lean_ctor_get(v_s_1181_, 2);
    v___x_1185_ = lean_nat_sub(v_stop_1184_, v_start_1183_);
    v___x_1186_ = lean_nat_dec_lt(v_i_1182_, v___x_1185_);
    leanh::lean_dec(v___x_1185_);
    if v___x_1186_ == 0 {
        leanh::lean_inc(v_inst_1180_);
        return v_inst_1180_;
    } else {
        let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1187_ = l_Subarray_get___redArg(v_s_1181_, v_i_1182_);
        return v___x_1187_;
    }
}
pub unsafe fn l_Subarray_get_x21___redArg___boxed(
    mut v_inst_1188_: *mut leanh::LeanObject,
    mut v_s_1189_: *mut leanh::LeanObject,
    mut v_i_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Subarray_get_x21___redArg(v_inst_1188_, v_s_1189_, v_i_1190_);
    leanh::lean_dec(v_i_1190_);
    leanh::lean_dec_ref(v_s_1189_);
    leanh::lean_dec(v_inst_1188_);
    return v_res_1191_;
}
pub unsafe fn l_Subarray_get_x21(
    mut v_00_u03b1_1192_: *mut leanh::LeanObject,
    mut v_inst_1193_: *mut leanh::LeanObject,
    mut v_s_1194_: *mut leanh::LeanObject,
    mut v_i_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    v_start_1196_ = leanh::lean_ctor_get(v_s_1194_, 1);
    v_stop_1197_ = leanh::lean_ctor_get(v_s_1194_, 2);
    v___x_1198_ = lean_nat_sub(v_stop_1197_, v_start_1196_);
    v___x_1199_ = lean_nat_dec_lt(v_i_1195_, v___x_1198_);
    leanh::lean_dec(v___x_1198_);
    if v___x_1199_ == 0 {
        leanh::lean_inc(v_inst_1193_);
        return v_inst_1193_;
    } else {
        let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1200_ = l_Subarray_get___redArg(v_s_1194_, v_i_1195_);
        return v___x_1200_;
    }
}
pub unsafe fn l_Subarray_get_x21___boxed(
    mut v_00_u03b1_1201_: *mut leanh::LeanObject,
    mut v_inst_1202_: *mut leanh::LeanObject,
    mut v_s_1203_: *mut leanh::LeanObject,
    mut v_i_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Subarray_get_x21(v_00_u03b1_1201_, v_inst_1202_, v_s_1203_, v_i_1204_);
    leanh::lean_dec(v_i_1204_);
    leanh::lean_dec_ref(v_s_1203_);
    leanh::lean_dec(v_inst_1202_);
    return v_res_1205_;
}
pub unsafe fn l_Subarray_popFront___redArg(
    mut v_s_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_unused_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1207_ = leanh::lean_ctor_get(v_s_1206_, 0);
                v_start_1208_ = leanh::lean_ctor_get(v_s_1206_, 1);
                v_stop_1209_ = leanh::lean_ctor_get(v_s_1206_, 2);
                v___x_1210_ = lean_nat_dec_lt(v_start_1208_, v_stop_1209_);
                if v___x_1210_ == 0 {
                    return v_s_1206_;
                } else {
                    leanh::lean_inc(v_stop_1209_);
                    leanh::lean_inc(v_start_1208_);
                    leanh::lean_inc_ref(v_array_1207_);
                    v_isSharedCheck_1219_ = (!leanh::lean_is_exclusive(v_s_1206_)) as u8;
                    if v_isSharedCheck_1219_ == 0 {
                        v_unused_1220_ = leanh::lean_ctor_get(v_s_1206_, 2);
                        leanh::lean_dec(v_unused_1220_);
                        v_unused_1221_ = leanh::lean_ctor_get(v_s_1206_, 1);
                        leanh::lean_dec(v_unused_1221_);
                        v_unused_1222_ = leanh::lean_ctor_get(v_s_1206_, 0);
                        leanh::lean_dec(v_unused_1222_);
                        v___x_1212_ = v_s_1206_;
                        v_isShared_1213_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_1206_);
                        v___x_1212_ = leanh::lean_box(0);
                        v_isShared_1213_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1214_ = leanh::lean_unsigned_to_nat(1);
                v___x_1215_ = lean_nat_add(v_start_1208_, v___x_1214_);
                leanh::lean_dec(v_start_1208_);
                if v_isShared_1213_ == 0 {
                    leanh::lean_ctor_set(v___x_1212_, 1, v___x_1215_);
                    v___x_1217_ = v___x_1212_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1218_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_array_1207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_stop_1209_);
                    v___x_1217_ = v_reuseFailAlloc_1218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_popFront(
    mut v_00_u03b1_1223_: *mut leanh::LeanObject,
    mut v_s_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = l_Subarray_popFront___redArg(v_s_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Subarray_empty(
    mut v_00_u03b1_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Subarray_empty___closed__1;
    return v___x_1232_;
}
pub unsafe fn _init_l_Subarray_instEmptyCollection___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Subarray_empty(leanh::lean_box(0));
    return v___x_1233_;
}
pub unsafe fn l_Subarray_instEmptyCollection(
    mut v_00_u03b1_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0_once),
        _init_l_Subarray_instEmptyCollection___closed__0,
    );
    return v___x_1235_;
}
pub unsafe fn l_Subarray_instInhabited(
    mut v_00_u03b1_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0_once),
        _init_l_Subarray_instEmptyCollection___closed__0,
    );
    return v___x_1237_;
}
pub unsafe fn l_Subarray_foldrM___redArg(
    mut v_inst_1238_: *mut leanh::LeanObject,
    mut v_f_1239_: *mut leanh::LeanObject,
    mut v_init_1240_: *mut leanh::LeanObject,
    mut v_as_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: u8 = 0;
    v_array_1242_ = leanh::lean_ctor_get(v_as_1241_, 0);
    leanh::lean_inc_ref(v_array_1242_);
    v_start_1243_ = leanh::lean_ctor_get(v_as_1241_, 1);
    leanh::lean_inc(v_start_1243_);
    v_stop_1244_ = leanh::lean_ctor_get(v_as_1241_, 2);
    leanh::lean_inc(v_stop_1244_);
    leanh::lean_dec_ref(v_as_1241_);
    v___x_1245_ = lean_array_get_size(v_array_1242_);
    v___x_1246_ = lean_nat_dec_le(v_stop_1244_, v___x_1245_);
    if v___x_1246_ == 0 {
        let mut v___x_1247_: u8 = 0;
        leanh::lean_dec(v_stop_1244_);
        v___x_1247_ = lean_nat_dec_lt(v_start_1243_, v___x_1245_);
        if v___x_1247_ == 0 {
            let mut v_toApplicative_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_start_1243_);
            leanh::lean_dec_ref(v_array_1242_);
            leanh::lean_dec(v_f_1239_);
            v_toApplicative_1248_ = leanh::lean_ctor_get(v_inst_1238_, 0);
            leanh::lean_inc_ref(v_toApplicative_1248_);
            leanh::lean_dec_ref(v_inst_1238_);
            v_toPure_1249_ = leanh::lean_ctor_get(v_toApplicative_1248_, 1);
            leanh::lean_inc(v_toPure_1249_);
            leanh::lean_dec_ref(v_toApplicative_1248_);
            v___x_1250_ =
                leanh::lean_apply_2(v_toPure_1249_, leanh::lean_box(0), v_init_1240_);
            return v___x_1250_;
        } else {
            let mut v___x_1251_: usize = 0;
            let mut v___x_1252_: usize = 0;
            let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1251_ = lean_usize_of_nat(v___x_1245_);
            v___x_1252_ = lean_usize_of_nat(v_start_1243_);
            leanh::lean_dec(v_start_1243_);
            v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1238_,
                v_f_1239_,
                v_array_1242_,
                v___x_1251_,
                v___x_1252_,
                v_init_1240_,
            );
            return v___x_1253_;
        }
    } else {
        let mut v___x_1254_: u8 = 0;
        v___x_1254_ = lean_nat_dec_lt(v_start_1243_, v_stop_1244_);
        if v___x_1254_ == 0 {
            let mut v_toApplicative_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_stop_1244_);
            leanh::lean_dec(v_start_1243_);
            leanh::lean_dec_ref(v_array_1242_);
            leanh::lean_dec(v_f_1239_);
            v_toApplicative_1255_ = leanh::lean_ctor_get(v_inst_1238_, 0);
            leanh::lean_inc_ref(v_toApplicative_1255_);
            leanh::lean_dec_ref(v_inst_1238_);
            v_toPure_1256_ = leanh::lean_ctor_get(v_toApplicative_1255_, 1);
            leanh::lean_inc(v_toPure_1256_);
            leanh::lean_dec_ref(v_toApplicative_1255_);
            v___x_1257_ =
                leanh::lean_apply_2(v_toPure_1256_, leanh::lean_box(0), v_init_1240_);
            return v___x_1257_;
        } else {
            let mut v___x_1258_: usize = 0;
            let mut v___x_1259_: usize = 0;
            let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1258_ = lean_usize_of_nat(v_stop_1244_);
            leanh::lean_dec(v_stop_1244_);
            v___x_1259_ = lean_usize_of_nat(v_start_1243_);
            leanh::lean_dec(v_start_1243_);
            v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1238_,
                v_f_1239_,
                v_array_1242_,
                v___x_1258_,
                v___x_1259_,
                v_init_1240_,
            );
            return v___x_1260_;
        }
    }
}
pub unsafe fn l_Subarray_foldrM(
    mut v_00_u03b1_1261_: *mut leanh::LeanObject,
    mut v_00_u03b2_1262_: *mut leanh::LeanObject,
    mut v_m_1263_: *mut leanh::LeanObject,
    mut v_inst_1264_: *mut leanh::LeanObject,
    mut v_f_1265_: *mut leanh::LeanObject,
    mut v_init_1266_: *mut leanh::LeanObject,
    mut v_as_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: u8 = 0;
    v_array_1268_ = leanh::lean_ctor_get(v_as_1267_, 0);
    leanh::lean_inc_ref(v_array_1268_);
    v_start_1269_ = leanh::lean_ctor_get(v_as_1267_, 1);
    leanh::lean_inc(v_start_1269_);
    v_stop_1270_ = leanh::lean_ctor_get(v_as_1267_, 2);
    leanh::lean_inc(v_stop_1270_);
    leanh::lean_dec_ref(v_as_1267_);
    v___x_1271_ = lean_array_get_size(v_array_1268_);
    v___x_1272_ = lean_nat_dec_le(v_stop_1270_, v___x_1271_);
    if v___x_1272_ == 0 {
        let mut v___x_1273_: u8 = 0;
        leanh::lean_dec(v_stop_1270_);
        v___x_1273_ = lean_nat_dec_lt(v_start_1269_, v___x_1271_);
        if v___x_1273_ == 0 {
            let mut v_toApplicative_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_start_1269_);
            leanh::lean_dec_ref(v_array_1268_);
            leanh::lean_dec(v_f_1265_);
            v_toApplicative_1274_ = leanh::lean_ctor_get(v_inst_1264_, 0);
            leanh::lean_inc_ref(v_toApplicative_1274_);
            leanh::lean_dec_ref(v_inst_1264_);
            v_toPure_1275_ = leanh::lean_ctor_get(v_toApplicative_1274_, 1);
            leanh::lean_inc(v_toPure_1275_);
            leanh::lean_dec_ref(v_toApplicative_1274_);
            v___x_1276_ =
                leanh::lean_apply_2(v_toPure_1275_, leanh::lean_box(0), v_init_1266_);
            return v___x_1276_;
        } else {
            let mut v___x_1277_: usize = 0;
            let mut v___x_1278_: usize = 0;
            let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1277_ = lean_usize_of_nat(v___x_1271_);
            v___x_1278_ = lean_usize_of_nat(v_start_1269_);
            leanh::lean_dec(v_start_1269_);
            v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1264_,
                v_f_1265_,
                v_array_1268_,
                v___x_1277_,
                v___x_1278_,
                v_init_1266_,
            );
            return v___x_1279_;
        }
    } else {
        let mut v___x_1280_: u8 = 0;
        v___x_1280_ = lean_nat_dec_lt(v_start_1269_, v_stop_1270_);
        if v___x_1280_ == 0 {
            let mut v_toApplicative_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_stop_1270_);
            leanh::lean_dec(v_start_1269_);
            leanh::lean_dec_ref(v_array_1268_);
            leanh::lean_dec(v_f_1265_);
            v_toApplicative_1281_ = leanh::lean_ctor_get(v_inst_1264_, 0);
            leanh::lean_inc_ref(v_toApplicative_1281_);
            leanh::lean_dec_ref(v_inst_1264_);
            v_toPure_1282_ = leanh::lean_ctor_get(v_toApplicative_1281_, 1);
            leanh::lean_inc(v_toPure_1282_);
            leanh::lean_dec_ref(v_toApplicative_1281_);
            v___x_1283_ =
                leanh::lean_apply_2(v_toPure_1282_, leanh::lean_box(0), v_init_1266_);
            return v___x_1283_;
        } else {
            let mut v___x_1284_: usize = 0;
            let mut v___x_1285_: usize = 0;
            let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1284_ = lean_usize_of_nat(v_stop_1270_);
            leanh::lean_dec(v_stop_1270_);
            v___x_1285_ = lean_usize_of_nat(v_start_1269_);
            leanh::lean_dec(v_start_1269_);
            v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1264_,
                v_f_1265_,
                v_array_1268_,
                v___x_1284_,
                v___x_1285_,
                v_init_1266_,
            );
            return v___x_1286_;
        }
    }
}
pub unsafe fn l_Subarray_anyM___redArg(
    mut v_inst_1287_: *mut leanh::LeanObject,
    mut v_p_1288_: *mut leanh::LeanObject,
    mut v_as_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v_toApplicative_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: usize = 0;
    let mut v___x_1301_: usize = 0;
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v_toApplicative_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1290_ = leanh::lean_ctor_get(v_as_1289_, 0);
                leanh::lean_inc_ref(v_array_1290_);
                v_start_1291_ = leanh::lean_ctor_get(v_as_1289_, 1);
                leanh::lean_inc(v_start_1291_);
                v_stop_1292_ = leanh::lean_ctor_get(v_as_1289_, 2);
                leanh::lean_inc(v_stop_1292_);
                leanh::lean_dec_ref(v_as_1289_);
                v___x_1303_ = lean_nat_dec_lt(v_start_1291_, v_stop_1292_);
                if v___x_1303_ == 0 {
                    leanh::lean_dec(v_stop_1292_);
                    leanh::lean_dec(v_start_1291_);
                    leanh::lean_dec_ref(v_array_1290_);
                    leanh::lean_dec(v_p_1288_);
                    v_toApplicative_1304_ = leanh::lean_ctor_get(v_inst_1287_, 0);
                    leanh::lean_inc_ref(v_toApplicative_1304_);
                    leanh::lean_dec_ref(v_inst_1287_);
                    v_toPure_1305_ = leanh::lean_ctor_get(v_toApplicative_1304_, 1);
                    leanh::lean_inc(v_toPure_1305_);
                    leanh::lean_dec_ref(v_toApplicative_1304_);
                    v___x_1306_ = leanh::lean_box((v___x_1303_) as usize);
                    v___x_1307_ = leanh::lean_apply_2(
                        v_toPure_1305_,
                        leanh::lean_box(0),
                        v___x_1306_,
                    );
                    return v___x_1307_;
                } else {
                    v___x_1308_ = lean_array_get_size(v_array_1290_);
                    v___x_1309_ = lean_nat_dec_le(v_stop_1292_, v___x_1308_);
                    if v___x_1309_ == 0 {
                        leanh::lean_dec(v_stop_1292_);
                        v___y_1294_ = v___x_1308_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1294_ = v_stop_1292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1295_ = lean_nat_dec_lt(v_start_1291_, v___y_1294_);
                if v___x_1295_ == 0 {
                    leanh::lean_dec(v___y_1294_);
                    leanh::lean_dec(v_start_1291_);
                    leanh::lean_dec_ref(v_array_1290_);
                    leanh::lean_dec(v_p_1288_);
                    v_toApplicative_1296_ = leanh::lean_ctor_get(v_inst_1287_, 0);
                    leanh::lean_inc_ref(v_toApplicative_1296_);
                    leanh::lean_dec_ref(v_inst_1287_);
                    v_toPure_1297_ = leanh::lean_ctor_get(v_toApplicative_1296_, 1);
                    leanh::lean_inc(v_toPure_1297_);
                    leanh::lean_dec_ref(v_toApplicative_1296_);
                    v___x_1298_ = leanh::lean_box((v___x_1295_) as usize);
                    v___x_1299_ = leanh::lean_apply_2(
                        v_toPure_1297_,
                        leanh::lean_box(0),
                        v___x_1298_,
                    );
                    return v___x_1299_;
                } else {
                    v___x_1300_ = lean_usize_of_nat(v_start_1291_);
                    leanh::lean_dec(v_start_1291_);
                    v___x_1301_ = lean_usize_of_nat(v___y_1294_);
                    leanh::lean_dec(v___y_1294_);
                    v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_1287_,
                        v_p_1288_,
                        v_array_1290_,
                        v___x_1300_,
                        v___x_1301_,
                    );
                    return v___x_1302_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_anyM(
    mut v_00_u03b1_1310_: *mut leanh::LeanObject,
    mut v_m_1311_: *mut leanh::LeanObject,
    mut v_inst_1312_: *mut leanh::LeanObject,
    mut v_p_1313_: *mut leanh::LeanObject,
    mut v_as_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v_toApplicative_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: usize = 0;
    let mut v___x_1326_: usize = 0;
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v_toApplicative_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1315_ = leanh::lean_ctor_get(v_as_1314_, 0);
                leanh::lean_inc_ref(v_array_1315_);
                v_start_1316_ = leanh::lean_ctor_get(v_as_1314_, 1);
                leanh::lean_inc(v_start_1316_);
                v_stop_1317_ = leanh::lean_ctor_get(v_as_1314_, 2);
                leanh::lean_inc(v_stop_1317_);
                leanh::lean_dec_ref(v_as_1314_);
                v___x_1328_ = lean_nat_dec_lt(v_start_1316_, v_stop_1317_);
                if v___x_1328_ == 0 {
                    leanh::lean_dec(v_stop_1317_);
                    leanh::lean_dec(v_start_1316_);
                    leanh::lean_dec_ref(v_array_1315_);
                    leanh::lean_dec(v_p_1313_);
                    v_toApplicative_1329_ = leanh::lean_ctor_get(v_inst_1312_, 0);
                    leanh::lean_inc_ref(v_toApplicative_1329_);
                    leanh::lean_dec_ref(v_inst_1312_);
                    v_toPure_1330_ = leanh::lean_ctor_get(v_toApplicative_1329_, 1);
                    leanh::lean_inc(v_toPure_1330_);
                    leanh::lean_dec_ref(v_toApplicative_1329_);
                    v___x_1331_ = leanh::lean_box((v___x_1328_) as usize);
                    v___x_1332_ = leanh::lean_apply_2(
                        v_toPure_1330_,
                        leanh::lean_box(0),
                        v___x_1331_,
                    );
                    return v___x_1332_;
                } else {
                    v___x_1333_ = lean_array_get_size(v_array_1315_);
                    v___x_1334_ = lean_nat_dec_le(v_stop_1317_, v___x_1333_);
                    if v___x_1334_ == 0 {
                        leanh::lean_dec(v_stop_1317_);
                        v___y_1319_ = v___x_1333_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1319_ = v_stop_1317_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1320_ = lean_nat_dec_lt(v_start_1316_, v___y_1319_);
                if v___x_1320_ == 0 {
                    leanh::lean_dec(v___y_1319_);
                    leanh::lean_dec(v_start_1316_);
                    leanh::lean_dec_ref(v_array_1315_);
                    leanh::lean_dec(v_p_1313_);
                    v_toApplicative_1321_ = leanh::lean_ctor_get(v_inst_1312_, 0);
                    leanh::lean_inc_ref(v_toApplicative_1321_);
                    leanh::lean_dec_ref(v_inst_1312_);
                    v_toPure_1322_ = leanh::lean_ctor_get(v_toApplicative_1321_, 1);
                    leanh::lean_inc(v_toPure_1322_);
                    leanh::lean_dec_ref(v_toApplicative_1321_);
                    v___x_1323_ = leanh::lean_box((v___x_1320_) as usize);
                    v___x_1324_ = leanh::lean_apply_2(
                        v_toPure_1322_,
                        leanh::lean_box(0),
                        v___x_1323_,
                    );
                    return v___x_1324_;
                } else {
                    v___x_1325_ = lean_usize_of_nat(v_start_1316_);
                    leanh::lean_dec(v_start_1316_);
                    v___x_1326_ = lean_usize_of_nat(v___y_1319_);
                    leanh::lean_dec(v___y_1319_);
                    v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_1312_,
                        v_p_1313_,
                        v_array_1315_,
                        v___x_1325_,
                        v___x_1326_,
                    );
                    return v___x_1327_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_allM___redArg___lam__0(
    mut v_toPure_1335_: *mut leanh::LeanObject,
    mut v_____do__lift_1336_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1336_ == 0 {
        let mut v___x_1337_: u8 = 0;
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1337_ = 1;
        v___x_1338_ = leanh::lean_box((v___x_1337_) as usize);
        v___x_1339_ =
            leanh::lean_apply_2(v_toPure_1335_, leanh::lean_box(0), v___x_1338_);
        return v___x_1339_;
    } else {
        let mut v___x_1340_: u8 = 0;
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1340_ = 0;
        v___x_1341_ = leanh::lean_box((v___x_1340_) as usize);
        v___x_1342_ =
            leanh::lean_apply_2(v_toPure_1335_, leanh::lean_box(0), v___x_1341_);
        return v___x_1342_;
    }
}
pub unsafe fn l_Subarray_allM___redArg___lam__0___boxed(
    mut v_toPure_1343_: *mut leanh::LeanObject,
    mut v_____do__lift_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_115__boxed_1345_: u8 = 0;
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_115__boxed_1345_ = (leanh::lean_unbox(v_____do__lift_1344_) as u8);
    v_res_1346_ =
        l_Subarray_allM___redArg___lam__0(v_toPure_1343_, v_____do__lift_115__boxed_1345_);
    return v_res_1346_;
}
pub unsafe fn l_Subarray_allM___redArg___lam__1(
    mut v_toPure_1347_: *mut leanh::LeanObject,
    mut v___x_1348_: u8,
    mut v_____do__lift_1349_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1349_ == 0 {
        let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1350_ = leanh::lean_box((v___x_1348_) as usize);
        v___x_1351_ =
            leanh::lean_apply_2(v_toPure_1347_, leanh::lean_box(0), v___x_1350_);
        return v___x_1351_;
    } else {
        let mut v___x_1352_: u8 = 0;
        let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1352_ = 0;
        v___x_1353_ = leanh::lean_box((v___x_1352_) as usize);
        v___x_1354_ =
            leanh::lean_apply_2(v_toPure_1347_, leanh::lean_box(0), v___x_1353_);
        return v___x_1354_;
    }
}
pub unsafe fn l_Subarray_allM___redArg___lam__1___boxed(
    mut v_toPure_1355_: *mut leanh::LeanObject,
    mut v___x_1356_: *mut leanh::LeanObject,
    mut v_____do__lift_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_130__boxed_1358_: u8 = 0;
    let mut v_____do__lift_131__boxed_1359_: u8 = 0;
    let mut v_res_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_130__boxed_1358_ = (leanh::lean_unbox(v___x_1356_) as u8);
    v_____do__lift_131__boxed_1359_ = (leanh::lean_unbox(v_____do__lift_1357_) as u8);
    v_res_1360_ = l_Subarray_allM___redArg___lam__1(
        v_toPure_1355_,
        v___x_130__boxed_1358_,
        v_____do__lift_131__boxed_1359_,
    );
    return v_res_1360_;
}
pub unsafe fn l_Subarray_allM___redArg___lam__2(
    mut v_p_1361_: *mut leanh::LeanObject,
    mut v_toBind_1362_: *mut leanh::LeanObject,
    mut v___f_1363_: *mut leanh::LeanObject,
    mut v_v_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = leanh::lean_apply_1(v_p_1361_, v_v_1364_);
    v___x_1366_ = leanh::lean_apply_4(
        v_toBind_1362_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1365_,
        v___f_1363_,
    );
    return v___x_1366_;
}
pub unsafe fn l_Subarray_allM___redArg(
    mut v_inst_1367_: *mut leanh::LeanObject,
    mut v_p_1368_: *mut leanh::LeanObject,
    mut v_as_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1370_ = leanh::lean_ctor_get(v_inst_1367_, 0);
                v_array_1371_ = leanh::lean_ctor_get(v_as_1369_, 0);
                leanh::lean_inc_ref(v_array_1371_);
                v_start_1372_ = leanh::lean_ctor_get(v_as_1369_, 1);
                leanh::lean_inc(v_start_1372_);
                v_stop_1373_ = leanh::lean_ctor_get(v_as_1369_, 2);
                leanh::lean_inc(v_stop_1373_);
                leanh::lean_dec_ref(v_as_1369_);
                v_toBind_1374_ = leanh::lean_ctor_get(v_inst_1367_, 1);
                leanh::lean_inc(v_toBind_1374_);
                v_toPure_1375_ = leanh::lean_ctor_get(v_toApplicative_1370_, 1);
                leanh::lean_inc(v_toPure_1375_);
                v___f_1376_ = leanh::lean_alloc_closure(
                    l_Subarray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1376_, 0, v_toPure_1375_);
                v___x_1377_ = lean_nat_dec_lt(v_start_1372_, v_stop_1373_);
                if v___x_1377_ == 0 {
                    leanh::lean_inc(v_toPure_1375_);
                    leanh::lean_dec(v_stop_1373_);
                    leanh::lean_dec(v_start_1372_);
                    leanh::lean_dec_ref(v_array_1371_);
                    leanh::lean_dec(v_p_1368_);
                    leanh::lean_dec_ref(v_inst_1367_);
                    v___x_1378_ = leanh::lean_box((v___x_1377_) as usize);
                    v___x_1379_ = leanh::lean_apply_2(
                        v_toPure_1375_,
                        leanh::lean_box(0),
                        v___x_1378_,
                    );
                    v___x_1380_ = leanh::lean_apply_4(
                        v_toBind_1374_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1379_,
                        v___f_1376_,
                    );
                    return v___x_1380_;
                } else {
                    v___x_1381_ = leanh::lean_box((v___x_1377_) as usize);
                    leanh::lean_inc(v_toPure_1375_);
                    v___f_1382_ = leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1382_, 0, v_toPure_1375_);
                    leanh::lean_closure_set(v___f_1382_, 1, v___x_1381_);
                    leanh::lean_inc(v_toBind_1374_);
                    v___f_1383_ = leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1383_, 0, v_p_1368_);
                    leanh::lean_closure_set(v___f_1383_, 1, v_toBind_1374_);
                    leanh::lean_closure_set(v___f_1383_, 2, v___f_1382_);
                    v___x_1394_ = lean_array_get_size(v_array_1371_);
                    v___x_1395_ = lean_nat_dec_le(v_stop_1373_, v___x_1394_);
                    if v___x_1395_ == 0 {
                        leanh::lean_dec(v_stop_1373_);
                        v___y_1385_ = v___x_1394_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1385_ = v_stop_1373_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1386_ = lean_nat_dec_lt(v_start_1372_, v___y_1385_);
                if v___x_1386_ == 0 {
                    leanh::lean_inc(v_toPure_1375_);
                    leanh::lean_dec(v___y_1385_);
                    leanh::lean_dec_ref(v___f_1383_);
                    leanh::lean_dec(v_start_1372_);
                    leanh::lean_dec_ref(v_array_1371_);
                    leanh::lean_dec_ref(v_inst_1367_);
                    v___x_1387_ = leanh::lean_box((v___x_1386_) as usize);
                    v___x_1388_ = leanh::lean_apply_2(
                        v_toPure_1375_,
                        leanh::lean_box(0),
                        v___x_1387_,
                    );
                    v___x_1389_ = leanh::lean_apply_4(
                        v_toBind_1374_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1388_,
                        v___f_1376_,
                    );
                    return v___x_1389_;
                } else {
                    v___x_1390_ = lean_usize_of_nat(v_start_1372_);
                    leanh::lean_dec(v_start_1372_);
                    v___x_1391_ = lean_usize_of_nat(v___y_1385_);
                    leanh::lean_dec(v___y_1385_);
                    v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_1367_,
                        v___f_1383_,
                        v_array_1371_,
                        v___x_1390_,
                        v___x_1391_,
                    );
                    v___x_1393_ = leanh::lean_apply_4(
                        v_toBind_1374_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1392_,
                        v___f_1376_,
                    );
                    return v___x_1393_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_allM(
    mut v_00_u03b1_1396_: *mut leanh::LeanObject,
    mut v_m_1397_: *mut leanh::LeanObject,
    mut v_inst_1398_: *mut leanh::LeanObject,
    mut v_p_1399_: *mut leanh::LeanObject,
    mut v_as_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: usize = 0;
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1401_ = leanh::lean_ctor_get(v_inst_1398_, 0);
                v_array_1402_ = leanh::lean_ctor_get(v_as_1400_, 0);
                leanh::lean_inc_ref(v_array_1402_);
                v_start_1403_ = leanh::lean_ctor_get(v_as_1400_, 1);
                leanh::lean_inc(v_start_1403_);
                v_stop_1404_ = leanh::lean_ctor_get(v_as_1400_, 2);
                leanh::lean_inc(v_stop_1404_);
                leanh::lean_dec_ref(v_as_1400_);
                v_toBind_1405_ = leanh::lean_ctor_get(v_inst_1398_, 1);
                leanh::lean_inc(v_toBind_1405_);
                v_toPure_1406_ = leanh::lean_ctor_get(v_toApplicative_1401_, 1);
                leanh::lean_inc(v_toPure_1406_);
                v___f_1407_ = leanh::lean_alloc_closure(
                    l_Subarray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1407_, 0, v_toPure_1406_);
                v___x_1408_ = lean_nat_dec_lt(v_start_1403_, v_stop_1404_);
                if v___x_1408_ == 0 {
                    leanh::lean_inc(v_toPure_1406_);
                    leanh::lean_dec(v_stop_1404_);
                    leanh::lean_dec(v_start_1403_);
                    leanh::lean_dec_ref(v_array_1402_);
                    leanh::lean_dec(v_p_1399_);
                    leanh::lean_dec_ref(v_inst_1398_);
                    v___x_1409_ = leanh::lean_box((v___x_1408_) as usize);
                    v___x_1410_ = leanh::lean_apply_2(
                        v_toPure_1406_,
                        leanh::lean_box(0),
                        v___x_1409_,
                    );
                    v___x_1411_ = leanh::lean_apply_4(
                        v_toBind_1405_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1410_,
                        v___f_1407_,
                    );
                    return v___x_1411_;
                } else {
                    v___x_1412_ = leanh::lean_box((v___x_1408_) as usize);
                    leanh::lean_inc(v_toPure_1406_);
                    v___f_1413_ = leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1413_, 0, v_toPure_1406_);
                    leanh::lean_closure_set(v___f_1413_, 1, v___x_1412_);
                    leanh::lean_inc(v_toBind_1405_);
                    v___f_1414_ = leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1414_, 0, v_p_1399_);
                    leanh::lean_closure_set(v___f_1414_, 1, v_toBind_1405_);
                    leanh::lean_closure_set(v___f_1414_, 2, v___f_1413_);
                    v___x_1425_ = lean_array_get_size(v_array_1402_);
                    v___x_1426_ = lean_nat_dec_le(v_stop_1404_, v___x_1425_);
                    if v___x_1426_ == 0 {
                        leanh::lean_dec(v_stop_1404_);
                        v___y_1416_ = v___x_1425_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1416_ = v_stop_1404_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1417_ = lean_nat_dec_lt(v_start_1403_, v___y_1416_);
                if v___x_1417_ == 0 {
                    leanh::lean_inc(v_toPure_1406_);
                    leanh::lean_dec(v___y_1416_);
                    leanh::lean_dec_ref(v___f_1414_);
                    leanh::lean_dec(v_start_1403_);
                    leanh::lean_dec_ref(v_array_1402_);
                    leanh::lean_dec_ref(v_inst_1398_);
                    v___x_1418_ = leanh::lean_box((v___x_1417_) as usize);
                    v___x_1419_ = leanh::lean_apply_2(
                        v_toPure_1406_,
                        leanh::lean_box(0),
                        v___x_1418_,
                    );
                    v___x_1420_ = leanh::lean_apply_4(
                        v_toBind_1405_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1419_,
                        v___f_1407_,
                    );
                    return v___x_1420_;
                } else {
                    v___x_1421_ = lean_usize_of_nat(v_start_1403_);
                    leanh::lean_dec(v_start_1403_);
                    v___x_1422_ = lean_usize_of_nat(v___y_1416_);
                    leanh::lean_dec(v___y_1416_);
                    v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_1398_,
                        v___f_1414_,
                        v_array_1402_,
                        v___x_1421_,
                        v___x_1422_,
                    );
                    v___x_1424_ = leanh::lean_apply_4(
                        v_toBind_1405_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1423_,
                        v___f_1407_,
                    );
                    return v___x_1424_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_forM___redArg___lam__0(
    mut v_f_1427_: *mut leanh::LeanObject,
    mut v_x_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = leanh::lean_apply_1(v_f_1427_, v___y_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Subarray_forM___redArg(
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_f_1432_: *mut leanh::LeanObject,
    mut v_as_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    v_array_1434_ = leanh::lean_ctor_get(v_as_1433_, 0);
    leanh::lean_inc_ref(v_array_1434_);
    v_start_1435_ = leanh::lean_ctor_get(v_as_1433_, 1);
    leanh::lean_inc(v_start_1435_);
    v_stop_1436_ = leanh::lean_ctor_get(v_as_1433_, 2);
    leanh::lean_inc(v_stop_1436_);
    leanh::lean_dec_ref(v_as_1433_);
    v___x_1437_ = leanh::lean_box(0);
    v___x_1438_ = lean_nat_dec_lt(v_start_1435_, v_stop_1436_);
    if v___x_1438_ == 0 {
        let mut v_toApplicative_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stop_1436_);
        leanh::lean_dec(v_start_1435_);
        leanh::lean_dec_ref(v_array_1434_);
        leanh::lean_dec(v_f_1432_);
        v_toApplicative_1439_ = leanh::lean_ctor_get(v_inst_1431_, 0);
        leanh::lean_inc_ref(v_toApplicative_1439_);
        leanh::lean_dec_ref(v_inst_1431_);
        v_toPure_1440_ = leanh::lean_ctor_get(v_toApplicative_1439_, 1);
        leanh::lean_inc(v_toPure_1440_);
        leanh::lean_dec_ref(v_toApplicative_1439_);
        v___x_1441_ =
            leanh::lean_apply_2(v_toPure_1440_, leanh::lean_box(0), v___x_1437_);
        return v___x_1441_;
    } else {
        let mut v___f_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: u8 = 0;
        v___f_1442_ = leanh::lean_alloc_closure(
            l_Subarray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1442_, 0, v_f_1432_);
        v___x_1443_ = lean_array_get_size(v_array_1434_);
        v___x_1444_ = lean_nat_dec_le(v_stop_1436_, v___x_1443_);
        if v___x_1444_ == 0 {
            let mut v___x_1445_: u8 = 0;
            leanh::lean_dec(v_stop_1436_);
            v___x_1445_ = lean_nat_dec_lt(v_start_1435_, v___x_1443_);
            if v___x_1445_ == 0 {
                let mut v_toApplicative_1446_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1442_);
                leanh::lean_dec(v_start_1435_);
                leanh::lean_dec_ref(v_array_1434_);
                v_toApplicative_1446_ = leanh::lean_ctor_get(v_inst_1431_, 0);
                leanh::lean_inc_ref(v_toApplicative_1446_);
                leanh::lean_dec_ref(v_inst_1431_);
                v_toPure_1447_ = leanh::lean_ctor_get(v_toApplicative_1446_, 1);
                leanh::lean_inc(v_toPure_1447_);
                leanh::lean_dec_ref(v_toApplicative_1446_);
                v___x_1448_ = leanh::lean_apply_2(
                    v_toPure_1447_,
                    leanh::lean_box(0),
                    v___x_1437_,
                );
                return v___x_1448_;
            } else {
                let mut v___x_1449_: usize = 0;
                let mut v___x_1450_: usize = 0;
                let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1449_ = lean_usize_of_nat(v_start_1435_);
                leanh::lean_dec(v_start_1435_);
                v___x_1450_ = lean_usize_of_nat(v___x_1443_);
                v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1431_,
                    v___f_1442_,
                    v_array_1434_,
                    v___x_1449_,
                    v___x_1450_,
                    v___x_1437_,
                );
                return v___x_1451_;
            }
        } else {
            let mut v___x_1452_: usize = 0;
            let mut v___x_1453_: usize = 0;
            let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1452_ = lean_usize_of_nat(v_start_1435_);
            leanh::lean_dec(v_start_1435_);
            v___x_1453_ = lean_usize_of_nat(v_stop_1436_);
            leanh::lean_dec(v_stop_1436_);
            v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1431_,
                v___f_1442_,
                v_array_1434_,
                v___x_1452_,
                v___x_1453_,
                v___x_1437_,
            );
            return v___x_1454_;
        }
    }
}
pub unsafe fn l_Subarray_forM(
    mut v_00_u03b1_1455_: *mut leanh::LeanObject,
    mut v_m_1456_: *mut leanh::LeanObject,
    mut v_inst_1457_: *mut leanh::LeanObject,
    mut v_f_1458_: *mut leanh::LeanObject,
    mut v_as_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    v_array_1460_ = leanh::lean_ctor_get(v_as_1459_, 0);
    leanh::lean_inc_ref(v_array_1460_);
    v_start_1461_ = leanh::lean_ctor_get(v_as_1459_, 1);
    leanh::lean_inc(v_start_1461_);
    v_stop_1462_ = leanh::lean_ctor_get(v_as_1459_, 2);
    leanh::lean_inc(v_stop_1462_);
    leanh::lean_dec_ref(v_as_1459_);
    v___x_1463_ = leanh::lean_box(0);
    v___x_1464_ = lean_nat_dec_lt(v_start_1461_, v_stop_1462_);
    if v___x_1464_ == 0 {
        let mut v_toApplicative_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stop_1462_);
        leanh::lean_dec(v_start_1461_);
        leanh::lean_dec_ref(v_array_1460_);
        leanh::lean_dec(v_f_1458_);
        v_toApplicative_1465_ = leanh::lean_ctor_get(v_inst_1457_, 0);
        leanh::lean_inc_ref(v_toApplicative_1465_);
        leanh::lean_dec_ref(v_inst_1457_);
        v_toPure_1466_ = leanh::lean_ctor_get(v_toApplicative_1465_, 1);
        leanh::lean_inc(v_toPure_1466_);
        leanh::lean_dec_ref(v_toApplicative_1465_);
        v___x_1467_ =
            leanh::lean_apply_2(v_toPure_1466_, leanh::lean_box(0), v___x_1463_);
        return v___x_1467_;
    } else {
        let mut v___f_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: u8 = 0;
        v___f_1468_ = leanh::lean_alloc_closure(
            l_Subarray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1468_, 0, v_f_1458_);
        v___x_1469_ = lean_array_get_size(v_array_1460_);
        v___x_1470_ = lean_nat_dec_le(v_stop_1462_, v___x_1469_);
        if v___x_1470_ == 0 {
            let mut v___x_1471_: u8 = 0;
            leanh::lean_dec(v_stop_1462_);
            v___x_1471_ = lean_nat_dec_lt(v_start_1461_, v___x_1469_);
            if v___x_1471_ == 0 {
                let mut v_toApplicative_1472_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_1468_);
                leanh::lean_dec(v_start_1461_);
                leanh::lean_dec_ref(v_array_1460_);
                v_toApplicative_1472_ = leanh::lean_ctor_get(v_inst_1457_, 0);
                leanh::lean_inc_ref(v_toApplicative_1472_);
                leanh::lean_dec_ref(v_inst_1457_);
                v_toPure_1473_ = leanh::lean_ctor_get(v_toApplicative_1472_, 1);
                leanh::lean_inc(v_toPure_1473_);
                leanh::lean_dec_ref(v_toApplicative_1472_);
                v___x_1474_ = leanh::lean_apply_2(
                    v_toPure_1473_,
                    leanh::lean_box(0),
                    v___x_1463_,
                );
                return v___x_1474_;
            } else {
                let mut v___x_1475_: usize = 0;
                let mut v___x_1476_: usize = 0;
                let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1475_ = lean_usize_of_nat(v_start_1461_);
                leanh::lean_dec(v_start_1461_);
                v___x_1476_ = lean_usize_of_nat(v___x_1469_);
                v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_1457_,
                    v___f_1468_,
                    v_array_1460_,
                    v___x_1475_,
                    v___x_1476_,
                    v___x_1463_,
                );
                return v___x_1477_;
            }
        } else {
            let mut v___x_1478_: usize = 0;
            let mut v___x_1479_: usize = 0;
            let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1478_ = lean_usize_of_nat(v_start_1461_);
            leanh::lean_dec(v_start_1461_);
            v___x_1479_ = lean_usize_of_nat(v_stop_1462_);
            leanh::lean_dec(v_stop_1462_);
            v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1457_,
                v___f_1468_,
                v_array_1460_,
                v___x_1478_,
                v___x_1479_,
                v___x_1463_,
            );
            return v___x_1480_;
        }
    }
}
pub unsafe fn l_Subarray_forRevM___redArg___lam__0(
    mut v_f_1481_: *mut leanh::LeanObject,
    mut v_a_1482_: *mut leanh::LeanObject,
    mut v_x_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = leanh::lean_apply_1(v_f_1481_, v_a_1482_);
    return v___x_1484_;
}
pub unsafe fn l_Subarray_forRevM___redArg(
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_f_1486_: *mut leanh::LeanObject,
    mut v_as_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    v_array_1488_ = leanh::lean_ctor_get(v_as_1487_, 0);
    leanh::lean_inc_ref(v_array_1488_);
    v_start_1489_ = leanh::lean_ctor_get(v_as_1487_, 1);
    leanh::lean_inc(v_start_1489_);
    v_stop_1490_ = leanh::lean_ctor_get(v_as_1487_, 2);
    leanh::lean_inc(v_stop_1490_);
    leanh::lean_dec_ref(v_as_1487_);
    v___f_1491_ = leanh::lean_alloc_closure(
        l_Subarray_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1491_, 0, v_f_1486_);
    v___x_1492_ = leanh::lean_box(0);
    v___x_1493_ = lean_array_get_size(v_array_1488_);
    v___x_1494_ = lean_nat_dec_le(v_stop_1490_, v___x_1493_);
    if v___x_1494_ == 0 {
        let mut v___x_1495_: u8 = 0;
        leanh::lean_dec(v_stop_1490_);
        v___x_1495_ = lean_nat_dec_lt(v_start_1489_, v___x_1493_);
        if v___x_1495_ == 0 {
            let mut v_toApplicative_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___f_1491_);
            leanh::lean_dec(v_start_1489_);
            leanh::lean_dec_ref(v_array_1488_);
            v_toApplicative_1496_ = leanh::lean_ctor_get(v_inst_1485_, 0);
            leanh::lean_inc_ref(v_toApplicative_1496_);
            leanh::lean_dec_ref(v_inst_1485_);
            v_toPure_1497_ = leanh::lean_ctor_get(v_toApplicative_1496_, 1);
            leanh::lean_inc(v_toPure_1497_);
            leanh::lean_dec_ref(v_toApplicative_1496_);
            v___x_1498_ =
                leanh::lean_apply_2(v_toPure_1497_, leanh::lean_box(0), v___x_1492_);
            return v___x_1498_;
        } else {
            let mut v___x_1499_: usize = 0;
            let mut v___x_1500_: usize = 0;
            let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1499_ = lean_usize_of_nat(v___x_1493_);
            v___x_1500_ = lean_usize_of_nat(v_start_1489_);
            leanh::lean_dec(v_start_1489_);
            v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1485_,
                v___f_1491_,
                v_array_1488_,
                v___x_1499_,
                v___x_1500_,
                v___x_1492_,
            );
            return v___x_1501_;
        }
    } else {
        let mut v___x_1502_: u8 = 0;
        v___x_1502_ = lean_nat_dec_lt(v_start_1489_, v_stop_1490_);
        if v___x_1502_ == 0 {
            let mut v_toApplicative_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___f_1491_);
            leanh::lean_dec(v_stop_1490_);
            leanh::lean_dec(v_start_1489_);
            leanh::lean_dec_ref(v_array_1488_);
            v_toApplicative_1503_ = leanh::lean_ctor_get(v_inst_1485_, 0);
            leanh::lean_inc_ref(v_toApplicative_1503_);
            leanh::lean_dec_ref(v_inst_1485_);
            v_toPure_1504_ = leanh::lean_ctor_get(v_toApplicative_1503_, 1);
            leanh::lean_inc(v_toPure_1504_);
            leanh::lean_dec_ref(v_toApplicative_1503_);
            v___x_1505_ =
                leanh::lean_apply_2(v_toPure_1504_, leanh::lean_box(0), v___x_1492_);
            return v___x_1505_;
        } else {
            let mut v___x_1506_: usize = 0;
            let mut v___x_1507_: usize = 0;
            let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1506_ = lean_usize_of_nat(v_stop_1490_);
            leanh::lean_dec(v_stop_1490_);
            v___x_1507_ = lean_usize_of_nat(v_start_1489_);
            leanh::lean_dec(v_start_1489_);
            v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1485_,
                v___f_1491_,
                v_array_1488_,
                v___x_1506_,
                v___x_1507_,
                v___x_1492_,
            );
            return v___x_1508_;
        }
    }
}
pub unsafe fn l_Subarray_forRevM(
    mut v_00_u03b1_1509_: *mut leanh::LeanObject,
    mut v_m_1510_: *mut leanh::LeanObject,
    mut v_inst_1511_: *mut leanh::LeanObject,
    mut v_f_1512_: *mut leanh::LeanObject,
    mut v_as_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    v_array_1514_ = leanh::lean_ctor_get(v_as_1513_, 0);
    leanh::lean_inc_ref(v_array_1514_);
    v_start_1515_ = leanh::lean_ctor_get(v_as_1513_, 1);
    leanh::lean_inc(v_start_1515_);
    v_stop_1516_ = leanh::lean_ctor_get(v_as_1513_, 2);
    leanh::lean_inc(v_stop_1516_);
    leanh::lean_dec_ref(v_as_1513_);
    v___f_1517_ = leanh::lean_alloc_closure(
        l_Subarray_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1517_, 0, v_f_1512_);
    v___x_1518_ = leanh::lean_box(0);
    v___x_1519_ = lean_array_get_size(v_array_1514_);
    v___x_1520_ = lean_nat_dec_le(v_stop_1516_, v___x_1519_);
    if v___x_1520_ == 0 {
        let mut v___x_1521_: u8 = 0;
        leanh::lean_dec(v_stop_1516_);
        v___x_1521_ = lean_nat_dec_lt(v_start_1515_, v___x_1519_);
        if v___x_1521_ == 0 {
            let mut v_toApplicative_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___f_1517_);
            leanh::lean_dec(v_start_1515_);
            leanh::lean_dec_ref(v_array_1514_);
            v_toApplicative_1522_ = leanh::lean_ctor_get(v_inst_1511_, 0);
            leanh::lean_inc_ref(v_toApplicative_1522_);
            leanh::lean_dec_ref(v_inst_1511_);
            v_toPure_1523_ = leanh::lean_ctor_get(v_toApplicative_1522_, 1);
            leanh::lean_inc(v_toPure_1523_);
            leanh::lean_dec_ref(v_toApplicative_1522_);
            v___x_1524_ =
                leanh::lean_apply_2(v_toPure_1523_, leanh::lean_box(0), v___x_1518_);
            return v___x_1524_;
        } else {
            let mut v___x_1525_: usize = 0;
            let mut v___x_1526_: usize = 0;
            let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1525_ = lean_usize_of_nat(v___x_1519_);
            v___x_1526_ = lean_usize_of_nat(v_start_1515_);
            leanh::lean_dec(v_start_1515_);
            v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1511_,
                v___f_1517_,
                v_array_1514_,
                v___x_1525_,
                v___x_1526_,
                v___x_1518_,
            );
            return v___x_1527_;
        }
    } else {
        let mut v___x_1528_: u8 = 0;
        v___x_1528_ = lean_nat_dec_lt(v_start_1515_, v_stop_1516_);
        if v___x_1528_ == 0 {
            let mut v_toApplicative_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___f_1517_);
            leanh::lean_dec(v_stop_1516_);
            leanh::lean_dec(v_start_1515_);
            leanh::lean_dec_ref(v_array_1514_);
            v_toApplicative_1529_ = leanh::lean_ctor_get(v_inst_1511_, 0);
            leanh::lean_inc_ref(v_toApplicative_1529_);
            leanh::lean_dec_ref(v_inst_1511_);
            v_toPure_1530_ = leanh::lean_ctor_get(v_toApplicative_1529_, 1);
            leanh::lean_inc(v_toPure_1530_);
            leanh::lean_dec_ref(v_toApplicative_1529_);
            v___x_1531_ =
                leanh::lean_apply_2(v_toPure_1530_, leanh::lean_box(0), v___x_1518_);
            return v___x_1531_;
        } else {
            let mut v___x_1532_: usize = 0;
            let mut v___x_1533_: usize = 0;
            let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1532_ = lean_usize_of_nat(v_stop_1516_);
            leanh::lean_dec(v_stop_1516_);
            v___x_1533_ = lean_usize_of_nat(v_start_1515_);
            leanh::lean_dec(v_start_1515_);
            v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_1511_,
                v___f_1517_,
                v_array_1514_,
                v___x_1532_,
                v___x_1533_,
                v___x_1518_,
            );
            return v___x_1534_;
        }
    }
}
pub unsafe fn l_Subarray_foldr___redArg___lam__0(
    mut v_f_1535_: *mut leanh::LeanObject,
    mut v_x1_1536_: *mut leanh::LeanObject,
    mut v_x2_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = leanh::lean_apply_2(v_f_1535_, v_x1_1536_, v_x2_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Subarray_foldr___redArg(
    mut v_f_1558_: *mut leanh::LeanObject,
    mut v_init_1559_: *mut leanh::LeanObject,
    mut v_as_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    v___x_1561_ = l_Subarray_foldr___redArg___closed__9;
    v_array_1562_ = leanh::lean_ctor_get(v_as_1560_, 0);
    leanh::lean_inc_ref(v_array_1562_);
    v_start_1563_ = leanh::lean_ctor_get(v_as_1560_, 1);
    leanh::lean_inc(v_start_1563_);
    v_stop_1564_ = leanh::lean_ctor_get(v_as_1560_, 2);
    leanh::lean_inc(v_stop_1564_);
    leanh::lean_dec_ref(v_as_1560_);
    v___f_1565_ = leanh::lean_alloc_closure(
        l_Subarray_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1565_, 0, v_f_1558_);
    v___x_1566_ = lean_array_get_size(v_array_1562_);
    v___x_1567_ = lean_nat_dec_le(v_stop_1564_, v___x_1566_);
    if v___x_1567_ == 0 {
        let mut v___x_1568_: u8 = 0;
        leanh::lean_dec(v_stop_1564_);
        v___x_1568_ = lean_nat_dec_lt(v_start_1563_, v___x_1566_);
        if v___x_1568_ == 0 {
            leanh::lean_dec_ref(v___f_1565_);
            leanh::lean_dec(v_start_1563_);
            leanh::lean_dec_ref(v_array_1562_);
            return v_init_1559_;
        } else {
            let mut v___x_1569_: usize = 0;
            let mut v___x_1570_: usize = 0;
            let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1569_ = lean_usize_of_nat(v___x_1566_);
            v___x_1570_ = lean_usize_of_nat(v_start_1563_);
            leanh::lean_dec(v_start_1563_);
            v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1561_,
                v___f_1565_,
                v_array_1562_,
                v___x_1569_,
                v___x_1570_,
                v_init_1559_,
            );
            return v___x_1571_;
        }
    } else {
        let mut v___x_1572_: u8 = 0;
        v___x_1572_ = lean_nat_dec_lt(v_start_1563_, v_stop_1564_);
        if v___x_1572_ == 0 {
            leanh::lean_dec_ref(v___f_1565_);
            leanh::lean_dec(v_stop_1564_);
            leanh::lean_dec(v_start_1563_);
            leanh::lean_dec_ref(v_array_1562_);
            return v_init_1559_;
        } else {
            let mut v___x_1573_: usize = 0;
            let mut v___x_1574_: usize = 0;
            let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1573_ = lean_usize_of_nat(v_stop_1564_);
            leanh::lean_dec(v_stop_1564_);
            v___x_1574_ = lean_usize_of_nat(v_start_1563_);
            leanh::lean_dec(v_start_1563_);
            v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1561_,
                v___f_1565_,
                v_array_1562_,
                v___x_1573_,
                v___x_1574_,
                v_init_1559_,
            );
            return v___x_1575_;
        }
    }
}
pub unsafe fn l_Subarray_foldr(
    mut v_00_u03b1_1576_: *mut leanh::LeanObject,
    mut v_00_u03b2_1577_: *mut leanh::LeanObject,
    mut v_f_1578_: *mut leanh::LeanObject,
    mut v_init_1579_: *mut leanh::LeanObject,
    mut v_as_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    v___x_1581_ = l_Subarray_foldr___redArg___closed__9;
    v_array_1582_ = leanh::lean_ctor_get(v_as_1580_, 0);
    leanh::lean_inc_ref(v_array_1582_);
    v_start_1583_ = leanh::lean_ctor_get(v_as_1580_, 1);
    leanh::lean_inc(v_start_1583_);
    v_stop_1584_ = leanh::lean_ctor_get(v_as_1580_, 2);
    leanh::lean_inc(v_stop_1584_);
    leanh::lean_dec_ref(v_as_1580_);
    v___f_1585_ = leanh::lean_alloc_closure(
        l_Subarray_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1585_, 0, v_f_1578_);
    v___x_1586_ = lean_array_get_size(v_array_1582_);
    v___x_1587_ = lean_nat_dec_le(v_stop_1584_, v___x_1586_);
    if v___x_1587_ == 0 {
        let mut v___x_1588_: u8 = 0;
        leanh::lean_dec(v_stop_1584_);
        v___x_1588_ = lean_nat_dec_lt(v_start_1583_, v___x_1586_);
        if v___x_1588_ == 0 {
            leanh::lean_dec_ref(v___f_1585_);
            leanh::lean_dec(v_start_1583_);
            leanh::lean_dec_ref(v_array_1582_);
            return v_init_1579_;
        } else {
            let mut v___x_1589_: usize = 0;
            let mut v___x_1590_: usize = 0;
            let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1589_ = lean_usize_of_nat(v___x_1586_);
            v___x_1590_ = lean_usize_of_nat(v_start_1583_);
            leanh::lean_dec(v_start_1583_);
            v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1581_,
                v___f_1585_,
                v_array_1582_,
                v___x_1589_,
                v___x_1590_,
                v_init_1579_,
            );
            return v___x_1591_;
        }
    } else {
        let mut v___x_1592_: u8 = 0;
        v___x_1592_ = lean_nat_dec_lt(v_start_1583_, v_stop_1584_);
        if v___x_1592_ == 0 {
            leanh::lean_dec_ref(v___f_1585_);
            leanh::lean_dec(v_stop_1584_);
            leanh::lean_dec(v_start_1583_);
            leanh::lean_dec_ref(v_array_1582_);
            return v_init_1579_;
        } else {
            let mut v___x_1593_: usize = 0;
            let mut v___x_1594_: usize = 0;
            let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1593_ = lean_usize_of_nat(v_stop_1584_);
            leanh::lean_dec(v_stop_1584_);
            v___x_1594_ = lean_usize_of_nat(v_start_1583_);
            leanh::lean_dec(v_start_1583_);
            v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1581_,
                v___f_1585_,
                v_array_1582_,
                v___x_1593_,
                v___x_1594_,
                v_init_1579_,
            );
            return v___x_1595_;
        }
    }
}
pub unsafe fn l_Subarray_any___redArg___lam__0(
    mut v_p_1596_: *mut leanh::LeanObject,
    mut v_x_1597_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v___x_1598_ = leanh::lean_apply_1(v_p_1596_, v_x_1597_);
    v___x_1599_ = (leanh::lean_unbox(v___x_1598_) as u8);
    return v___x_1599_;
}
pub unsafe fn l_Subarray_any___redArg___lam__0___boxed(
    mut v_p_1600_: *mut leanh::LeanObject,
    mut v_x_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: u8 = 0;
    let mut v_r_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Subarray_any___redArg___lam__0(v_p_1600_, v_x_1601_);
    v_r_1603_ = leanh::lean_box((v_res_1602_) as usize);
    return v_r_1603_;
}
pub unsafe fn l_Subarray_any___redArg(
    mut v_p_1604_: *mut leanh::LeanObject,
    mut v_as_1605_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___f_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: usize = 0;
    let mut v___x_1616_: usize = 0;
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1606_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1607_ = leanh::lean_ctor_get(v_as_1605_, 0);
                leanh::lean_inc_ref(v_array_1607_);
                v_start_1608_ = leanh::lean_ctor_get(v_as_1605_, 1);
                leanh::lean_inc(v_start_1608_);
                v_stop_1609_ = leanh::lean_ctor_get(v_as_1605_, 2);
                leanh::lean_inc(v_stop_1609_);
                leanh::lean_dec_ref(v_as_1605_);
                v___x_1610_ = lean_nat_dec_lt(v_start_1608_, v_stop_1609_);
                if v___x_1610_ == 0 {
                    leanh::lean_dec(v_stop_1609_);
                    leanh::lean_dec(v_start_1608_);
                    leanh::lean_dec_ref(v_array_1607_);
                    leanh::lean_dec_ref(v_p_1604_);
                    return v___x_1610_;
                } else {
                    v___f_1611_ = leanh::lean_alloc_closure(
                        l_Subarray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1611_, 0, v_p_1604_);
                    v___x_1619_ = lean_array_get_size(v_array_1607_);
                    v___x_1620_ = lean_nat_dec_le(v_stop_1609_, v___x_1619_);
                    if v___x_1620_ == 0 {
                        leanh::lean_dec(v_stop_1609_);
                        v___y_1613_ = v___x_1619_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1613_ = v_stop_1609_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1614_ = lean_nat_dec_lt(v_start_1608_, v___y_1613_);
                if v___x_1614_ == 0 {
                    leanh::lean_dec(v___y_1613_);
                    leanh::lean_dec_ref(v___f_1611_);
                    leanh::lean_dec(v_start_1608_);
                    leanh::lean_dec_ref(v_array_1607_);
                    return v___x_1614_;
                } else {
                    v___x_1615_ = lean_usize_of_nat(v_start_1608_);
                    leanh::lean_dec(v_start_1608_);
                    v___x_1616_ = lean_usize_of_nat(v___y_1613_);
                    leanh::lean_dec(v___y_1613_);
                    v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1606_,
                        v___f_1611_,
                        v_array_1607_,
                        v___x_1615_,
                        v___x_1616_,
                    );
                    v___x_1618_ = (leanh::lean_unbox(v___x_1617_) as u8);
                    leanh::lean_dec(v___x_1617_);
                    return v___x_1618_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_any___redArg___boxed(
    mut v_p_1621_: *mut leanh::LeanObject,
    mut v_as_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1623_: u8 = 0;
    let mut v_r_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Subarray_any___redArg(v_p_1621_, v_as_1622_);
    v_r_1624_ = leanh::lean_box((v_res_1623_) as usize);
    return v_r_1624_;
}
pub unsafe fn l_Subarray_any(
    mut v_00_u03b1_1625_: *mut leanh::LeanObject,
    mut v_p_1626_: *mut leanh::LeanObject,
    mut v_as_1627_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___f_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: usize = 0;
    let mut v___x_1638_: usize = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1628_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1629_ = leanh::lean_ctor_get(v_as_1627_, 0);
                leanh::lean_inc_ref(v_array_1629_);
                v_start_1630_ = leanh::lean_ctor_get(v_as_1627_, 1);
                leanh::lean_inc(v_start_1630_);
                v_stop_1631_ = leanh::lean_ctor_get(v_as_1627_, 2);
                leanh::lean_inc(v_stop_1631_);
                leanh::lean_dec_ref(v_as_1627_);
                v___x_1632_ = lean_nat_dec_lt(v_start_1630_, v_stop_1631_);
                if v___x_1632_ == 0 {
                    leanh::lean_dec(v_stop_1631_);
                    leanh::lean_dec(v_start_1630_);
                    leanh::lean_dec_ref(v_array_1629_);
                    leanh::lean_dec_ref(v_p_1626_);
                    return v___x_1632_;
                } else {
                    v___f_1633_ = leanh::lean_alloc_closure(
                        l_Subarray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1633_, 0, v_p_1626_);
                    v___x_1641_ = lean_array_get_size(v_array_1629_);
                    v___x_1642_ = lean_nat_dec_le(v_stop_1631_, v___x_1641_);
                    if v___x_1642_ == 0 {
                        leanh::lean_dec(v_stop_1631_);
                        v___y_1635_ = v___x_1641_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1635_ = v_stop_1631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1636_ = lean_nat_dec_lt(v_start_1630_, v___y_1635_);
                if v___x_1636_ == 0 {
                    leanh::lean_dec(v___y_1635_);
                    leanh::lean_dec_ref(v___f_1633_);
                    leanh::lean_dec(v_start_1630_);
                    leanh::lean_dec_ref(v_array_1629_);
                    return v___x_1636_;
                } else {
                    v___x_1637_ = lean_usize_of_nat(v_start_1630_);
                    leanh::lean_dec(v_start_1630_);
                    v___x_1638_ = lean_usize_of_nat(v___y_1635_);
                    leanh::lean_dec(v___y_1635_);
                    v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1628_,
                        v___f_1633_,
                        v_array_1629_,
                        v___x_1637_,
                        v___x_1638_,
                    );
                    v___x_1640_ = (leanh::lean_unbox(v___x_1639_) as u8);
                    leanh::lean_dec(v___x_1639_);
                    return v___x_1640_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_any___boxed(
    mut v_00_u03b1_1643_: *mut leanh::LeanObject,
    mut v_p_1644_: *mut leanh::LeanObject,
    mut v_as_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Subarray_any(v_00_u03b1_1643_, v_p_1644_, v_as_1645_);
    v_r_1647_ = leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Subarray_all___redArg___lam__0(
    mut v_p_1648_: *mut leanh::LeanObject,
    mut v___x_1649_: u8,
    mut v_v_1650_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    v___x_1651_ = leanh::lean_apply_1(v_p_1648_, v_v_1650_);
    v___x_1652_ = (leanh::lean_unbox(v___x_1651_) as u8);
    if v___x_1652_ == 0 {
        return v___x_1649_;
    } else {
        let mut v___x_1653_: u8 = 0;
        v___x_1653_ = 0;
        return v___x_1653_;
    }
}
pub unsafe fn l_Subarray_all___redArg___lam__0___boxed(
    mut v_p_1654_: *mut leanh::LeanObject,
    mut v___x_1655_: *mut leanh::LeanObject,
    mut v_v_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342__boxed_1657_: u8 = 0;
    let mut v_res_1658_: u8 = 0;
    let mut v_r_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342__boxed_1657_ = (leanh::lean_unbox(v___x_1655_) as u8);
    v_res_1658_ = l_Subarray_all___redArg___lam__0(v_p_1654_, v___x_342__boxed_1657_, v_v_1656_);
    v_r_1659_ = leanh::lean_box((v_res_1658_) as usize);
    return v_r_1659_;
}
pub unsafe fn l_Subarray_all___redArg(
    mut v_p_1660_: *mut leanh::LeanObject,
    mut v_as_1661_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: u8 = 0;
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1662_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1663_ = leanh::lean_ctor_get(v_as_1661_, 0);
                leanh::lean_inc_ref(v_array_1663_);
                v_start_1664_ = leanh::lean_ctor_get(v_as_1661_, 1);
                leanh::lean_inc(v_start_1664_);
                v_stop_1665_ = leanh::lean_ctor_get(v_as_1661_, 2);
                leanh::lean_inc(v_stop_1665_);
                leanh::lean_dec_ref(v_as_1661_);
                v___x_1666_ = lean_nat_dec_lt(v_start_1664_, v_stop_1665_);
                if v___x_1666_ == 0 {
                    leanh::lean_dec(v_stop_1665_);
                    leanh::lean_dec(v_start_1664_);
                    leanh::lean_dec_ref(v_array_1663_);
                    leanh::lean_dec_ref(v_p_1660_);
                    v___x_1667_ = 1;
                    return v___x_1667_;
                } else {
                    v___x_1668_ = leanh::lean_box((v___x_1666_) as usize);
                    v___f_1669_ = leanh::lean_alloc_closure(
                        l_Subarray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1669_, 0, v_p_1660_);
                    leanh::lean_closure_set(v___f_1669_, 1, v___x_1668_);
                    v___x_1678_ = lean_array_get_size(v_array_1663_);
                    v___x_1679_ = lean_nat_dec_le(v_stop_1665_, v___x_1678_);
                    if v___x_1679_ == 0 {
                        leanh::lean_dec(v_stop_1665_);
                        v___y_1671_ = v___x_1678_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1671_ = v_stop_1665_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1672_ = lean_nat_dec_lt(v_start_1664_, v___y_1671_);
                if v___x_1672_ == 0 {
                    leanh::lean_dec(v___y_1671_);
                    leanh::lean_dec_ref(v___f_1669_);
                    leanh::lean_dec(v_start_1664_);
                    leanh::lean_dec_ref(v_array_1663_);
                    return v___x_1666_;
                } else {
                    v___x_1673_ = lean_usize_of_nat(v_start_1664_);
                    leanh::lean_dec(v_start_1664_);
                    v___x_1674_ = lean_usize_of_nat(v___y_1671_);
                    leanh::lean_dec(v___y_1671_);
                    v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1662_,
                        v___f_1669_,
                        v_array_1663_,
                        v___x_1673_,
                        v___x_1674_,
                    );
                    v___x_1676_ = (leanh::lean_unbox(v___x_1675_) as u8);
                    leanh::lean_dec(v___x_1675_);
                    if v___x_1676_ == 0 {
                        return v___x_1672_;
                    } else {
                        v___x_1677_ = 0;
                        return v___x_1677_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_all___redArg___boxed(
    mut v_p_1680_: *mut leanh::LeanObject,
    mut v_as_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Subarray_all___redArg(v_p_1680_, v_as_1681_);
    v_r_1683_ = leanh::lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn l_Subarray_all(
    mut v_00_u03b1_1684_: *mut leanh::LeanObject,
    mut v_p_1685_: *mut leanh::LeanObject,
    mut v_as_1686_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: usize = 0;
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1687_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1688_ = leanh::lean_ctor_get(v_as_1686_, 0);
                leanh::lean_inc_ref(v_array_1688_);
                v_start_1689_ = leanh::lean_ctor_get(v_as_1686_, 1);
                leanh::lean_inc(v_start_1689_);
                v_stop_1690_ = leanh::lean_ctor_get(v_as_1686_, 2);
                leanh::lean_inc(v_stop_1690_);
                leanh::lean_dec_ref(v_as_1686_);
                v___x_1691_ = lean_nat_dec_lt(v_start_1689_, v_stop_1690_);
                if v___x_1691_ == 0 {
                    leanh::lean_dec(v_stop_1690_);
                    leanh::lean_dec(v_start_1689_);
                    leanh::lean_dec_ref(v_array_1688_);
                    leanh::lean_dec_ref(v_p_1685_);
                    v___x_1692_ = 1;
                    return v___x_1692_;
                } else {
                    v___x_1693_ = leanh::lean_box((v___x_1691_) as usize);
                    v___f_1694_ = leanh::lean_alloc_closure(
                        l_Subarray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1694_, 0, v_p_1685_);
                    leanh::lean_closure_set(v___f_1694_, 1, v___x_1693_);
                    v___x_1703_ = lean_array_get_size(v_array_1688_);
                    v___x_1704_ = lean_nat_dec_le(v_stop_1690_, v___x_1703_);
                    if v___x_1704_ == 0 {
                        leanh::lean_dec(v_stop_1690_);
                        v___y_1696_ = v___x_1703_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1696_ = v_stop_1690_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1697_ = lean_nat_dec_lt(v_start_1689_, v___y_1696_);
                if v___x_1697_ == 0 {
                    leanh::lean_dec(v___y_1696_);
                    leanh::lean_dec_ref(v___f_1694_);
                    leanh::lean_dec(v_start_1689_);
                    leanh::lean_dec_ref(v_array_1688_);
                    return v___x_1691_;
                } else {
                    v___x_1698_ = lean_usize_of_nat(v_start_1689_);
                    leanh::lean_dec(v_start_1689_);
                    v___x_1699_ = lean_usize_of_nat(v___y_1696_);
                    leanh::lean_dec(v___y_1696_);
                    v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1687_,
                        v___f_1694_,
                        v_array_1688_,
                        v___x_1698_,
                        v___x_1699_,
                    );
                    v___x_1701_ = (leanh::lean_unbox(v___x_1700_) as u8);
                    leanh::lean_dec(v___x_1700_);
                    if v___x_1701_ == 0 {
                        return v___x_1697_;
                    } else {
                        v___x_1702_ = 0;
                        return v___x_1702_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_all___boxed(
    mut v_00_u03b1_1705_: *mut leanh::LeanObject,
    mut v_p_1706_: *mut leanh::LeanObject,
    mut v_as_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1708_: u8 = 0;
    let mut v_r_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Subarray_all(v_00_u03b1_1705_, v_p_1706_, v_as_1707_);
    v_r_1709_ = leanh::lean_box((v_res_1708_) as usize);
    return v_r_1709_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(
    mut v_inst_1710_: *mut leanh::LeanObject,
    mut v_as_1711_: *mut leanh::LeanObject,
    mut v_f_1712_: *mut leanh::LeanObject,
    mut v_n_1713_: *mut leanh::LeanObject,
    mut v_toPure_1714_: *mut leanh::LeanObject,
    mut v_r_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ =
        l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(
            v_inst_1710_,
            v_as_1711_,
            v_f_1712_,
            v_n_1713_,
            v_toPure_1714_,
            v_r_1715_,
        );
    leanh::lean_dec(v_n_1713_);
    return v_res_1716_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
    mut v_inst_1717_: *mut leanh::LeanObject,
    mut v_as_1718_: *mut leanh::LeanObject,
    mut v_f_1719_: *mut leanh::LeanObject,
    mut v_i_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1725_: u8 = 0;
    v_toApplicative_1721_ = leanh::lean_ctor_get(v_inst_1717_, 0);
    v_toBind_1722_ = leanh::lean_ctor_get(v_inst_1717_, 1);
    leanh::lean_inc(v_toBind_1722_);
    v_toPure_1723_ = leanh::lean_ctor_get(v_toApplicative_1721_, 1);
    leanh::lean_inc(v_toPure_1723_);
    v_zero_1724_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1725_ = lean_nat_dec_eq(v_i_1720_, v_zero_1724_);
    if v_isZero_1725_ == 1 {
        let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_1722_);
        leanh::lean_dec(v_f_1719_);
        leanh::lean_dec_ref(v_as_1718_);
        leanh::lean_dec_ref(v_inst_1717_);
        v___x_1726_ = leanh::lean_box(0);
        v___x_1727_ =
            leanh::lean_apply_2(v_toPure_1723_, leanh::lean_box(0), v___x_1726_);
        return v___x_1727_;
    } else {
        let mut v_one_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_1728_ = leanh::lean_unsigned_to_nat(1);
        v_n_1729_ = lean_nat_sub(v_i_1720_, v_one_1728_);
        leanh::lean_inc(v_n_1729_);
        leanh::lean_inc(v_f_1719_);
        leanh::lean_inc_ref(v_as_1718_);
        v___f_1730_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_1730_, 0, v_inst_1717_);
        leanh::lean_closure_set(v___f_1730_, 1, v_as_1718_);
        leanh::lean_closure_set(v___f_1730_, 2, v_f_1719_);
        leanh::lean_closure_set(v___f_1730_, 3, v_n_1729_);
        leanh::lean_closure_set(v___f_1730_, 4, v_toPure_1723_);
        v___x_1731_ = l_Subarray_get___redArg(v_as_1718_, v_n_1729_);
        leanh::lean_dec(v_n_1729_);
        leanh::lean_dec_ref(v_as_1718_);
        v___x_1732_ = leanh::lean_apply_1(v_f_1719_, v___x_1731_);
        v___x_1733_ = leanh::lean_apply_4(
            v_toBind_1722_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1732_,
            v___f_1730_,
        );
        return v___x_1733_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(
    mut v_inst_1734_: *mut leanh::LeanObject,
    mut v_as_1735_: *mut leanh::LeanObject,
    mut v_f_1736_: *mut leanh::LeanObject,
    mut v_n_1737_: *mut leanh::LeanObject,
    mut v_toPure_1738_: *mut leanh::LeanObject,
    mut v_r_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_1739_) == 0 {
        let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1738_);
        v___x_1740_ =
            l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
                v_inst_1734_,
                v_as_1735_,
                v_f_1736_,
                v_n_1737_,
            );
        return v___x_1740_;
    } else {
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_1736_);
        leanh::lean_dec_ref(v_as_1735_);
        leanh::lean_dec_ref(v_inst_1734_);
        v___x_1741_ =
            leanh::lean_apply_2(v_toPure_1738_, leanh::lean_box(0), v_r_1739_);
        return v___x_1741_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(
    mut v_inst_1742_: *mut leanh::LeanObject,
    mut v_as_1743_: *mut leanh::LeanObject,
    mut v_f_1744_: *mut leanh::LeanObject,
    mut v_i_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1742_,
        v_as_1743_,
        v_f_1744_,
        v_i_1745_,
    );
    leanh::lean_dec(v_i_1745_);
    return v_res_1746_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(
    mut v_00_u03b1_1747_: *mut leanh::LeanObject,
    mut v_00_u03b2_1748_: *mut leanh::LeanObject,
    mut v_m_1749_: *mut leanh::LeanObject,
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_as_1751_: *mut leanh::LeanObject,
    mut v_f_1752_: *mut leanh::LeanObject,
    mut v_i_1753_: *mut leanh::LeanObject,
    mut v_a_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1750_,
        v_as_1751_,
        v_f_1752_,
        v_i_1753_,
    );
    return v___x_1755_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(
    mut v_00_u03b1_1756_: *mut leanh::LeanObject,
    mut v_00_u03b2_1757_: *mut leanh::LeanObject,
    mut v_m_1758_: *mut leanh::LeanObject,
    mut v_inst_1759_: *mut leanh::LeanObject,
    mut v_as_1760_: *mut leanh::LeanObject,
    mut v_f_1761_: *mut leanh::LeanObject,
    mut v_i_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1764_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(
        v_00_u03b1_1756_,
        v_00_u03b2_1757_,
        v_m_1758_,
        v_inst_1759_,
        v_as_1760_,
        v_f_1761_,
        v_i_1762_,
        v_a_1763_,
    );
    leanh::lean_dec(v_i_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Subarray_findSomeRevM_x3f___redArg(
    mut v_inst_1765_: *mut leanh::LeanObject,
    mut v_as_1766_: *mut leanh::LeanObject,
    mut v_f_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_1768_ = leanh::lean_ctor_get(v_as_1766_, 1);
    v_stop_1769_ = leanh::lean_ctor_get(v_as_1766_, 2);
    v___x_1770_ = lean_nat_sub(v_stop_1769_, v_start_1768_);
    v___x_1771_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1765_,
        v_as_1766_,
        v_f_1767_,
        v___x_1770_,
    );
    leanh::lean_dec(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Subarray_findSomeRevM_x3f(
    mut v_00_u03b1_1772_: *mut leanh::LeanObject,
    mut v_00_u03b2_1773_: *mut leanh::LeanObject,
    mut v_m_1774_: *mut leanh::LeanObject,
    mut v_inst_1775_: *mut leanh::LeanObject,
    mut v_as_1776_: *mut leanh::LeanObject,
    mut v_f_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_1778_ = leanh::lean_ctor_get(v_as_1776_, 1);
    v_stop_1779_ = leanh::lean_ctor_get(v_as_1776_, 2);
    v___x_1780_ = lean_nat_sub(v_stop_1779_, v_start_1778_);
    v___x_1781_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1775_,
        v_as_1776_,
        v_f_1777_,
        v___x_1780_,
    );
    leanh::lean_dec(v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__0(
    mut v_toPure_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
    mut v_____do__lift_1784_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1784_ == 0 {
        let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1783_);
        v___x_1785_ = leanh::lean_box(0);
        v___x_1786_ =
            leanh::lean_apply_2(v_toPure_1782_, leanh::lean_box(0), v___x_1785_);
        return v___x_1786_;
    } else {
        let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1787_, 0, v_a_1783_);
        v___x_1788_ =
            leanh::lean_apply_2(v_toPure_1782_, leanh::lean_box(0), v___x_1787_);
        return v___x_1788_;
    }
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__0___boxed(
    mut v_toPure_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_____do__lift_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_77__boxed_1792_: u8 = 0;
    let mut v_res_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_77__boxed_1792_ = (leanh::lean_unbox(v_____do__lift_1791_) as u8);
    v_res_1793_ = l_Subarray_findRevM_x3f___redArg___lam__0(
        v_toPure_1789_,
        v_a_1790_,
        v_____do__lift_77__boxed_1792_,
    );
    return v_res_1793_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__1(
    mut v_toPure_1794_: *mut leanh::LeanObject,
    mut v_p_1795_: *mut leanh::LeanObject,
    mut v_toBind_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_1797_);
    v___f_1798_ = leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1798_, 0, v_toPure_1794_);
    leanh::lean_closure_set(v___f_1798_, 1, v_a_1797_);
    v___x_1799_ = leanh::lean_apply_1(v_p_1795_, v_a_1797_);
    v___x_1800_ = leanh::lean_apply_4(
        v_toBind_1796_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1799_,
        v___f_1798_,
    );
    return v___x_1800_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg(
    mut v_inst_1801_: *mut leanh::LeanObject,
    mut v_as_1802_: *mut leanh::LeanObject,
    mut v_p_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1804_ = leanh::lean_ctor_get(v_inst_1801_, 0);
    v_toBind_1805_ = leanh::lean_ctor_get(v_inst_1801_, 1);
    v_toPure_1806_ = leanh::lean_ctor_get(v_toApplicative_1804_, 1);
    v_start_1807_ = leanh::lean_ctor_get(v_as_1802_, 1);
    v_stop_1808_ = leanh::lean_ctor_get(v_as_1802_, 2);
    leanh::lean_inc(v_toBind_1805_);
    leanh::lean_inc(v_toPure_1806_);
    v___f_1809_ = leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1809_, 0, v_toPure_1806_);
    leanh::lean_closure_set(v___f_1809_, 1, v_p_1803_);
    leanh::lean_closure_set(v___f_1809_, 2, v_toBind_1805_);
    v___x_1810_ = lean_nat_sub(v_stop_1808_, v_start_1807_);
    v___x_1811_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1801_,
        v_as_1802_,
        v___f_1809_,
        v___x_1810_,
    );
    leanh::lean_dec(v___x_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Subarray_findRevM_x3f(
    mut v_00_u03b1_1812_: *mut leanh::LeanObject,
    mut v_m_1813_: *mut leanh::LeanObject,
    mut v_inst_1814_: *mut leanh::LeanObject,
    mut v_as_1815_: *mut leanh::LeanObject,
    mut v_p_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1817_ = leanh::lean_ctor_get(v_inst_1814_, 0);
    v_toBind_1818_ = leanh::lean_ctor_get(v_inst_1814_, 1);
    v_toPure_1819_ = leanh::lean_ctor_get(v_toApplicative_1817_, 1);
    v_start_1820_ = leanh::lean_ctor_get(v_as_1815_, 1);
    v_stop_1821_ = leanh::lean_ctor_get(v_as_1815_, 2);
    leanh::lean_inc(v_toBind_1818_);
    leanh::lean_inc(v_toPure_1819_);
    v___f_1822_ = leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1822_, 0, v_toPure_1819_);
    leanh::lean_closure_set(v___f_1822_, 1, v_p_1816_);
    leanh::lean_closure_set(v___f_1822_, 2, v_toBind_1818_);
    v___x_1823_ = lean_nat_sub(v_stop_1821_, v_start_1820_);
    v___x_1824_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1814_,
        v_as_1815_,
        v___f_1822_,
        v___x_1823_,
    );
    leanh::lean_dec(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Subarray_findRev_x3f___redArg___lam__0(
    mut v_p_1825_: *mut leanh::LeanObject,
    mut v_a_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    leanh::lean_inc(v_a_1826_);
    v___x_1827_ = leanh::lean_apply_1(v_p_1825_, v_a_1826_);
    v___x_1828_ = (leanh::lean_unbox(v___x_1827_) as u8);
    if v___x_1828_ == 0 {
        let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1826_);
        v___x_1829_ = leanh::lean_box(0);
        return v___x_1829_;
    } else {
        let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1830_, 0, v_a_1826_);
        return v___x_1830_;
    }
}
pub unsafe fn l_Subarray_findRev_x3f___redArg(
    mut v_as_1831_: *mut leanh::LeanObject,
    mut v_p_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Subarray_foldr___redArg___closed__9;
    v_start_1834_ = leanh::lean_ctor_get(v_as_1831_, 1);
    v_stop_1835_ = leanh::lean_ctor_get(v_as_1831_, 2);
    v___f_1836_ = leanh::lean_alloc_closure(
        l_Subarray_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1836_, 0, v_p_1832_);
    v___x_1837_ = lean_nat_sub(v_stop_1835_, v_start_1834_);
    v___x_1838_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v___x_1833_,
        v_as_1831_,
        v___f_1836_,
        v___x_1837_,
    );
    leanh::lean_dec(v___x_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Subarray_findRev_x3f(
    mut v_00_u03b1_1839_: *mut leanh::LeanObject,
    mut v_as_1840_: *mut leanh::LeanObject,
    mut v_p_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Subarray_foldr___redArg___closed__9;
    v_start_1843_ = leanh::lean_ctor_get(v_as_1840_, 1);
    v_stop_1844_ = leanh::lean_ctor_get(v_as_1840_, 2);
    v___f_1845_ = leanh::lean_alloc_closure(
        l_Subarray_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1845_, 0, v_p_1841_);
    v___x_1846_ = lean_nat_sub(v_stop_1844_, v_start_1843_);
    v___x_1847_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v___x_1842_,
        v_as_1840_,
        v___f_1845_,
        v___x_1846_,
    );
    leanh::lean_dec(v___x_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Array_toSubarray___redArg(
    mut v_as_1848_: *mut leanh::LeanObject,
    mut v_start_1849_: *mut leanh::LeanObject,
    mut v_stop_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    v___x_1851_ = lean_array_get_size(v_as_1848_);
    v___x_1852_ = lean_nat_dec_le(v_stop_1850_, v___x_1851_);
    if v___x_1852_ == 0 {
        let mut v___x_1853_: u8 = 0;
        leanh::lean_dec(v_stop_1850_);
        v___x_1853_ = lean_nat_dec_le(v_start_1849_, v___x_1851_);
        if v___x_1853_ == 0 {
            let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_start_1849_);
            v___x_1854_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1854_, 0, v_as_1848_);
            leanh::lean_ctor_set(v___x_1854_, 1, v___x_1851_);
            leanh::lean_ctor_set(v___x_1854_, 2, v___x_1851_);
            return v___x_1854_;
        } else {
            let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1855_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1855_, 0, v_as_1848_);
            leanh::lean_ctor_set(v___x_1855_, 1, v_start_1849_);
            leanh::lean_ctor_set(v___x_1855_, 2, v___x_1851_);
            return v___x_1855_;
        }
    } else {
        let mut v___x_1856_: u8 = 0;
        v___x_1856_ = lean_nat_dec_le(v_start_1849_, v_stop_1850_);
        if v___x_1856_ == 0 {
            let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_start_1849_);
            leanh::lean_inc(v_stop_1850_);
            v___x_1857_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1857_, 0, v_as_1848_);
            leanh::lean_ctor_set(v___x_1857_, 1, v_stop_1850_);
            leanh::lean_ctor_set(v___x_1857_, 2, v_stop_1850_);
            return v___x_1857_;
        } else {
            let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1858_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1858_, 0, v_as_1848_);
            leanh::lean_ctor_set(v___x_1858_, 1, v_start_1849_);
            leanh::lean_ctor_set(v___x_1858_, 2, v_stop_1850_);
            return v___x_1858_;
        }
    }
}
pub unsafe fn l_Array_toSubarray(
    mut v_00_u03b1_1859_: *mut leanh::LeanObject,
    mut v_as_1860_: *mut leanh::LeanObject,
    mut v_start_1861_: *mut leanh::LeanObject,
    mut v_stop_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Array_toSubarray___redArg(v_as_1860_, v_start_1861_, v_stop_1862_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5;
    v___x_1981_ = l_String_toRawSubstring_x27(v___x_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(
    mut v_x_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
    mut v_a_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    v___x_1998_ = l_Array_term_____x5b___x3a___x5d___closed__2;
    leanh::lean_inc(v_x_1995_);
    v___x_1999_ = l_Lean_Syntax_isOfKind(v_x_1995_, v___x_1998_);
    if v___x_1999_ == 0 {
        let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1995_);
        v___x_2000_ = leanh::lean_box(1);
        v___x_2001_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2001_, 0, v___x_2000_);
        leanh::lean_ctor_set(v___x_2001_, 1, v_a_1997_);
        return v___x_2001_;
    } else {
        let mut v_quotContext_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: u8 = 0;
        let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2002_ = leanh::lean_ctor_get(v_a_1996_, 1);
        v_currMacroScope_2003_ = leanh::lean_ctor_get(v_a_1996_, 2);
        v_ref_2004_ = leanh::lean_ctor_get(v_a_1996_, 5);
        v___x_2005_ = leanh::lean_unsigned_to_nat(0);
        v___x_2006_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2005_);
        v___x_2007_ = leanh::lean_unsigned_to_nat(2);
        v___x_2008_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2007_);
        v___x_2009_ = leanh::lean_unsigned_to_nat(4);
        v___x_2010_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2009_);
        leanh::lean_dec(v_x_1995_);
        v___x_2011_ = 0;
        v___x_2012_ = l_Lean_SourceInfo_fromRef(v_ref_2004_, v___x_2011_);
        v___x_2013_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2015_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        leanh::lean_inc(v_currMacroScope_2003_);
        leanh::lean_inc(v_quotContext_2002_);
        v___x_2016_ =
            l_Lean_addMacroScope(v_quotContext_2002_, v___x_2015_, v_currMacroScope_2003_);
        v___x_2017_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10;
        leanh::lean_inc_n(v___x_2012_, 2);
        v___x_2018_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2018_, 0, v___x_2012_);
        leanh::lean_ctor_set(v___x_2018_, 1, v___x_2014_);
        leanh::lean_ctor_set(v___x_2018_, 2, v___x_2016_);
        leanh::lean_ctor_set(v___x_2018_, 3, v___x_2017_);
        v___x_2019_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2020_ = l_Lean_Syntax_node3(
            v___x_2012_,
            v___x_2019_,
            v___x_2006_,
            v___x_2008_,
            v___x_2010_,
        );
        v___x_2021_ = l_Lean_Syntax_node2(v___x_2012_, v___x_2013_, v___x_2018_, v___x_2020_);
        v___x_2022_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
        leanh::lean_ctor_set(v___x_2022_, 1, v_a_1997_);
        return v___x_2022_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(
    mut v_x_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
    mut v_a_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_2023_, v_a_2024_, v_a_2025_);
    leanh::lean_dec_ref(v_a_2024_);
    return v_res_2026_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(
    mut v_x_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
    mut v_a_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    v___x_2034_ = l_Array_term_____x5b_x3a___x5d___closed__1;
    leanh::lean_inc(v_x_2031_);
    v___x_2035_ = l_Lean_Syntax_isOfKind(v_x_2031_, v___x_2034_);
    if v___x_2035_ == 0 {
        let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2031_);
        v___x_2036_ = leanh::lean_box(1);
        v___x_2037_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2037_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2037_, 1, v_a_2033_);
        return v___x_2037_;
    } else {
        let mut v_quotContext_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: u8 = 0;
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2038_ = leanh::lean_ctor_get(v_a_2032_, 1);
        v_currMacroScope_2039_ = leanh::lean_ctor_get(v_a_2032_, 2);
        v_ref_2040_ = leanh::lean_ctor_get(v_a_2032_, 5);
        v___x_2041_ = leanh::lean_unsigned_to_nat(0);
        v___x_2042_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2041_);
        v___x_2043_ = leanh::lean_unsigned_to_nat(3);
        v___x_2044_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2043_);
        leanh::lean_dec(v_x_2031_);
        v___x_2045_ = 0;
        v___x_2046_ = l_Lean_SourceInfo_fromRef(v_ref_2040_, v___x_2045_);
        v___x_2047_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2049_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        leanh::lean_inc(v_currMacroScope_2039_);
        leanh::lean_inc(v_quotContext_2038_);
        v___x_2050_ =
            l_Lean_addMacroScope(v_quotContext_2038_, v___x_2049_, v_currMacroScope_2039_);
        v___x_2051_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10;
        leanh::lean_inc_n(v___x_2046_, 4);
        v___x_2052_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2052_, 0, v___x_2046_);
        leanh::lean_ctor_set(v___x_2052_, 1, v___x_2048_);
        leanh::lean_ctor_set(v___x_2052_, 2, v___x_2050_);
        leanh::lean_ctor_set(v___x_2052_, 3, v___x_2051_);
        v___x_2053_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2054_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1;
        v___x_2055_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2;
        v___x_2056_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2056_, 0, v___x_2046_);
        leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        v___x_2057_ = l_Lean_Syntax_node1(v___x_2046_, v___x_2054_, v___x_2056_);
        v___x_2058_ = l_Lean_Syntax_node3(
            v___x_2046_,
            v___x_2053_,
            v___x_2042_,
            v___x_2057_,
            v___x_2044_,
        );
        v___x_2059_ = l_Lean_Syntax_node2(v___x_2046_, v___x_2047_, v___x_2052_, v___x_2058_);
        v___x_2060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
        leanh::lean_ctor_set(v___x_2060_, 1, v_a_2033_);
        return v___x_2060_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(
    mut v_x_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_2061_, v_a_2062_, v_a_2063_);
    leanh::lean_dec_ref(v_a_2062_);
    return v_res_2064_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2077_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11;
    v___x_2098_ = l_String_toRawSubstring_x27(v___x_2097_);
    return v___x_2098_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18;
    v___x_2111_ = l_String_toRawSubstring_x27(v___x_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(
    mut v_x_2116_: *mut leanh::LeanObject,
    mut v_a_2117_: *mut leanh::LeanObject,
    mut v_a_2118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    v___x_2119_ = l_Array_term_____x5b___x3a_x5d___closed__1;
    leanh::lean_inc(v_x_2116_);
    v___x_2120_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2119_);
    if v___x_2120_ == 0 {
        let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2116_);
        v___x_2121_ = leanh::lean_box(1);
        v___x_2122_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
        leanh::lean_ctor_set(v___x_2122_, 1, v_a_2118_);
        return v___x_2122_;
    } else {
        let mut v_quotContext_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: u8 = 0;
        let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2123_ = leanh::lean_ctor_get(v_a_2117_, 1);
        v_currMacroScope_2124_ = leanh::lean_ctor_get(v_a_2117_, 2);
        v_ref_2125_ = leanh::lean_ctor_get(v_a_2117_, 5);
        v___x_2126_ = leanh::lean_unsigned_to_nat(0);
        v___x_2127_ = l_Lean_Syntax_getArg(v_x_2116_, v___x_2126_);
        v___x_2128_ = leanh::lean_unsigned_to_nat(2);
        v___x_2129_ = l_Lean_Syntax_getArg(v_x_2116_, v___x_2128_);
        leanh::lean_dec(v_x_2116_);
        v___x_2130_ = 0;
        v___x_2131_ = l_Lean_SourceInfo_fromRef(v_ref_2125_, v___x_2130_);
        v___x_2132_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0;
        v___x_2133_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1;
        leanh::lean_inc_n(v___x_2131_, 13);
        v___x_2134_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2134_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2134_, 1, v___x_2132_);
        v___x_2135_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3;
        v___x_2136_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2137_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
        v___x_2138_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2138_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2138_, 1, v___x_2136_);
        leanh::lean_ctor_set(v___x_2138_, 2, v___x_2137_);
        leanh::lean_inc_ref_n(v___x_2138_, 2);
        v___x_2139_ = l_Lean_Syntax_node1(v___x_2131_, v___x_2135_, v___x_2138_);
        v___x_2140_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6;
        v___x_2141_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8;
        v___x_2142_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10;
        v___x_2143_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
        v___x_2144_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13;
        leanh::lean_inc_n(v_currMacroScope_2124_, 3);
        leanh::lean_inc_n(v_quotContext_2123_, 3);
        v___x_2145_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2144_, v_currMacroScope_2124_);
        v___x_2146_ = leanh::lean_box(0);
        v___x_2147_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2147_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2147_, 1, v___x_2143_);
        leanh::lean_ctor_set(v___x_2147_, 2, v___x_2145_);
        leanh::lean_ctor_set(v___x_2147_, 3, v___x_2146_);
        leanh::lean_inc_ref(v___x_2147_);
        v___x_2148_ = l_Lean_Syntax_node1(v___x_2131_, v___x_2142_, v___x_2147_);
        v___x_2149_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14;
        v___x_2150_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2150_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
        v___x_2151_ = l_Lean_Syntax_node5(
            v___x_2131_,
            v___x_2141_,
            v___x_2148_,
            v___x_2138_,
            v___x_2138_,
            v___x_2150_,
            v___x_2127_,
        );
        v___x_2152_ = l_Lean_Syntax_node1(v___x_2131_, v___x_2140_, v___x_2151_);
        v___x_2153_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15;
        v___x_2154_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2154_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2154_, 1, v___x_2153_);
        v___x_2155_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2156_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2157_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        v___x_2158_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2157_, v_currMacroScope_2124_);
        v___x_2159_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17;
        v___x_2160_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2160_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2160_, 1, v___x_2156_);
        leanh::lean_ctor_set(v___x_2160_, 2, v___x_2158_);
        leanh::lean_ctor_set(v___x_2160_, 3, v___x_2159_);
        v___x_2161_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
        v___x_2162_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21;
        v___x_2163_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2162_, v_currMacroScope_2124_);
        v___x_2164_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2164_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2164_, 1, v___x_2161_);
        leanh::lean_ctor_set(v___x_2164_, 2, v___x_2163_);
        leanh::lean_ctor_set(v___x_2164_, 3, v___x_2146_);
        v___x_2165_ = l_Lean_Syntax_node3(
            v___x_2131_,
            v___x_2136_,
            v___x_2147_,
            v___x_2129_,
            v___x_2164_,
        );
        v___x_2166_ = l_Lean_Syntax_node2(v___x_2131_, v___x_2155_, v___x_2160_, v___x_2165_);
        v___x_2167_ = l_Lean_Syntax_node5(
            v___x_2131_,
            v___x_2133_,
            v___x_2134_,
            v___x_2139_,
            v___x_2152_,
            v___x_2154_,
            v___x_2166_,
        );
        v___x_2168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2168_, 0, v___x_2167_);
        leanh::lean_ctor_set(v___x_2168_, 1, v_a_2118_);
        return v___x_2168_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(
    mut v_x_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_2169_, v_a_2170_, v_a_2171_);
    leanh::lean_dec_ref(v_a_2170_);
    return v_res_2172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Subarray(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Subarray(
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
pub unsafe fn initialize_Init_Data_Array_Subarray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Subarray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Subarray(builtin);
}