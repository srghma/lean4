// Lean compiler output
// Module: Init.Data.Array.Subarray
// Imports: Init.Data.Array.Basic Init.Data.Slice.Operations
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
use crate::ffi::lean_usize_of_nat;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub,
};
pub static l_Subarray_instSliceSizeSubarrayData___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Subarray_instSliceSizeSubarrayData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Subarray_instSliceSizeSubarrayData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_instSliceSizeSubarrayData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value:
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
    m_fun: l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Subarray_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_empty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Subarray_empty___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Subarray_empty___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Subarray_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_empty___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Subarray_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Subarray_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Subarray_foldr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_foldr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_foldr___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Subarray_foldr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_foldr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [65, 114, 114, 97, 121, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8749134177695247953 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b___x3a___x5d___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15207914032045756441 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
            1581446985683836252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__8_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__11_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__11_value)
                as *mut crate::leanh::LeanObject,
            1164644006045091397 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__13_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__14_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__16_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__20_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__21_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__22_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a___x5d___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__24_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__21_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a___x5d___closed__25_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a___x5d___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Array_term_____x5b___x3a___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b___x3a_x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8749134177695247953 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b___x3a_x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14055661608840943147 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b___x3a_x5d___closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b___x3a_x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Array_term_____x5b___x3a_x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b___x3a_x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_term_____x5b_x3a___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8749134177695247953 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Array_term_____x5b_x3a___x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8389090204557134608 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_term_____x5b_x3a___x5d___closed__6_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_term_____x5b_x3a___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Array_term_____x5b_x3a___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term_____x5b_x3a___x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [65, 114, 114, 97, 121, 46, 116, 111, 83, 117, 98, 97, 114, 114, 97, 121, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 117, 98, 97, 114, 114, 97, 121, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_term_____x5b___x3a___x5d___closed__0_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__7_value) as *mut crate::leanh::LeanObject,4159008167141249932 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__11_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,146480343229376155 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,17404204824591055365 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__5_value) as *mut crate::leanh::LeanObject,8036185514257755965 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__7_value) as *mut crate::leanh::LeanObject,17116161260408496210 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__9_value) as *mut crate::leanh::LeanObject,13708106407786339395 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__16_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 46, 115, 105, 122, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 122, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value) as *mut crate::leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__20_value) as *mut crate::leanh::LeanObject,2164234508552290018 as *mut crate::leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Subarray_array___redArg(
    mut v_xs_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1088_ = crate::leanh::lean_ctor_get(v_xs_1087_, 0);
    crate::leanh::lean_inc_ref(v_array_1088_);
    return v_array_1088_;
}
pub unsafe fn l_Subarray_array___redArg___boxed(
    mut v_xs_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Subarray_array___redArg(v_xs_1089_);
    crate::leanh::lean_dec_ref(v_xs_1089_);
    return v_res_1090_;
}
pub unsafe fn l_Subarray_array(
    mut v_00_u03b1_1091_: *mut crate::leanh::LeanObject,
    mut v_xs_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1093_ = crate::leanh::lean_ctor_get(v_xs_1092_, 0);
    crate::leanh::lean_inc_ref(v_array_1093_);
    return v_array_1093_;
}
pub unsafe fn l_Subarray_array___boxed(
    mut v_00_u03b1_1094_: *mut crate::leanh::LeanObject,
    mut v_xs_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Subarray_array(v_00_u03b1_1094_, v_xs_1095_);
    crate::leanh::lean_dec_ref(v_xs_1095_);
    return v_res_1096_;
}
pub unsafe fn l_Subarray_start___redArg(
    mut v_xs_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_1098_ = crate::leanh::lean_ctor_get(v_xs_1097_, 1);
    crate::leanh::lean_inc(v_start_1098_);
    return v_start_1098_;
}
pub unsafe fn l_Subarray_start___redArg___boxed(
    mut v_xs_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1100_ = l_Subarray_start___redArg(v_xs_1099_);
    crate::leanh::lean_dec_ref(v_xs_1099_);
    return v_res_1100_;
}
pub unsafe fn l_Subarray_start(
    mut v_00_u03b1_1101_: *mut crate::leanh::LeanObject,
    mut v_xs_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_1103_ = crate::leanh::lean_ctor_get(v_xs_1102_, 1);
    crate::leanh::lean_inc(v_start_1103_);
    return v_start_1103_;
}
pub unsafe fn l_Subarray_start___boxed(
    mut v_00_u03b1_1104_: *mut crate::leanh::LeanObject,
    mut v_xs_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Subarray_start(v_00_u03b1_1104_, v_xs_1105_);
    crate::leanh::lean_dec_ref(v_xs_1105_);
    return v_res_1106_;
}
pub unsafe fn l_Subarray_stop___redArg(
    mut v_xs_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stop_1108_ = crate::leanh::lean_ctor_get(v_xs_1107_, 2);
    crate::leanh::lean_inc(v_stop_1108_);
    return v_stop_1108_;
}
pub unsafe fn l_Subarray_stop___redArg___boxed(
    mut v_xs_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Subarray_stop___redArg(v_xs_1109_);
    crate::leanh::lean_dec_ref(v_xs_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Subarray_stop(
    mut v_00_u03b1_1111_: *mut crate::leanh::LeanObject,
    mut v_xs_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stop_1113_ = crate::leanh::lean_ctor_get(v_xs_1112_, 2);
    crate::leanh::lean_inc(v_stop_1113_);
    return v_stop_1113_;
}
pub unsafe fn l_Subarray_stop___boxed(
    mut v_00_u03b1_1114_: *mut crate::leanh::LeanObject,
    mut v_xs_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Subarray_stop(v_00_u03b1_1114_, v_xs_1115_);
    crate::leanh::lean_dec_ref(v_xs_1115_);
    return v_res_1116_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData___lam__0(
    mut v_s_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_1118_ = crate::leanh::lean_ctor_get(v_s_1117_, 1);
    v_stop_1119_ = crate::leanh::lean_ctor_get(v_s_1117_, 2);
    v___x_1120_ = lean_nat_sub(v_stop_1119_, v_start_1118_);
    return v___x_1120_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData___lam__0___boxed(
    mut v_s_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Subarray_instSliceSizeSubarrayData___lam__0(v_s_1121_);
    crate::leanh::lean_dec_ref(v_s_1121_);
    return v_res_1122_;
}
pub unsafe fn l_Subarray_instSliceSizeSubarrayData(
    mut v_00_u03b1_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1125_ = l_Subarray_instSliceSizeSubarrayData___closed__0;
    return v___f_1125_;
}
pub unsafe fn l_Subarray_get___redArg(
    mut v_s_1126_: *mut crate::leanh::LeanObject,
    mut v_i_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1128_ = crate::leanh::lean_ctor_get(v_s_1126_, 0);
    v_start_1129_ = crate::leanh::lean_ctor_get(v_s_1126_, 1);
    v___x_1130_ = lean_nat_add(v_start_1129_, v_i_1127_);
    v___x_1131_ = lean_array_fget_borrowed(v_array_1128_, v___x_1130_);
    crate::leanh::lean_dec(v___x_1130_);
    crate::leanh::lean_inc(v___x_1131_);
    return v___x_1131_;
}
pub unsafe fn l_Subarray_get___redArg___boxed(
    mut v_s_1132_: *mut crate::leanh::LeanObject,
    mut v_i_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Subarray_get___redArg(v_s_1132_, v_i_1133_);
    crate::leanh::lean_dec(v_i_1133_);
    crate::leanh::lean_dec_ref(v_s_1132_);
    return v_res_1134_;
}
pub unsafe fn l_Subarray_get(
    mut v_00_u03b1_1135_: *mut crate::leanh::LeanObject,
    mut v_s_1136_: *mut crate::leanh::LeanObject,
    mut v_i_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = l_Subarray_get___redArg(v_s_1136_, v_i_1137_);
    return v___x_1138_;
}
pub unsafe fn l_Subarray_get___boxed(
    mut v_00_u03b1_1139_: *mut crate::leanh::LeanObject,
    mut v_s_1140_: *mut crate::leanh::LeanObject,
    mut v_i_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Subarray_get(v_00_u03b1_1139_, v_s_1140_, v_i_1141_);
    crate::leanh::lean_dec(v_i_1141_);
    crate::leanh::lean_dec_ref(v_s_1140_);
    return v_res_1142_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(
    mut v_xs_1143_: *mut crate::leanh::LeanObject,
    mut v_i_1144_: *mut crate::leanh::LeanObject,
    mut v_h_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Subarray_get___redArg(v_xs_1143_, v_i_1144_);
    return v___x_1146_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0___boxed(
    mut v_xs_1147_: *mut crate::leanh::LeanObject,
    mut v_i_1148_: *mut crate::leanh::LeanObject,
    mut v_h_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ =
        l_Subarray_instGetElemNatLtSizeSubarrayData___lam__0(v_xs_1147_, v_i_1148_, v_h_1149_);
    crate::leanh::lean_dec(v_i_1148_);
    crate::leanh::lean_dec_ref(v_xs_1147_);
    return v_res_1150_;
}
pub unsafe fn l_Subarray_instGetElemNatLtSizeSubarrayData(
    mut v_00_u03b1_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1153_ = l_Subarray_instGetElemNatLtSizeSubarrayData___closed__0;
    return v___f_1153_;
}
pub unsafe fn l_Subarray_getD___redArg(
    mut v_s_1154_: *mut crate::leanh::LeanObject,
    mut v_i_1155_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    v_start_1157_ = crate::leanh::lean_ctor_get(v_s_1154_, 1);
    v_stop_1158_ = crate::leanh::lean_ctor_get(v_s_1154_, 2);
    v___x_1159_ = lean_nat_sub(v_stop_1158_, v_start_1157_);
    v___x_1160_ = lean_nat_dec_lt(v_i_1155_, v___x_1159_);
    crate::leanh::lean_dec(v___x_1159_);
    if v___x_1160_ == 0 {
        crate::leanh::lean_inc(v_v_u2080_1156_);
        return v_v_u2080_1156_;
    } else {
        let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1161_ = l_Subarray_get___redArg(v_s_1154_, v_i_1155_);
        return v___x_1161_;
    }
}
pub unsafe fn l_Subarray_getD___redArg___boxed(
    mut v_s_1162_: *mut crate::leanh::LeanObject,
    mut v_i_1163_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Subarray_getD___redArg(v_s_1162_, v_i_1163_, v_v_u2080_1164_);
    crate::leanh::lean_dec(v_v_u2080_1164_);
    crate::leanh::lean_dec(v_i_1163_);
    crate::leanh::lean_dec_ref(v_s_1162_);
    return v_res_1165_;
}
pub unsafe fn l_Subarray_getD(
    mut v_00_u03b1_1166_: *mut crate::leanh::LeanObject,
    mut v_s_1167_: *mut crate::leanh::LeanObject,
    mut v_i_1168_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: u8 = 0;
    v_start_1170_ = crate::leanh::lean_ctor_get(v_s_1167_, 1);
    v_stop_1171_ = crate::leanh::lean_ctor_get(v_s_1167_, 2);
    v___x_1172_ = lean_nat_sub(v_stop_1171_, v_start_1170_);
    v___x_1173_ = lean_nat_dec_lt(v_i_1168_, v___x_1172_);
    crate::leanh::lean_dec(v___x_1172_);
    if v___x_1173_ == 0 {
        crate::leanh::lean_inc(v_v_u2080_1169_);
        return v_v_u2080_1169_;
    } else {
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1174_ = l_Subarray_get___redArg(v_s_1167_, v_i_1168_);
        return v___x_1174_;
    }
}
pub unsafe fn l_Subarray_getD___boxed(
    mut v_00_u03b1_1175_: *mut crate::leanh::LeanObject,
    mut v_s_1176_: *mut crate::leanh::LeanObject,
    mut v_i_1177_: *mut crate::leanh::LeanObject,
    mut v_v_u2080_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Subarray_getD(v_00_u03b1_1175_, v_s_1176_, v_i_1177_, v_v_u2080_1178_);
    crate::leanh::lean_dec(v_v_u2080_1178_);
    crate::leanh::lean_dec(v_i_1177_);
    crate::leanh::lean_dec_ref(v_s_1176_);
    return v_res_1179_;
}
pub unsafe fn l_Subarray_get_x21___redArg(
    mut v_inst_1180_: *mut crate::leanh::LeanObject,
    mut v_s_1181_: *mut crate::leanh::LeanObject,
    mut v_i_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: u8 = 0;
    v_start_1183_ = crate::leanh::lean_ctor_get(v_s_1181_, 1);
    v_stop_1184_ = crate::leanh::lean_ctor_get(v_s_1181_, 2);
    v___x_1185_ = lean_nat_sub(v_stop_1184_, v_start_1183_);
    v___x_1186_ = lean_nat_dec_lt(v_i_1182_, v___x_1185_);
    crate::leanh::lean_dec(v___x_1185_);
    if v___x_1186_ == 0 {
        crate::leanh::lean_inc(v_inst_1180_);
        return v_inst_1180_;
    } else {
        let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1187_ = l_Subarray_get___redArg(v_s_1181_, v_i_1182_);
        return v___x_1187_;
    }
}
pub unsafe fn l_Subarray_get_x21___redArg___boxed(
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
    mut v_s_1189_: *mut crate::leanh::LeanObject,
    mut v_i_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Subarray_get_x21___redArg(v_inst_1188_, v_s_1189_, v_i_1190_);
    crate::leanh::lean_dec(v_i_1190_);
    crate::leanh::lean_dec_ref(v_s_1189_);
    crate::leanh::lean_dec(v_inst_1188_);
    return v_res_1191_;
}
pub unsafe fn l_Subarray_get_x21(
    mut v_00_u03b1_1192_: *mut crate::leanh::LeanObject,
    mut v_inst_1193_: *mut crate::leanh::LeanObject,
    mut v_s_1194_: *mut crate::leanh::LeanObject,
    mut v_i_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    v_start_1196_ = crate::leanh::lean_ctor_get(v_s_1194_, 1);
    v_stop_1197_ = crate::leanh::lean_ctor_get(v_s_1194_, 2);
    v___x_1198_ = lean_nat_sub(v_stop_1197_, v_start_1196_);
    v___x_1199_ = lean_nat_dec_lt(v_i_1195_, v___x_1198_);
    crate::leanh::lean_dec(v___x_1198_);
    if v___x_1199_ == 0 {
        crate::leanh::lean_inc(v_inst_1193_);
        return v_inst_1193_;
    } else {
        let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1200_ = l_Subarray_get___redArg(v_s_1194_, v_i_1195_);
        return v___x_1200_;
    }
}
pub unsafe fn l_Subarray_get_x21___boxed(
    mut v_00_u03b1_1201_: *mut crate::leanh::LeanObject,
    mut v_inst_1202_: *mut crate::leanh::LeanObject,
    mut v_s_1203_: *mut crate::leanh::LeanObject,
    mut v_i_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Subarray_get_x21(v_00_u03b1_1201_, v_inst_1202_, v_s_1203_, v_i_1204_);
    crate::leanh::lean_dec(v_i_1204_);
    crate::leanh::lean_dec_ref(v_s_1203_);
    crate::leanh::lean_dec(v_inst_1202_);
    return v_res_1205_;
}
pub unsafe fn l_Subarray_popFront___redArg(
    mut v_s_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_unused_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1207_ = crate::leanh::lean_ctor_get(v_s_1206_, 0);
                v_start_1208_ = crate::leanh::lean_ctor_get(v_s_1206_, 1);
                v_stop_1209_ = crate::leanh::lean_ctor_get(v_s_1206_, 2);
                v___x_1210_ = lean_nat_dec_lt(v_start_1208_, v_stop_1209_);
                if v___x_1210_ == 0 {
                    return v_s_1206_;
                } else {
                    crate::leanh::lean_inc(v_stop_1209_);
                    crate::leanh::lean_inc(v_start_1208_);
                    crate::leanh::lean_inc_ref(v_array_1207_);
                    v_isSharedCheck_1219_ = (!crate::leanh::lean_is_exclusive(v_s_1206_)) as u8;
                    if v_isSharedCheck_1219_ == 0 {
                        v_unused_1220_ = crate::leanh::lean_ctor_get(v_s_1206_, 2);
                        crate::leanh::lean_dec(v_unused_1220_);
                        v_unused_1221_ = crate::leanh::lean_ctor_get(v_s_1206_, 1);
                        crate::leanh::lean_dec(v_unused_1221_);
                        v_unused_1222_ = crate::leanh::lean_ctor_get(v_s_1206_, 0);
                        crate::leanh::lean_dec(v_unused_1222_);
                        v___x_1212_ = v_s_1206_;
                        v_isShared_1213_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_1206_);
                        v___x_1212_ = crate::leanh::lean_box(0);
                        v_isShared_1213_ = v_isSharedCheck_1219_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1214_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1215_ = lean_nat_add(v_start_1208_, v___x_1214_);
                crate::leanh::lean_dec(v_start_1208_);
                if v_isShared_1213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1215_);
                    v___x_1217_ = v___x_1212_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1218_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_array_1207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_stop_1209_);
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
    mut v_00_u03b1_1223_: *mut crate::leanh::LeanObject,
    mut v_s_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = l_Subarray_popFront___redArg(v_s_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Subarray_empty(
    mut v_00_u03b1_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Subarray_empty___closed__1;
    return v___x_1232_;
}
pub unsafe fn _init_l_Subarray_instEmptyCollection___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Subarray_empty(crate::leanh::lean_box(0));
    return v___x_1233_;
}
pub unsafe fn l_Subarray_instEmptyCollection(
    mut v_00_u03b1_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0_once),
        _init_l_Subarray_instEmptyCollection___closed__0,
    );
    return v___x_1235_;
}
pub unsafe fn l_Subarray_instInhabited(
    mut v_00_u03b1_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Subarray_instEmptyCollection___closed__0_once),
        _init_l_Subarray_instEmptyCollection___closed__0,
    );
    return v___x_1237_;
}
pub unsafe fn l_Subarray_foldrM___redArg(
    mut v_inst_1238_: *mut crate::leanh::LeanObject,
    mut v_f_1239_: *mut crate::leanh::LeanObject,
    mut v_init_1240_: *mut crate::leanh::LeanObject,
    mut v_as_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: u8 = 0;
    v_array_1242_ = crate::leanh::lean_ctor_get(v_as_1241_, 0);
    crate::leanh::lean_inc_ref(v_array_1242_);
    v_start_1243_ = crate::leanh::lean_ctor_get(v_as_1241_, 1);
    crate::leanh::lean_inc(v_start_1243_);
    v_stop_1244_ = crate::leanh::lean_ctor_get(v_as_1241_, 2);
    crate::leanh::lean_inc(v_stop_1244_);
    crate::leanh::lean_dec_ref(v_as_1241_);
    v___x_1245_ = lean_array_get_size(v_array_1242_);
    v___x_1246_ = lean_nat_dec_le(v_stop_1244_, v___x_1245_);
    if v___x_1246_ == 0 {
        let mut v___x_1247_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1244_);
        v___x_1247_ = lean_nat_dec_lt(v_start_1243_, v___x_1245_);
        if v___x_1247_ == 0 {
            let mut v_toApplicative_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_start_1243_);
            crate::leanh::lean_dec_ref(v_array_1242_);
            crate::leanh::lean_dec(v_f_1239_);
            v_toApplicative_1248_ = crate::leanh::lean_ctor_get(v_inst_1238_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1248_);
            crate::leanh::lean_dec_ref(v_inst_1238_);
            v_toPure_1249_ = crate::leanh::lean_ctor_get(v_toApplicative_1248_, 1);
            crate::leanh::lean_inc(v_toPure_1249_);
            crate::leanh::lean_dec_ref(v_toApplicative_1248_);
            v___x_1250_ =
                crate::leanh::lean_apply_2(v_toPure_1249_, crate::leanh::lean_box(0), v_init_1240_);
            return v___x_1250_;
        } else {
            let mut v___x_1251_: usize = 0;
            let mut v___x_1252_: usize = 0;
            let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1251_ = lean_usize_of_nat(v___x_1245_);
            v___x_1252_ = lean_usize_of_nat(v_start_1243_);
            crate::leanh::lean_dec(v_start_1243_);
            v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            let mut v_toApplicative_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_stop_1244_);
            crate::leanh::lean_dec(v_start_1243_);
            crate::leanh::lean_dec_ref(v_array_1242_);
            crate::leanh::lean_dec(v_f_1239_);
            v_toApplicative_1255_ = crate::leanh::lean_ctor_get(v_inst_1238_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1255_);
            crate::leanh::lean_dec_ref(v_inst_1238_);
            v_toPure_1256_ = crate::leanh::lean_ctor_get(v_toApplicative_1255_, 1);
            crate::leanh::lean_inc(v_toPure_1256_);
            crate::leanh::lean_dec_ref(v_toApplicative_1255_);
            v___x_1257_ =
                crate::leanh::lean_apply_2(v_toPure_1256_, crate::leanh::lean_box(0), v_init_1240_);
            return v___x_1257_;
        } else {
            let mut v___x_1258_: usize = 0;
            let mut v___x_1259_: usize = 0;
            let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1258_ = lean_usize_of_nat(v_stop_1244_);
            crate::leanh::lean_dec(v_stop_1244_);
            v___x_1259_ = lean_usize_of_nat(v_start_1243_);
            crate::leanh::lean_dec(v_start_1243_);
            v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1262_: *mut crate::leanh::LeanObject,
    mut v_m_1263_: *mut crate::leanh::LeanObject,
    mut v_inst_1264_: *mut crate::leanh::LeanObject,
    mut v_f_1265_: *mut crate::leanh::LeanObject,
    mut v_init_1266_: *mut crate::leanh::LeanObject,
    mut v_as_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: u8 = 0;
    v_array_1268_ = crate::leanh::lean_ctor_get(v_as_1267_, 0);
    crate::leanh::lean_inc_ref(v_array_1268_);
    v_start_1269_ = crate::leanh::lean_ctor_get(v_as_1267_, 1);
    crate::leanh::lean_inc(v_start_1269_);
    v_stop_1270_ = crate::leanh::lean_ctor_get(v_as_1267_, 2);
    crate::leanh::lean_inc(v_stop_1270_);
    crate::leanh::lean_dec_ref(v_as_1267_);
    v___x_1271_ = lean_array_get_size(v_array_1268_);
    v___x_1272_ = lean_nat_dec_le(v_stop_1270_, v___x_1271_);
    if v___x_1272_ == 0 {
        let mut v___x_1273_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1270_);
        v___x_1273_ = lean_nat_dec_lt(v_start_1269_, v___x_1271_);
        if v___x_1273_ == 0 {
            let mut v_toApplicative_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_start_1269_);
            crate::leanh::lean_dec_ref(v_array_1268_);
            crate::leanh::lean_dec(v_f_1265_);
            v_toApplicative_1274_ = crate::leanh::lean_ctor_get(v_inst_1264_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1274_);
            crate::leanh::lean_dec_ref(v_inst_1264_);
            v_toPure_1275_ = crate::leanh::lean_ctor_get(v_toApplicative_1274_, 1);
            crate::leanh::lean_inc(v_toPure_1275_);
            crate::leanh::lean_dec_ref(v_toApplicative_1274_);
            v___x_1276_ =
                crate::leanh::lean_apply_2(v_toPure_1275_, crate::leanh::lean_box(0), v_init_1266_);
            return v___x_1276_;
        } else {
            let mut v___x_1277_: usize = 0;
            let mut v___x_1278_: usize = 0;
            let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1277_ = lean_usize_of_nat(v___x_1271_);
            v___x_1278_ = lean_usize_of_nat(v_start_1269_);
            crate::leanh::lean_dec(v_start_1269_);
            v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            let mut v_toApplicative_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_stop_1270_);
            crate::leanh::lean_dec(v_start_1269_);
            crate::leanh::lean_dec_ref(v_array_1268_);
            crate::leanh::lean_dec(v_f_1265_);
            v_toApplicative_1281_ = crate::leanh::lean_ctor_get(v_inst_1264_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1281_);
            crate::leanh::lean_dec_ref(v_inst_1264_);
            v_toPure_1282_ = crate::leanh::lean_ctor_get(v_toApplicative_1281_, 1);
            crate::leanh::lean_inc(v_toPure_1282_);
            crate::leanh::lean_dec_ref(v_toApplicative_1281_);
            v___x_1283_ =
                crate::leanh::lean_apply_2(v_toPure_1282_, crate::leanh::lean_box(0), v_init_1266_);
            return v___x_1283_;
        } else {
            let mut v___x_1284_: usize = 0;
            let mut v___x_1285_: usize = 0;
            let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1284_ = lean_usize_of_nat(v_stop_1270_);
            crate::leanh::lean_dec(v_stop_1270_);
            v___x_1285_ = lean_usize_of_nat(v_start_1269_);
            crate::leanh::lean_dec(v_start_1269_);
            v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_inst_1287_: *mut crate::leanh::LeanObject,
    mut v_p_1288_: *mut crate::leanh::LeanObject,
    mut v_as_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v_toApplicative_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: usize = 0;
    let mut v___x_1301_: usize = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: u8 = 0;
    let mut v_toApplicative_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1290_ = crate::leanh::lean_ctor_get(v_as_1289_, 0);
                crate::leanh::lean_inc_ref(v_array_1290_);
                v_start_1291_ = crate::leanh::lean_ctor_get(v_as_1289_, 1);
                crate::leanh::lean_inc(v_start_1291_);
                v_stop_1292_ = crate::leanh::lean_ctor_get(v_as_1289_, 2);
                crate::leanh::lean_inc(v_stop_1292_);
                crate::leanh::lean_dec_ref(v_as_1289_);
                v___x_1303_ = lean_nat_dec_lt(v_start_1291_, v_stop_1292_);
                if v___x_1303_ == 0 {
                    crate::leanh::lean_dec(v_stop_1292_);
                    crate::leanh::lean_dec(v_start_1291_);
                    crate::leanh::lean_dec_ref(v_array_1290_);
                    crate::leanh::lean_dec(v_p_1288_);
                    v_toApplicative_1304_ = crate::leanh::lean_ctor_get(v_inst_1287_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1304_);
                    crate::leanh::lean_dec_ref(v_inst_1287_);
                    v_toPure_1305_ = crate::leanh::lean_ctor_get(v_toApplicative_1304_, 1);
                    crate::leanh::lean_inc(v_toPure_1305_);
                    crate::leanh::lean_dec_ref(v_toApplicative_1304_);
                    v___x_1306_ = crate::leanh::lean_box((v___x_1303_) as usize);
                    v___x_1307_ = crate::leanh::lean_apply_2(
                        v_toPure_1305_,
                        crate::leanh::lean_box(0),
                        v___x_1306_,
                    );
                    return v___x_1307_;
                } else {
                    v___x_1308_ = lean_array_get_size(v_array_1290_);
                    v___x_1309_ = lean_nat_dec_le(v_stop_1292_, v___x_1308_);
                    if v___x_1309_ == 0 {
                        crate::leanh::lean_dec(v_stop_1292_);
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
                    crate::leanh::lean_dec(v___y_1294_);
                    crate::leanh::lean_dec(v_start_1291_);
                    crate::leanh::lean_dec_ref(v_array_1290_);
                    crate::leanh::lean_dec(v_p_1288_);
                    v_toApplicative_1296_ = crate::leanh::lean_ctor_get(v_inst_1287_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1296_);
                    crate::leanh::lean_dec_ref(v_inst_1287_);
                    v_toPure_1297_ = crate::leanh::lean_ctor_get(v_toApplicative_1296_, 1);
                    crate::leanh::lean_inc(v_toPure_1297_);
                    crate::leanh::lean_dec_ref(v_toApplicative_1296_);
                    v___x_1298_ = crate::leanh::lean_box((v___x_1295_) as usize);
                    v___x_1299_ = crate::leanh::lean_apply_2(
                        v_toPure_1297_,
                        crate::leanh::lean_box(0),
                        v___x_1298_,
                    );
                    return v___x_1299_;
                } else {
                    v___x_1300_ = lean_usize_of_nat(v_start_1291_);
                    crate::leanh::lean_dec(v_start_1291_);
                    v___x_1301_ = lean_usize_of_nat(v___y_1294_);
                    crate::leanh::lean_dec(v___y_1294_);
                    v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1310_: *mut crate::leanh::LeanObject,
    mut v_m_1311_: *mut crate::leanh::LeanObject,
    mut v_inst_1312_: *mut crate::leanh::LeanObject,
    mut v_p_1313_: *mut crate::leanh::LeanObject,
    mut v_as_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v_toApplicative_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: usize = 0;
    let mut v___x_1326_: usize = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v_toApplicative_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1315_ = crate::leanh::lean_ctor_get(v_as_1314_, 0);
                crate::leanh::lean_inc_ref(v_array_1315_);
                v_start_1316_ = crate::leanh::lean_ctor_get(v_as_1314_, 1);
                crate::leanh::lean_inc(v_start_1316_);
                v_stop_1317_ = crate::leanh::lean_ctor_get(v_as_1314_, 2);
                crate::leanh::lean_inc(v_stop_1317_);
                crate::leanh::lean_dec_ref(v_as_1314_);
                v___x_1328_ = lean_nat_dec_lt(v_start_1316_, v_stop_1317_);
                if v___x_1328_ == 0 {
                    crate::leanh::lean_dec(v_stop_1317_);
                    crate::leanh::lean_dec(v_start_1316_);
                    crate::leanh::lean_dec_ref(v_array_1315_);
                    crate::leanh::lean_dec(v_p_1313_);
                    v_toApplicative_1329_ = crate::leanh::lean_ctor_get(v_inst_1312_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1329_);
                    crate::leanh::lean_dec_ref(v_inst_1312_);
                    v_toPure_1330_ = crate::leanh::lean_ctor_get(v_toApplicative_1329_, 1);
                    crate::leanh::lean_inc(v_toPure_1330_);
                    crate::leanh::lean_dec_ref(v_toApplicative_1329_);
                    v___x_1331_ = crate::leanh::lean_box((v___x_1328_) as usize);
                    v___x_1332_ = crate::leanh::lean_apply_2(
                        v_toPure_1330_,
                        crate::leanh::lean_box(0),
                        v___x_1331_,
                    );
                    return v___x_1332_;
                } else {
                    v___x_1333_ = lean_array_get_size(v_array_1315_);
                    v___x_1334_ = lean_nat_dec_le(v_stop_1317_, v___x_1333_);
                    if v___x_1334_ == 0 {
                        crate::leanh::lean_dec(v_stop_1317_);
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
                    crate::leanh::lean_dec(v___y_1319_);
                    crate::leanh::lean_dec(v_start_1316_);
                    crate::leanh::lean_dec_ref(v_array_1315_);
                    crate::leanh::lean_dec(v_p_1313_);
                    v_toApplicative_1321_ = crate::leanh::lean_ctor_get(v_inst_1312_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1321_);
                    crate::leanh::lean_dec_ref(v_inst_1312_);
                    v_toPure_1322_ = crate::leanh::lean_ctor_get(v_toApplicative_1321_, 1);
                    crate::leanh::lean_inc(v_toPure_1322_);
                    crate::leanh::lean_dec_ref(v_toApplicative_1321_);
                    v___x_1323_ = crate::leanh::lean_box((v___x_1320_) as usize);
                    v___x_1324_ = crate::leanh::lean_apply_2(
                        v_toPure_1322_,
                        crate::leanh::lean_box(0),
                        v___x_1323_,
                    );
                    return v___x_1324_;
                } else {
                    v___x_1325_ = lean_usize_of_nat(v_start_1316_);
                    crate::leanh::lean_dec(v_start_1316_);
                    v___x_1326_ = lean_usize_of_nat(v___y_1319_);
                    crate::leanh::lean_dec(v___y_1319_);
                    v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_toPure_1335_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1336_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1336_ == 0 {
        let mut v___x_1337_: u8 = 0;
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1337_ = 1;
        v___x_1338_ = crate::leanh::lean_box((v___x_1337_) as usize);
        v___x_1339_ =
            crate::leanh::lean_apply_2(v_toPure_1335_, crate::leanh::lean_box(0), v___x_1338_);
        return v___x_1339_;
    } else {
        let mut v___x_1340_: u8 = 0;
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1340_ = 0;
        v___x_1341_ = crate::leanh::lean_box((v___x_1340_) as usize);
        v___x_1342_ =
            crate::leanh::lean_apply_2(v_toPure_1335_, crate::leanh::lean_box(0), v___x_1341_);
        return v___x_1342_;
    }
}
pub unsafe fn l_Subarray_allM___redArg___lam__0___boxed(
    mut v_toPure_1343_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_115__boxed_1345_: u8 = 0;
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_115__boxed_1345_ = (crate::leanh::lean_unbox(v_____do__lift_1344_) as u8);
    v_res_1346_ =
        l_Subarray_allM___redArg___lam__0(v_toPure_1343_, v_____do__lift_115__boxed_1345_);
    return v_res_1346_;
}
pub unsafe fn l_Subarray_allM___redArg___lam__1(
    mut v_toPure_1347_: *mut crate::leanh::LeanObject,
    mut v___x_1348_: u8,
    mut v_____do__lift_1349_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1349_ == 0 {
        let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1350_ = crate::leanh::lean_box((v___x_1348_) as usize);
        v___x_1351_ =
            crate::leanh::lean_apply_2(v_toPure_1347_, crate::leanh::lean_box(0), v___x_1350_);
        return v___x_1351_;
    } else {
        let mut v___x_1352_: u8 = 0;
        let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1352_ = 0;
        v___x_1353_ = crate::leanh::lean_box((v___x_1352_) as usize);
        v___x_1354_ =
            crate::leanh::lean_apply_2(v_toPure_1347_, crate::leanh::lean_box(0), v___x_1353_);
        return v___x_1354_;
    }
}
pub unsafe fn l_Subarray_allM___redArg___lam__1___boxed(
    mut v_toPure_1355_: *mut crate::leanh::LeanObject,
    mut v___x_1356_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_130__boxed_1358_: u8 = 0;
    let mut v_____do__lift_131__boxed_1359_: u8 = 0;
    let mut v_res_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_130__boxed_1358_ = (crate::leanh::lean_unbox(v___x_1356_) as u8);
    v_____do__lift_131__boxed_1359_ = (crate::leanh::lean_unbox(v_____do__lift_1357_) as u8);
    v_res_1360_ = l_Subarray_allM___redArg___lam__1(
        v_toPure_1355_,
        v___x_130__boxed_1358_,
        v_____do__lift_131__boxed_1359_,
    );
    return v_res_1360_;
}
pub unsafe fn l_Subarray_allM___redArg___lam__2(
    mut v_p_1361_: *mut crate::leanh::LeanObject,
    mut v_toBind_1362_: *mut crate::leanh::LeanObject,
    mut v___f_1363_: *mut crate::leanh::LeanObject,
    mut v_v_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = crate::leanh::lean_apply_1(v_p_1361_, v_v_1364_);
    v___x_1366_ = crate::leanh::lean_apply_4(
        v_toBind_1362_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1365_,
        v___f_1363_,
    );
    return v___x_1366_;
}
pub unsafe fn l_Subarray_allM___redArg(
    mut v_inst_1367_: *mut crate::leanh::LeanObject,
    mut v_p_1368_: *mut crate::leanh::LeanObject,
    mut v_as_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1370_ = crate::leanh::lean_ctor_get(v_inst_1367_, 0);
                v_array_1371_ = crate::leanh::lean_ctor_get(v_as_1369_, 0);
                crate::leanh::lean_inc_ref(v_array_1371_);
                v_start_1372_ = crate::leanh::lean_ctor_get(v_as_1369_, 1);
                crate::leanh::lean_inc(v_start_1372_);
                v_stop_1373_ = crate::leanh::lean_ctor_get(v_as_1369_, 2);
                crate::leanh::lean_inc(v_stop_1373_);
                crate::leanh::lean_dec_ref(v_as_1369_);
                v_toBind_1374_ = crate::leanh::lean_ctor_get(v_inst_1367_, 1);
                crate::leanh::lean_inc(v_toBind_1374_);
                v_toPure_1375_ = crate::leanh::lean_ctor_get(v_toApplicative_1370_, 1);
                crate::leanh::lean_inc(v_toPure_1375_);
                v___f_1376_ = crate::leanh::lean_alloc_closure(
                    l_Subarray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1376_, 0, v_toPure_1375_);
                v___x_1377_ = lean_nat_dec_lt(v_start_1372_, v_stop_1373_);
                if v___x_1377_ == 0 {
                    crate::leanh::lean_inc(v_toPure_1375_);
                    crate::leanh::lean_dec(v_stop_1373_);
                    crate::leanh::lean_dec(v_start_1372_);
                    crate::leanh::lean_dec_ref(v_array_1371_);
                    crate::leanh::lean_dec(v_p_1368_);
                    crate::leanh::lean_dec_ref(v_inst_1367_);
                    v___x_1378_ = crate::leanh::lean_box((v___x_1377_) as usize);
                    v___x_1379_ = crate::leanh::lean_apply_2(
                        v_toPure_1375_,
                        crate::leanh::lean_box(0),
                        v___x_1378_,
                    );
                    v___x_1380_ = crate::leanh::lean_apply_4(
                        v_toBind_1374_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1379_,
                        v___f_1376_,
                    );
                    return v___x_1380_;
                } else {
                    v___x_1381_ = crate::leanh::lean_box((v___x_1377_) as usize);
                    crate::leanh::lean_inc(v_toPure_1375_);
                    v___f_1382_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1382_, 0, v_toPure_1375_);
                    crate::leanh::lean_closure_set(v___f_1382_, 1, v___x_1381_);
                    crate::leanh::lean_inc(v_toBind_1374_);
                    v___f_1383_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_1383_, 0, v_p_1368_);
                    crate::leanh::lean_closure_set(v___f_1383_, 1, v_toBind_1374_);
                    crate::leanh::lean_closure_set(v___f_1383_, 2, v___f_1382_);
                    v___x_1394_ = lean_array_get_size(v_array_1371_);
                    v___x_1395_ = lean_nat_dec_le(v_stop_1373_, v___x_1394_);
                    if v___x_1395_ == 0 {
                        crate::leanh::lean_dec(v_stop_1373_);
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
                    crate::leanh::lean_inc(v_toPure_1375_);
                    crate::leanh::lean_dec(v___y_1385_);
                    crate::leanh::lean_dec_ref(v___f_1383_);
                    crate::leanh::lean_dec(v_start_1372_);
                    crate::leanh::lean_dec_ref(v_array_1371_);
                    crate::leanh::lean_dec_ref(v_inst_1367_);
                    v___x_1387_ = crate::leanh::lean_box((v___x_1386_) as usize);
                    v___x_1388_ = crate::leanh::lean_apply_2(
                        v_toPure_1375_,
                        crate::leanh::lean_box(0),
                        v___x_1387_,
                    );
                    v___x_1389_ = crate::leanh::lean_apply_4(
                        v_toBind_1374_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1388_,
                        v___f_1376_,
                    );
                    return v___x_1389_;
                } else {
                    v___x_1390_ = lean_usize_of_nat(v_start_1372_);
                    crate::leanh::lean_dec(v_start_1372_);
                    v___x_1391_ = lean_usize_of_nat(v___y_1385_);
                    crate::leanh::lean_dec(v___y_1385_);
                    v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_1367_,
                        v___f_1383_,
                        v_array_1371_,
                        v___x_1390_,
                        v___x_1391_,
                    );
                    v___x_1393_ = crate::leanh::lean_apply_4(
                        v_toBind_1374_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1396_: *mut crate::leanh::LeanObject,
    mut v_m_1397_: *mut crate::leanh::LeanObject,
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_p_1399_: *mut crate::leanh::LeanObject,
    mut v_as_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: usize = 0;
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1401_ = crate::leanh::lean_ctor_get(v_inst_1398_, 0);
                v_array_1402_ = crate::leanh::lean_ctor_get(v_as_1400_, 0);
                crate::leanh::lean_inc_ref(v_array_1402_);
                v_start_1403_ = crate::leanh::lean_ctor_get(v_as_1400_, 1);
                crate::leanh::lean_inc(v_start_1403_);
                v_stop_1404_ = crate::leanh::lean_ctor_get(v_as_1400_, 2);
                crate::leanh::lean_inc(v_stop_1404_);
                crate::leanh::lean_dec_ref(v_as_1400_);
                v_toBind_1405_ = crate::leanh::lean_ctor_get(v_inst_1398_, 1);
                crate::leanh::lean_inc(v_toBind_1405_);
                v_toPure_1406_ = crate::leanh::lean_ctor_get(v_toApplicative_1401_, 1);
                crate::leanh::lean_inc(v_toPure_1406_);
                v___f_1407_ = crate::leanh::lean_alloc_closure(
                    l_Subarray_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1407_, 0, v_toPure_1406_);
                v___x_1408_ = lean_nat_dec_lt(v_start_1403_, v_stop_1404_);
                if v___x_1408_ == 0 {
                    crate::leanh::lean_inc(v_toPure_1406_);
                    crate::leanh::lean_dec(v_stop_1404_);
                    crate::leanh::lean_dec(v_start_1403_);
                    crate::leanh::lean_dec_ref(v_array_1402_);
                    crate::leanh::lean_dec(v_p_1399_);
                    crate::leanh::lean_dec_ref(v_inst_1398_);
                    v___x_1409_ = crate::leanh::lean_box((v___x_1408_) as usize);
                    v___x_1410_ = crate::leanh::lean_apply_2(
                        v_toPure_1406_,
                        crate::leanh::lean_box(0),
                        v___x_1409_,
                    );
                    v___x_1411_ = crate::leanh::lean_apply_4(
                        v_toBind_1405_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1410_,
                        v___f_1407_,
                    );
                    return v___x_1411_;
                } else {
                    v___x_1412_ = crate::leanh::lean_box((v___x_1408_) as usize);
                    crate::leanh::lean_inc(v_toPure_1406_);
                    v___f_1413_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1413_, 0, v_toPure_1406_);
                    crate::leanh::lean_closure_set(v___f_1413_, 1, v___x_1412_);
                    crate::leanh::lean_inc(v_toBind_1405_);
                    v___f_1414_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_allM___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_1414_, 0, v_p_1399_);
                    crate::leanh::lean_closure_set(v___f_1414_, 1, v_toBind_1405_);
                    crate::leanh::lean_closure_set(v___f_1414_, 2, v___f_1413_);
                    v___x_1425_ = lean_array_get_size(v_array_1402_);
                    v___x_1426_ = lean_nat_dec_le(v_stop_1404_, v___x_1425_);
                    if v___x_1426_ == 0 {
                        crate::leanh::lean_dec(v_stop_1404_);
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
                    crate::leanh::lean_inc(v_toPure_1406_);
                    crate::leanh::lean_dec(v___y_1416_);
                    crate::leanh::lean_dec_ref(v___f_1414_);
                    crate::leanh::lean_dec(v_start_1403_);
                    crate::leanh::lean_dec_ref(v_array_1402_);
                    crate::leanh::lean_dec_ref(v_inst_1398_);
                    v___x_1418_ = crate::leanh::lean_box((v___x_1417_) as usize);
                    v___x_1419_ = crate::leanh::lean_apply_2(
                        v_toPure_1406_,
                        crate::leanh::lean_box(0),
                        v___x_1418_,
                    );
                    v___x_1420_ = crate::leanh::lean_apply_4(
                        v_toBind_1405_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1419_,
                        v___f_1407_,
                    );
                    return v___x_1420_;
                } else {
                    v___x_1421_ = lean_usize_of_nat(v_start_1403_);
                    crate::leanh::lean_dec(v_start_1403_);
                    v___x_1422_ = lean_usize_of_nat(v___y_1416_);
                    crate::leanh::lean_dec(v___y_1416_);
                    v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_1398_,
                        v___f_1414_,
                        v_array_1402_,
                        v___x_1421_,
                        v___x_1422_,
                    );
                    v___x_1424_ = crate::leanh::lean_apply_4(
                        v_toBind_1405_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_f_1427_: *mut crate::leanh::LeanObject,
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = crate::leanh::lean_apply_1(v_f_1427_, v___y_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Subarray_forM___redArg(
    mut v_inst_1431_: *mut crate::leanh::LeanObject,
    mut v_f_1432_: *mut crate::leanh::LeanObject,
    mut v_as_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    v_array_1434_ = crate::leanh::lean_ctor_get(v_as_1433_, 0);
    crate::leanh::lean_inc_ref(v_array_1434_);
    v_start_1435_ = crate::leanh::lean_ctor_get(v_as_1433_, 1);
    crate::leanh::lean_inc(v_start_1435_);
    v_stop_1436_ = crate::leanh::lean_ctor_get(v_as_1433_, 2);
    crate::leanh::lean_inc(v_stop_1436_);
    crate::leanh::lean_dec_ref(v_as_1433_);
    v___x_1437_ = crate::leanh::lean_box(0);
    v___x_1438_ = lean_nat_dec_lt(v_start_1435_, v_stop_1436_);
    if v___x_1438_ == 0 {
        let mut v_toApplicative_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stop_1436_);
        crate::leanh::lean_dec(v_start_1435_);
        crate::leanh::lean_dec_ref(v_array_1434_);
        crate::leanh::lean_dec(v_f_1432_);
        v_toApplicative_1439_ = crate::leanh::lean_ctor_get(v_inst_1431_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1439_);
        crate::leanh::lean_dec_ref(v_inst_1431_);
        v_toPure_1440_ = crate::leanh::lean_ctor_get(v_toApplicative_1439_, 1);
        crate::leanh::lean_inc(v_toPure_1440_);
        crate::leanh::lean_dec_ref(v_toApplicative_1439_);
        v___x_1441_ =
            crate::leanh::lean_apply_2(v_toPure_1440_, crate::leanh::lean_box(0), v___x_1437_);
        return v___x_1441_;
    } else {
        let mut v___f_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: u8 = 0;
        v___f_1442_ = crate::leanh::lean_alloc_closure(
            l_Subarray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1442_, 0, v_f_1432_);
        v___x_1443_ = lean_array_get_size(v_array_1434_);
        v___x_1444_ = lean_nat_dec_le(v_stop_1436_, v___x_1443_);
        if v___x_1444_ == 0 {
            let mut v___x_1445_: u8 = 0;
            crate::leanh::lean_dec(v_stop_1436_);
            v___x_1445_ = lean_nat_dec_lt(v_start_1435_, v___x_1443_);
            if v___x_1445_ == 0 {
                let mut v_toApplicative_1446_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_1442_);
                crate::leanh::lean_dec(v_start_1435_);
                crate::leanh::lean_dec_ref(v_array_1434_);
                v_toApplicative_1446_ = crate::leanh::lean_ctor_get(v_inst_1431_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1446_);
                crate::leanh::lean_dec_ref(v_inst_1431_);
                v_toPure_1447_ = crate::leanh::lean_ctor_get(v_toApplicative_1446_, 1);
                crate::leanh::lean_inc(v_toPure_1447_);
                crate::leanh::lean_dec_ref(v_toApplicative_1446_);
                v___x_1448_ = crate::leanh::lean_apply_2(
                    v_toPure_1447_,
                    crate::leanh::lean_box(0),
                    v___x_1437_,
                );
                return v___x_1448_;
            } else {
                let mut v___x_1449_: usize = 0;
                let mut v___x_1450_: usize = 0;
                let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1449_ = lean_usize_of_nat(v_start_1435_);
                crate::leanh::lean_dec(v_start_1435_);
                v___x_1450_ = lean_usize_of_nat(v___x_1443_);
                v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1452_ = lean_usize_of_nat(v_start_1435_);
            crate::leanh::lean_dec(v_start_1435_);
            v___x_1453_ = lean_usize_of_nat(v_stop_1436_);
            crate::leanh::lean_dec(v_stop_1436_);
            v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1455_: *mut crate::leanh::LeanObject,
    mut v_m_1456_: *mut crate::leanh::LeanObject,
    mut v_inst_1457_: *mut crate::leanh::LeanObject,
    mut v_f_1458_: *mut crate::leanh::LeanObject,
    mut v_as_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    v_array_1460_ = crate::leanh::lean_ctor_get(v_as_1459_, 0);
    crate::leanh::lean_inc_ref(v_array_1460_);
    v_start_1461_ = crate::leanh::lean_ctor_get(v_as_1459_, 1);
    crate::leanh::lean_inc(v_start_1461_);
    v_stop_1462_ = crate::leanh::lean_ctor_get(v_as_1459_, 2);
    crate::leanh::lean_inc(v_stop_1462_);
    crate::leanh::lean_dec_ref(v_as_1459_);
    v___x_1463_ = crate::leanh::lean_box(0);
    v___x_1464_ = lean_nat_dec_lt(v_start_1461_, v_stop_1462_);
    if v___x_1464_ == 0 {
        let mut v_toApplicative_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stop_1462_);
        crate::leanh::lean_dec(v_start_1461_);
        crate::leanh::lean_dec_ref(v_array_1460_);
        crate::leanh::lean_dec(v_f_1458_);
        v_toApplicative_1465_ = crate::leanh::lean_ctor_get(v_inst_1457_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1465_);
        crate::leanh::lean_dec_ref(v_inst_1457_);
        v_toPure_1466_ = crate::leanh::lean_ctor_get(v_toApplicative_1465_, 1);
        crate::leanh::lean_inc(v_toPure_1466_);
        crate::leanh::lean_dec_ref(v_toApplicative_1465_);
        v___x_1467_ =
            crate::leanh::lean_apply_2(v_toPure_1466_, crate::leanh::lean_box(0), v___x_1463_);
        return v___x_1467_;
    } else {
        let mut v___f_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: u8 = 0;
        v___f_1468_ = crate::leanh::lean_alloc_closure(
            l_Subarray_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1468_, 0, v_f_1458_);
        v___x_1469_ = lean_array_get_size(v_array_1460_);
        v___x_1470_ = lean_nat_dec_le(v_stop_1462_, v___x_1469_);
        if v___x_1470_ == 0 {
            let mut v___x_1471_: u8 = 0;
            crate::leanh::lean_dec(v_stop_1462_);
            v___x_1471_ = lean_nat_dec_lt(v_start_1461_, v___x_1469_);
            if v___x_1471_ == 0 {
                let mut v_toApplicative_1472_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___f_1468_);
                crate::leanh::lean_dec(v_start_1461_);
                crate::leanh::lean_dec_ref(v_array_1460_);
                v_toApplicative_1472_ = crate::leanh::lean_ctor_get(v_inst_1457_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1472_);
                crate::leanh::lean_dec_ref(v_inst_1457_);
                v_toPure_1473_ = crate::leanh::lean_ctor_get(v_toApplicative_1472_, 1);
                crate::leanh::lean_inc(v_toPure_1473_);
                crate::leanh::lean_dec_ref(v_toApplicative_1472_);
                v___x_1474_ = crate::leanh::lean_apply_2(
                    v_toPure_1473_,
                    crate::leanh::lean_box(0),
                    v___x_1463_,
                );
                return v___x_1474_;
            } else {
                let mut v___x_1475_: usize = 0;
                let mut v___x_1476_: usize = 0;
                let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1475_ = lean_usize_of_nat(v_start_1461_);
                crate::leanh::lean_dec(v_start_1461_);
                v___x_1476_ = lean_usize_of_nat(v___x_1469_);
                v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
            let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1478_ = lean_usize_of_nat(v_start_1461_);
            crate::leanh::lean_dec(v_start_1461_);
            v___x_1479_ = lean_usize_of_nat(v_stop_1462_);
            crate::leanh::lean_dec(v_stop_1462_);
            v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_f_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = crate::leanh::lean_apply_1(v_f_1481_, v_a_1482_);
    return v___x_1484_;
}
pub unsafe fn l_Subarray_forRevM___redArg(
    mut v_inst_1485_: *mut crate::leanh::LeanObject,
    mut v_f_1486_: *mut crate::leanh::LeanObject,
    mut v_as_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    v_array_1488_ = crate::leanh::lean_ctor_get(v_as_1487_, 0);
    crate::leanh::lean_inc_ref(v_array_1488_);
    v_start_1489_ = crate::leanh::lean_ctor_get(v_as_1487_, 1);
    crate::leanh::lean_inc(v_start_1489_);
    v_stop_1490_ = crate::leanh::lean_ctor_get(v_as_1487_, 2);
    crate::leanh::lean_inc(v_stop_1490_);
    crate::leanh::lean_dec_ref(v_as_1487_);
    v___f_1491_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1491_, 0, v_f_1486_);
    v___x_1492_ = crate::leanh::lean_box(0);
    v___x_1493_ = lean_array_get_size(v_array_1488_);
    v___x_1494_ = lean_nat_dec_le(v_stop_1490_, v___x_1493_);
    if v___x_1494_ == 0 {
        let mut v___x_1495_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1490_);
        v___x_1495_ = lean_nat_dec_lt(v_start_1489_, v___x_1493_);
        if v___x_1495_ == 0 {
            let mut v_toApplicative_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___f_1491_);
            crate::leanh::lean_dec(v_start_1489_);
            crate::leanh::lean_dec_ref(v_array_1488_);
            v_toApplicative_1496_ = crate::leanh::lean_ctor_get(v_inst_1485_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1496_);
            crate::leanh::lean_dec_ref(v_inst_1485_);
            v_toPure_1497_ = crate::leanh::lean_ctor_get(v_toApplicative_1496_, 1);
            crate::leanh::lean_inc(v_toPure_1497_);
            crate::leanh::lean_dec_ref(v_toApplicative_1496_);
            v___x_1498_ =
                crate::leanh::lean_apply_2(v_toPure_1497_, crate::leanh::lean_box(0), v___x_1492_);
            return v___x_1498_;
        } else {
            let mut v___x_1499_: usize = 0;
            let mut v___x_1500_: usize = 0;
            let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1499_ = lean_usize_of_nat(v___x_1493_);
            v___x_1500_ = lean_usize_of_nat(v_start_1489_);
            crate::leanh::lean_dec(v_start_1489_);
            v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            let mut v_toApplicative_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___f_1491_);
            crate::leanh::lean_dec(v_stop_1490_);
            crate::leanh::lean_dec(v_start_1489_);
            crate::leanh::lean_dec_ref(v_array_1488_);
            v_toApplicative_1503_ = crate::leanh::lean_ctor_get(v_inst_1485_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1503_);
            crate::leanh::lean_dec_ref(v_inst_1485_);
            v_toPure_1504_ = crate::leanh::lean_ctor_get(v_toApplicative_1503_, 1);
            crate::leanh::lean_inc(v_toPure_1504_);
            crate::leanh::lean_dec_ref(v_toApplicative_1503_);
            v___x_1505_ =
                crate::leanh::lean_apply_2(v_toPure_1504_, crate::leanh::lean_box(0), v___x_1492_);
            return v___x_1505_;
        } else {
            let mut v___x_1506_: usize = 0;
            let mut v___x_1507_: usize = 0;
            let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1506_ = lean_usize_of_nat(v_stop_1490_);
            crate::leanh::lean_dec(v_stop_1490_);
            v___x_1507_ = lean_usize_of_nat(v_start_1489_);
            crate::leanh::lean_dec(v_start_1489_);
            v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1509_: *mut crate::leanh::LeanObject,
    mut v_m_1510_: *mut crate::leanh::LeanObject,
    mut v_inst_1511_: *mut crate::leanh::LeanObject,
    mut v_f_1512_: *mut crate::leanh::LeanObject,
    mut v_as_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    v_array_1514_ = crate::leanh::lean_ctor_get(v_as_1513_, 0);
    crate::leanh::lean_inc_ref(v_array_1514_);
    v_start_1515_ = crate::leanh::lean_ctor_get(v_as_1513_, 1);
    crate::leanh::lean_inc(v_start_1515_);
    v_stop_1516_ = crate::leanh::lean_ctor_get(v_as_1513_, 2);
    crate::leanh::lean_inc(v_stop_1516_);
    crate::leanh::lean_dec_ref(v_as_1513_);
    v___f_1517_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forRevM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1517_, 0, v_f_1512_);
    v___x_1518_ = crate::leanh::lean_box(0);
    v___x_1519_ = lean_array_get_size(v_array_1514_);
    v___x_1520_ = lean_nat_dec_le(v_stop_1516_, v___x_1519_);
    if v___x_1520_ == 0 {
        let mut v___x_1521_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1516_);
        v___x_1521_ = lean_nat_dec_lt(v_start_1515_, v___x_1519_);
        if v___x_1521_ == 0 {
            let mut v_toApplicative_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___f_1517_);
            crate::leanh::lean_dec(v_start_1515_);
            crate::leanh::lean_dec_ref(v_array_1514_);
            v_toApplicative_1522_ = crate::leanh::lean_ctor_get(v_inst_1511_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1522_);
            crate::leanh::lean_dec_ref(v_inst_1511_);
            v_toPure_1523_ = crate::leanh::lean_ctor_get(v_toApplicative_1522_, 1);
            crate::leanh::lean_inc(v_toPure_1523_);
            crate::leanh::lean_dec_ref(v_toApplicative_1522_);
            v___x_1524_ =
                crate::leanh::lean_apply_2(v_toPure_1523_, crate::leanh::lean_box(0), v___x_1518_);
            return v___x_1524_;
        } else {
            let mut v___x_1525_: usize = 0;
            let mut v___x_1526_: usize = 0;
            let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1525_ = lean_usize_of_nat(v___x_1519_);
            v___x_1526_ = lean_usize_of_nat(v_start_1515_);
            crate::leanh::lean_dec(v_start_1515_);
            v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            let mut v_toApplicative_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___f_1517_);
            crate::leanh::lean_dec(v_stop_1516_);
            crate::leanh::lean_dec(v_start_1515_);
            crate::leanh::lean_dec_ref(v_array_1514_);
            v_toApplicative_1529_ = crate::leanh::lean_ctor_get(v_inst_1511_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1529_);
            crate::leanh::lean_dec_ref(v_inst_1511_);
            v_toPure_1530_ = crate::leanh::lean_ctor_get(v_toApplicative_1529_, 1);
            crate::leanh::lean_inc(v_toPure_1530_);
            crate::leanh::lean_dec_ref(v_toApplicative_1529_);
            v___x_1531_ =
                crate::leanh::lean_apply_2(v_toPure_1530_, crate::leanh::lean_box(0), v___x_1518_);
            return v___x_1531_;
        } else {
            let mut v___x_1532_: usize = 0;
            let mut v___x_1533_: usize = 0;
            let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1532_ = lean_usize_of_nat(v_stop_1516_);
            crate::leanh::lean_dec(v_stop_1516_);
            v___x_1533_ = lean_usize_of_nat(v_start_1515_);
            crate::leanh::lean_dec(v_start_1515_);
            v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_f_1535_: *mut crate::leanh::LeanObject,
    mut v_x1_1536_: *mut crate::leanh::LeanObject,
    mut v_x2_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = crate::leanh::lean_apply_2(v_f_1535_, v_x1_1536_, v_x2_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Subarray_foldr___redArg(
    mut v_f_1558_: *mut crate::leanh::LeanObject,
    mut v_init_1559_: *mut crate::leanh::LeanObject,
    mut v_as_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    v___x_1561_ = l_Subarray_foldr___redArg___closed__9;
    v_array_1562_ = crate::leanh::lean_ctor_get(v_as_1560_, 0);
    crate::leanh::lean_inc_ref(v_array_1562_);
    v_start_1563_ = crate::leanh::lean_ctor_get(v_as_1560_, 1);
    crate::leanh::lean_inc(v_start_1563_);
    v_stop_1564_ = crate::leanh::lean_ctor_get(v_as_1560_, 2);
    crate::leanh::lean_inc(v_stop_1564_);
    crate::leanh::lean_dec_ref(v_as_1560_);
    v___f_1565_ = crate::leanh::lean_alloc_closure(
        l_Subarray_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1565_, 0, v_f_1558_);
    v___x_1566_ = lean_array_get_size(v_array_1562_);
    v___x_1567_ = lean_nat_dec_le(v_stop_1564_, v___x_1566_);
    if v___x_1567_ == 0 {
        let mut v___x_1568_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1564_);
        v___x_1568_ = lean_nat_dec_lt(v_start_1563_, v___x_1566_);
        if v___x_1568_ == 0 {
            crate::leanh::lean_dec_ref(v___f_1565_);
            crate::leanh::lean_dec(v_start_1563_);
            crate::leanh::lean_dec_ref(v_array_1562_);
            return v_init_1559_;
        } else {
            let mut v___x_1569_: usize = 0;
            let mut v___x_1570_: usize = 0;
            let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1569_ = lean_usize_of_nat(v___x_1566_);
            v___x_1570_ = lean_usize_of_nat(v_start_1563_);
            crate::leanh::lean_dec(v_start_1563_);
            v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            crate::leanh::lean_dec_ref(v___f_1565_);
            crate::leanh::lean_dec(v_stop_1564_);
            crate::leanh::lean_dec(v_start_1563_);
            crate::leanh::lean_dec_ref(v_array_1562_);
            return v_init_1559_;
        } else {
            let mut v___x_1573_: usize = 0;
            let mut v___x_1574_: usize = 0;
            let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1573_ = lean_usize_of_nat(v_stop_1564_);
            crate::leanh::lean_dec(v_stop_1564_);
            v___x_1574_ = lean_usize_of_nat(v_start_1563_);
            crate::leanh::lean_dec(v_start_1563_);
            v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_00_u03b1_1576_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1577_: *mut crate::leanh::LeanObject,
    mut v_f_1578_: *mut crate::leanh::LeanObject,
    mut v_init_1579_: *mut crate::leanh::LeanObject,
    mut v_as_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    v___x_1581_ = l_Subarray_foldr___redArg___closed__9;
    v_array_1582_ = crate::leanh::lean_ctor_get(v_as_1580_, 0);
    crate::leanh::lean_inc_ref(v_array_1582_);
    v_start_1583_ = crate::leanh::lean_ctor_get(v_as_1580_, 1);
    crate::leanh::lean_inc(v_start_1583_);
    v_stop_1584_ = crate::leanh::lean_ctor_get(v_as_1580_, 2);
    crate::leanh::lean_inc(v_stop_1584_);
    crate::leanh::lean_dec_ref(v_as_1580_);
    v___f_1585_ = crate::leanh::lean_alloc_closure(
        l_Subarray_foldr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1585_, 0, v_f_1578_);
    v___x_1586_ = lean_array_get_size(v_array_1582_);
    v___x_1587_ = lean_nat_dec_le(v_stop_1584_, v___x_1586_);
    if v___x_1587_ == 0 {
        let mut v___x_1588_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1584_);
        v___x_1588_ = lean_nat_dec_lt(v_start_1583_, v___x_1586_);
        if v___x_1588_ == 0 {
            crate::leanh::lean_dec_ref(v___f_1585_);
            crate::leanh::lean_dec(v_start_1583_);
            crate::leanh::lean_dec_ref(v_array_1582_);
            return v_init_1579_;
        } else {
            let mut v___x_1589_: usize = 0;
            let mut v___x_1590_: usize = 0;
            let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1589_ = lean_usize_of_nat(v___x_1586_);
            v___x_1590_ = lean_usize_of_nat(v_start_1583_);
            crate::leanh::lean_dec(v_start_1583_);
            v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
            crate::leanh::lean_dec_ref(v___f_1585_);
            crate::leanh::lean_dec(v_stop_1584_);
            crate::leanh::lean_dec(v_start_1583_);
            crate::leanh::lean_dec_ref(v_array_1582_);
            return v_init_1579_;
        } else {
            let mut v___x_1593_: usize = 0;
            let mut v___x_1594_: usize = 0;
            let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1593_ = lean_usize_of_nat(v_stop_1584_);
            crate::leanh::lean_dec(v_stop_1584_);
            v___x_1594_ = lean_usize_of_nat(v_start_1583_);
            crate::leanh::lean_dec(v_start_1583_);
            v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
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
    mut v_p_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    v___x_1598_ = crate::leanh::lean_apply_1(v_p_1596_, v_x_1597_);
    v___x_1599_ = (crate::leanh::lean_unbox(v___x_1598_) as u8);
    return v___x_1599_;
}
pub unsafe fn l_Subarray_any___redArg___lam__0___boxed(
    mut v_p_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1602_: u8 = 0;
    let mut v_r_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Subarray_any___redArg___lam__0(v_p_1600_, v_x_1601_);
    v_r_1603_ = crate::leanh::lean_box((v_res_1602_) as usize);
    return v_r_1603_;
}
pub unsafe fn l_Subarray_any___redArg(
    mut v_p_1604_: *mut crate::leanh::LeanObject,
    mut v_as_1605_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___f_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: usize = 0;
    let mut v___x_1616_: usize = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1606_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1607_ = crate::leanh::lean_ctor_get(v_as_1605_, 0);
                crate::leanh::lean_inc_ref(v_array_1607_);
                v_start_1608_ = crate::leanh::lean_ctor_get(v_as_1605_, 1);
                crate::leanh::lean_inc(v_start_1608_);
                v_stop_1609_ = crate::leanh::lean_ctor_get(v_as_1605_, 2);
                crate::leanh::lean_inc(v_stop_1609_);
                crate::leanh::lean_dec_ref(v_as_1605_);
                v___x_1610_ = lean_nat_dec_lt(v_start_1608_, v_stop_1609_);
                if v___x_1610_ == 0 {
                    crate::leanh::lean_dec(v_stop_1609_);
                    crate::leanh::lean_dec(v_start_1608_);
                    crate::leanh::lean_dec_ref(v_array_1607_);
                    crate::leanh::lean_dec_ref(v_p_1604_);
                    return v___x_1610_;
                } else {
                    v___f_1611_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1611_, 0, v_p_1604_);
                    v___x_1619_ = lean_array_get_size(v_array_1607_);
                    v___x_1620_ = lean_nat_dec_le(v_stop_1609_, v___x_1619_);
                    if v___x_1620_ == 0 {
                        crate::leanh::lean_dec(v_stop_1609_);
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
                    crate::leanh::lean_dec(v___y_1613_);
                    crate::leanh::lean_dec_ref(v___f_1611_);
                    crate::leanh::lean_dec(v_start_1608_);
                    crate::leanh::lean_dec_ref(v_array_1607_);
                    return v___x_1614_;
                } else {
                    v___x_1615_ = lean_usize_of_nat(v_start_1608_);
                    crate::leanh::lean_dec(v_start_1608_);
                    v___x_1616_ = lean_usize_of_nat(v___y_1613_);
                    crate::leanh::lean_dec(v___y_1613_);
                    v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1606_,
                        v___f_1611_,
                        v_array_1607_,
                        v___x_1615_,
                        v___x_1616_,
                    );
                    v___x_1618_ = (crate::leanh::lean_unbox(v___x_1617_) as u8);
                    crate::leanh::lean_dec(v___x_1617_);
                    return v___x_1618_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_any___redArg___boxed(
    mut v_p_1621_: *mut crate::leanh::LeanObject,
    mut v_as_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1623_: u8 = 0;
    let mut v_r_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Subarray_any___redArg(v_p_1621_, v_as_1622_);
    v_r_1624_ = crate::leanh::lean_box((v_res_1623_) as usize);
    return v_r_1624_;
}
pub unsafe fn l_Subarray_any(
    mut v_00_u03b1_1625_: *mut crate::leanh::LeanObject,
    mut v_p_1626_: *mut crate::leanh::LeanObject,
    mut v_as_1627_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___f_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: usize = 0;
    let mut v___x_1638_: usize = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1628_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1629_ = crate::leanh::lean_ctor_get(v_as_1627_, 0);
                crate::leanh::lean_inc_ref(v_array_1629_);
                v_start_1630_ = crate::leanh::lean_ctor_get(v_as_1627_, 1);
                crate::leanh::lean_inc(v_start_1630_);
                v_stop_1631_ = crate::leanh::lean_ctor_get(v_as_1627_, 2);
                crate::leanh::lean_inc(v_stop_1631_);
                crate::leanh::lean_dec_ref(v_as_1627_);
                v___x_1632_ = lean_nat_dec_lt(v_start_1630_, v_stop_1631_);
                if v___x_1632_ == 0 {
                    crate::leanh::lean_dec(v_stop_1631_);
                    crate::leanh::lean_dec(v_start_1630_);
                    crate::leanh::lean_dec_ref(v_array_1629_);
                    crate::leanh::lean_dec_ref(v_p_1626_);
                    return v___x_1632_;
                } else {
                    v___f_1633_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1633_, 0, v_p_1626_);
                    v___x_1641_ = lean_array_get_size(v_array_1629_);
                    v___x_1642_ = lean_nat_dec_le(v_stop_1631_, v___x_1641_);
                    if v___x_1642_ == 0 {
                        crate::leanh::lean_dec(v_stop_1631_);
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
                    crate::leanh::lean_dec(v___y_1635_);
                    crate::leanh::lean_dec_ref(v___f_1633_);
                    crate::leanh::lean_dec(v_start_1630_);
                    crate::leanh::lean_dec_ref(v_array_1629_);
                    return v___x_1636_;
                } else {
                    v___x_1637_ = lean_usize_of_nat(v_start_1630_);
                    crate::leanh::lean_dec(v_start_1630_);
                    v___x_1638_ = lean_usize_of_nat(v___y_1635_);
                    crate::leanh::lean_dec(v___y_1635_);
                    v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1628_,
                        v___f_1633_,
                        v_array_1629_,
                        v___x_1637_,
                        v___x_1638_,
                    );
                    v___x_1640_ = (crate::leanh::lean_unbox(v___x_1639_) as u8);
                    crate::leanh::lean_dec(v___x_1639_);
                    return v___x_1640_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_any___boxed(
    mut v_00_u03b1_1643_: *mut crate::leanh::LeanObject,
    mut v_p_1644_: *mut crate::leanh::LeanObject,
    mut v_as_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: u8 = 0;
    let mut v_r_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Subarray_any(v_00_u03b1_1643_, v_p_1644_, v_as_1645_);
    v_r_1647_ = crate::leanh::lean_box((v_res_1646_) as usize);
    return v_r_1647_;
}
pub unsafe fn l_Subarray_all___redArg___lam__0(
    mut v_p_1648_: *mut crate::leanh::LeanObject,
    mut v___x_1649_: u8,
    mut v_v_1650_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    v___x_1651_ = crate::leanh::lean_apply_1(v_p_1648_, v_v_1650_);
    v___x_1652_ = (crate::leanh::lean_unbox(v___x_1651_) as u8);
    if v___x_1652_ == 0 {
        return v___x_1649_;
    } else {
        let mut v___x_1653_: u8 = 0;
        v___x_1653_ = 0;
        return v___x_1653_;
    }
}
pub unsafe fn l_Subarray_all___redArg___lam__0___boxed(
    mut v_p_1654_: *mut crate::leanh::LeanObject,
    mut v___x_1655_: *mut crate::leanh::LeanObject,
    mut v_v_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342__boxed_1657_: u8 = 0;
    let mut v_res_1658_: u8 = 0;
    let mut v_r_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342__boxed_1657_ = (crate::leanh::lean_unbox(v___x_1655_) as u8);
    v_res_1658_ = l_Subarray_all___redArg___lam__0(v_p_1654_, v___x_342__boxed_1657_, v_v_1656_);
    v_r_1659_ = crate::leanh::lean_box((v_res_1658_) as usize);
    return v_r_1659_;
}
pub unsafe fn l_Subarray_all___redArg(
    mut v_p_1660_: *mut crate::leanh::LeanObject,
    mut v_as_1661_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1662_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1663_ = crate::leanh::lean_ctor_get(v_as_1661_, 0);
                crate::leanh::lean_inc_ref(v_array_1663_);
                v_start_1664_ = crate::leanh::lean_ctor_get(v_as_1661_, 1);
                crate::leanh::lean_inc(v_start_1664_);
                v_stop_1665_ = crate::leanh::lean_ctor_get(v_as_1661_, 2);
                crate::leanh::lean_inc(v_stop_1665_);
                crate::leanh::lean_dec_ref(v_as_1661_);
                v___x_1666_ = lean_nat_dec_lt(v_start_1664_, v_stop_1665_);
                if v___x_1666_ == 0 {
                    crate::leanh::lean_dec(v_stop_1665_);
                    crate::leanh::lean_dec(v_start_1664_);
                    crate::leanh::lean_dec_ref(v_array_1663_);
                    crate::leanh::lean_dec_ref(v_p_1660_);
                    v___x_1667_ = 1;
                    return v___x_1667_;
                } else {
                    v___x_1668_ = crate::leanh::lean_box((v___x_1666_) as usize);
                    v___f_1669_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1669_, 0, v_p_1660_);
                    crate::leanh::lean_closure_set(v___f_1669_, 1, v___x_1668_);
                    v___x_1678_ = lean_array_get_size(v_array_1663_);
                    v___x_1679_ = lean_nat_dec_le(v_stop_1665_, v___x_1678_);
                    if v___x_1679_ == 0 {
                        crate::leanh::lean_dec(v_stop_1665_);
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
                    crate::leanh::lean_dec(v___y_1671_);
                    crate::leanh::lean_dec_ref(v___f_1669_);
                    crate::leanh::lean_dec(v_start_1664_);
                    crate::leanh::lean_dec_ref(v_array_1663_);
                    return v___x_1666_;
                } else {
                    v___x_1673_ = lean_usize_of_nat(v_start_1664_);
                    crate::leanh::lean_dec(v_start_1664_);
                    v___x_1674_ = lean_usize_of_nat(v___y_1671_);
                    crate::leanh::lean_dec(v___y_1671_);
                    v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1662_,
                        v___f_1669_,
                        v_array_1663_,
                        v___x_1673_,
                        v___x_1674_,
                    );
                    v___x_1676_ = (crate::leanh::lean_unbox(v___x_1675_) as u8);
                    crate::leanh::lean_dec(v___x_1675_);
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
    mut v_p_1680_: *mut crate::leanh::LeanObject,
    mut v_as_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_Subarray_all___redArg(v_p_1680_, v_as_1681_);
    v_r_1683_ = crate::leanh::lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn l_Subarray_all(
    mut v_00_u03b1_1684_: *mut crate::leanh::LeanObject,
    mut v_p_1685_: *mut crate::leanh::LeanObject,
    mut v_as_1686_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: usize = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1687_ = l_Subarray_foldr___redArg___closed__9;
                v_array_1688_ = crate::leanh::lean_ctor_get(v_as_1686_, 0);
                crate::leanh::lean_inc_ref(v_array_1688_);
                v_start_1689_ = crate::leanh::lean_ctor_get(v_as_1686_, 1);
                crate::leanh::lean_inc(v_start_1689_);
                v_stop_1690_ = crate::leanh::lean_ctor_get(v_as_1686_, 2);
                crate::leanh::lean_inc(v_stop_1690_);
                crate::leanh::lean_dec_ref(v_as_1686_);
                v___x_1691_ = lean_nat_dec_lt(v_start_1689_, v_stop_1690_);
                if v___x_1691_ == 0 {
                    crate::leanh::lean_dec(v_stop_1690_);
                    crate::leanh::lean_dec(v_start_1689_);
                    crate::leanh::lean_dec_ref(v_array_1688_);
                    crate::leanh::lean_dec_ref(v_p_1685_);
                    v___x_1692_ = 1;
                    return v___x_1692_;
                } else {
                    v___x_1693_ = crate::leanh::lean_box((v___x_1691_) as usize);
                    v___f_1694_ = crate::leanh::lean_alloc_closure(
                        l_Subarray_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1694_, 0, v_p_1685_);
                    crate::leanh::lean_closure_set(v___f_1694_, 1, v___x_1693_);
                    v___x_1703_ = lean_array_get_size(v_array_1688_);
                    v___x_1704_ = lean_nat_dec_le(v_stop_1690_, v___x_1703_);
                    if v___x_1704_ == 0 {
                        crate::leanh::lean_dec(v_stop_1690_);
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
                    crate::leanh::lean_dec(v___y_1696_);
                    crate::leanh::lean_dec_ref(v___f_1694_);
                    crate::leanh::lean_dec(v_start_1689_);
                    crate::leanh::lean_dec_ref(v_array_1688_);
                    return v___x_1691_;
                } else {
                    v___x_1698_ = lean_usize_of_nat(v_start_1689_);
                    crate::leanh::lean_dec(v_start_1689_);
                    v___x_1699_ = lean_usize_of_nat(v___y_1696_);
                    crate::leanh::lean_dec(v___y_1696_);
                    v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1687_,
                        v___f_1694_,
                        v_array_1688_,
                        v___x_1698_,
                        v___x_1699_,
                    );
                    v___x_1701_ = (crate::leanh::lean_unbox(v___x_1700_) as u8);
                    crate::leanh::lean_dec(v___x_1700_);
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
    mut v_00_u03b1_1705_: *mut crate::leanh::LeanObject,
    mut v_p_1706_: *mut crate::leanh::LeanObject,
    mut v_as_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1708_: u8 = 0;
    let mut v_r_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Subarray_all(v_00_u03b1_1705_, v_p_1706_, v_as_1707_);
    v_r_1709_ = crate::leanh::lean_box((v_res_1708_) as usize);
    return v_r_1709_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed(
    mut v_inst_1710_: *mut crate::leanh::LeanObject,
    mut v_as_1711_: *mut crate::leanh::LeanObject,
    mut v_f_1712_: *mut crate::leanh::LeanObject,
    mut v_n_1713_: *mut crate::leanh::LeanObject,
    mut v_toPure_1714_: *mut crate::leanh::LeanObject,
    mut v_r_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ =
        l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(
            v_inst_1710_,
            v_as_1711_,
            v_f_1712_,
            v_n_1713_,
            v_toPure_1714_,
            v_r_1715_,
        );
    crate::leanh::lean_dec(v_n_1713_);
    return v_res_1716_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
    mut v_inst_1717_: *mut crate::leanh::LeanObject,
    mut v_as_1718_: *mut crate::leanh::LeanObject,
    mut v_f_1719_: *mut crate::leanh::LeanObject,
    mut v_i_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1725_: u8 = 0;
    v_toApplicative_1721_ = crate::leanh::lean_ctor_get(v_inst_1717_, 0);
    v_toBind_1722_ = crate::leanh::lean_ctor_get(v_inst_1717_, 1);
    crate::leanh::lean_inc(v_toBind_1722_);
    v_toPure_1723_ = crate::leanh::lean_ctor_get(v_toApplicative_1721_, 1);
    crate::leanh::lean_inc(v_toPure_1723_);
    v_zero_1724_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1725_ = lean_nat_dec_eq(v_i_1720_, v_zero_1724_);
    if v_isZero_1725_ == 1 {
        let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_1722_);
        crate::leanh::lean_dec(v_f_1719_);
        crate::leanh::lean_dec_ref(v_as_1718_);
        crate::leanh::lean_dec_ref(v_inst_1717_);
        v___x_1726_ = crate::leanh::lean_box(0);
        v___x_1727_ =
            crate::leanh::lean_apply_2(v_toPure_1723_, crate::leanh::lean_box(0), v___x_1726_);
        return v___x_1727_;
    } else {
        let mut v_one_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_1728_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1729_ = lean_nat_sub(v_i_1720_, v_one_1728_);
        crate::leanh::lean_inc(v_n_1729_);
        crate::leanh::lean_inc(v_f_1719_);
        crate::leanh::lean_inc_ref(v_as_1718_);
        v___f_1730_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_1730_, 0, v_inst_1717_);
        crate::leanh::lean_closure_set(v___f_1730_, 1, v_as_1718_);
        crate::leanh::lean_closure_set(v___f_1730_, 2, v_f_1719_);
        crate::leanh::lean_closure_set(v___f_1730_, 3, v_n_1729_);
        crate::leanh::lean_closure_set(v___f_1730_, 4, v_toPure_1723_);
        v___x_1731_ = l_Subarray_get___redArg(v_as_1718_, v_n_1729_);
        crate::leanh::lean_dec(v_n_1729_);
        crate::leanh::lean_dec_ref(v_as_1718_);
        v___x_1732_ = crate::leanh::lean_apply_1(v_f_1719_, v___x_1731_);
        v___x_1733_ = crate::leanh::lean_apply_4(
            v_toBind_1722_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1732_,
            v___f_1730_,
        );
        return v___x_1733_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___lam__0(
    mut v_inst_1734_: *mut crate::leanh::LeanObject,
    mut v_as_1735_: *mut crate::leanh::LeanObject,
    mut v_f_1736_: *mut crate::leanh::LeanObject,
    mut v_n_1737_: *mut crate::leanh::LeanObject,
    mut v_toPure_1738_: *mut crate::leanh::LeanObject,
    mut v_r_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_1739_) == 0 {
        let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1738_);
        v___x_1740_ =
            l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
                v_inst_1734_,
                v_as_1735_,
                v_f_1736_,
                v_n_1737_,
            );
        return v___x_1740_;
    } else {
        let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1736_);
        crate::leanh::lean_dec_ref(v_as_1735_);
        crate::leanh::lean_dec_ref(v_inst_1734_);
        v___x_1741_ =
            crate::leanh::lean_apply_2(v_toPure_1738_, crate::leanh::lean_box(0), v_r_1739_);
        return v___x_1741_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg___boxed(
    mut v_inst_1742_: *mut crate::leanh::LeanObject,
    mut v_as_1743_: *mut crate::leanh::LeanObject,
    mut v_f_1744_: *mut crate::leanh::LeanObject,
    mut v_i_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1742_,
        v_as_1743_,
        v_f_1744_,
        v_i_1745_,
    );
    crate::leanh::lean_dec(v_i_1745_);
    return v_res_1746_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find(
    mut v_00_u03b1_1747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1748_: *mut crate::leanh::LeanObject,
    mut v_m_1749_: *mut crate::leanh::LeanObject,
    mut v_inst_1750_: *mut crate::leanh::LeanObject,
    mut v_as_1751_: *mut crate::leanh::LeanObject,
    mut v_f_1752_: *mut crate::leanh::LeanObject,
    mut v_i_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1750_,
        v_as_1751_,
        v_f_1752_,
        v_i_1753_,
    );
    return v___x_1755_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___boxed(
    mut v_00_u03b1_1756_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1757_: *mut crate::leanh::LeanObject,
    mut v_m_1758_: *mut crate::leanh::LeanObject,
    mut v_inst_1759_: *mut crate::leanh::LeanObject,
    mut v_as_1760_: *mut crate::leanh::LeanObject,
    mut v_f_1761_: *mut crate::leanh::LeanObject,
    mut v_i_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_i_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Subarray_findSomeRevM_x3f___redArg(
    mut v_inst_1765_: *mut crate::leanh::LeanObject,
    mut v_as_1766_: *mut crate::leanh::LeanObject,
    mut v_f_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_1768_ = crate::leanh::lean_ctor_get(v_as_1766_, 1);
    v_stop_1769_ = crate::leanh::lean_ctor_get(v_as_1766_, 2);
    v___x_1770_ = lean_nat_sub(v_stop_1769_, v_start_1768_);
    v___x_1771_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1765_,
        v_as_1766_,
        v_f_1767_,
        v___x_1770_,
    );
    crate::leanh::lean_dec(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Subarray_findSomeRevM_x3f(
    mut v_00_u03b1_1772_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1773_: *mut crate::leanh::LeanObject,
    mut v_m_1774_: *mut crate::leanh::LeanObject,
    mut v_inst_1775_: *mut crate::leanh::LeanObject,
    mut v_as_1776_: *mut crate::leanh::LeanObject,
    mut v_f_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_1778_ = crate::leanh::lean_ctor_get(v_as_1776_, 1);
    v_stop_1779_ = crate::leanh::lean_ctor_get(v_as_1776_, 2);
    v___x_1780_ = lean_nat_sub(v_stop_1779_, v_start_1778_);
    v___x_1781_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1775_,
        v_as_1776_,
        v_f_1777_,
        v___x_1780_,
    );
    crate::leanh::lean_dec(v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__0(
    mut v_toPure_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1784_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1784_ == 0 {
        let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1783_);
        v___x_1785_ = crate::leanh::lean_box(0);
        v___x_1786_ =
            crate::leanh::lean_apply_2(v_toPure_1782_, crate::leanh::lean_box(0), v___x_1785_);
        return v___x_1786_;
    } else {
        let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1787_, 0, v_a_1783_);
        v___x_1788_ =
            crate::leanh::lean_apply_2(v_toPure_1782_, crate::leanh::lean_box(0), v___x_1787_);
        return v___x_1788_;
    }
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__0___boxed(
    mut v_toPure_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_77__boxed_1792_: u8 = 0;
    let mut v_res_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_77__boxed_1792_ = (crate::leanh::lean_unbox(v_____do__lift_1791_) as u8);
    v_res_1793_ = l_Subarray_findRevM_x3f___redArg___lam__0(
        v_toPure_1789_,
        v_a_1790_,
        v_____do__lift_77__boxed_1792_,
    );
    return v_res_1793_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg___lam__1(
    mut v_toPure_1794_: *mut crate::leanh::LeanObject,
    mut v_p_1795_: *mut crate::leanh::LeanObject,
    mut v_toBind_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1797_);
    v___f_1798_ = crate::leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1798_, 0, v_toPure_1794_);
    crate::leanh::lean_closure_set(v___f_1798_, 1, v_a_1797_);
    v___x_1799_ = crate::leanh::lean_apply_1(v_p_1795_, v_a_1797_);
    v___x_1800_ = crate::leanh::lean_apply_4(
        v_toBind_1796_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1799_,
        v___f_1798_,
    );
    return v___x_1800_;
}
pub unsafe fn l_Subarray_findRevM_x3f___redArg(
    mut v_inst_1801_: *mut crate::leanh::LeanObject,
    mut v_as_1802_: *mut crate::leanh::LeanObject,
    mut v_p_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1804_ = crate::leanh::lean_ctor_get(v_inst_1801_, 0);
    v_toBind_1805_ = crate::leanh::lean_ctor_get(v_inst_1801_, 1);
    v_toPure_1806_ = crate::leanh::lean_ctor_get(v_toApplicative_1804_, 1);
    v_start_1807_ = crate::leanh::lean_ctor_get(v_as_1802_, 1);
    v_stop_1808_ = crate::leanh::lean_ctor_get(v_as_1802_, 2);
    crate::leanh::lean_inc(v_toBind_1805_);
    crate::leanh::lean_inc(v_toPure_1806_);
    v___f_1809_ = crate::leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1809_, 0, v_toPure_1806_);
    crate::leanh::lean_closure_set(v___f_1809_, 1, v_p_1803_);
    crate::leanh::lean_closure_set(v___f_1809_, 2, v_toBind_1805_);
    v___x_1810_ = lean_nat_sub(v_stop_1808_, v_start_1807_);
    v___x_1811_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1801_,
        v_as_1802_,
        v___f_1809_,
        v___x_1810_,
    );
    crate::leanh::lean_dec(v___x_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Subarray_findRevM_x3f(
    mut v_00_u03b1_1812_: *mut crate::leanh::LeanObject,
    mut v_m_1813_: *mut crate::leanh::LeanObject,
    mut v_inst_1814_: *mut crate::leanh::LeanObject,
    mut v_as_1815_: *mut crate::leanh::LeanObject,
    mut v_p_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1817_ = crate::leanh::lean_ctor_get(v_inst_1814_, 0);
    v_toBind_1818_ = crate::leanh::lean_ctor_get(v_inst_1814_, 1);
    v_toPure_1819_ = crate::leanh::lean_ctor_get(v_toApplicative_1817_, 1);
    v_start_1820_ = crate::leanh::lean_ctor_get(v_as_1815_, 1);
    v_stop_1821_ = crate::leanh::lean_ctor_get(v_as_1815_, 2);
    crate::leanh::lean_inc(v_toBind_1818_);
    crate::leanh::lean_inc(v_toPure_1819_);
    v___f_1822_ = crate::leanh::lean_alloc_closure(
        l_Subarray_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1822_, 0, v_toPure_1819_);
    crate::leanh::lean_closure_set(v___f_1822_, 1, v_p_1816_);
    crate::leanh::lean_closure_set(v___f_1822_, 2, v_toBind_1818_);
    v___x_1823_ = lean_nat_sub(v_stop_1821_, v_start_1820_);
    v___x_1824_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v_inst_1814_,
        v_as_1815_,
        v___f_1822_,
        v___x_1823_,
    );
    crate::leanh::lean_dec(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Subarray_findRev_x3f___redArg___lam__0(
    mut v_p_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    crate::leanh::lean_inc(v_a_1826_);
    v___x_1827_ = crate::leanh::lean_apply_1(v_p_1825_, v_a_1826_);
    v___x_1828_ = (crate::leanh::lean_unbox(v___x_1827_) as u8);
    if v___x_1828_ == 0 {
        let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1826_);
        v___x_1829_ = crate::leanh::lean_box(0);
        return v___x_1829_;
    } else {
        let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1830_, 0, v_a_1826_);
        return v___x_1830_;
    }
}
pub unsafe fn l_Subarray_findRev_x3f___redArg(
    mut v_as_1831_: *mut crate::leanh::LeanObject,
    mut v_p_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Subarray_foldr___redArg___closed__9;
    v_start_1834_ = crate::leanh::lean_ctor_get(v_as_1831_, 1);
    v_stop_1835_ = crate::leanh::lean_ctor_get(v_as_1831_, 2);
    v___f_1836_ = crate::leanh::lean_alloc_closure(
        l_Subarray_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1836_, 0, v_p_1832_);
    v___x_1837_ = lean_nat_sub(v_stop_1835_, v_start_1834_);
    v___x_1838_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v___x_1833_,
        v_as_1831_,
        v___f_1836_,
        v___x_1837_,
    );
    crate::leanh::lean_dec(v___x_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Subarray_findRev_x3f(
    mut v_00_u03b1_1839_: *mut crate::leanh::LeanObject,
    mut v_as_1840_: *mut crate::leanh::LeanObject,
    mut v_p_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Subarray_foldr___redArg___closed__9;
    v_start_1843_ = crate::leanh::lean_ctor_get(v_as_1840_, 1);
    v_stop_1844_ = crate::leanh::lean_ctor_get(v_as_1840_, 2);
    v___f_1845_ = crate::leanh::lean_alloc_closure(
        l_Subarray_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1845_, 0, v_p_1841_);
    v___x_1846_ = lean_nat_sub(v_stop_1844_, v_start_1843_);
    v___x_1847_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___redArg(
        v___x_1842_,
        v_as_1840_,
        v___f_1845_,
        v___x_1846_,
    );
    crate::leanh::lean_dec(v___x_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Array_toSubarray___redArg(
    mut v_as_1848_: *mut crate::leanh::LeanObject,
    mut v_start_1849_: *mut crate::leanh::LeanObject,
    mut v_stop_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    v___x_1851_ = lean_array_get_size(v_as_1848_);
    v___x_1852_ = lean_nat_dec_le(v_stop_1850_, v___x_1851_);
    if v___x_1852_ == 0 {
        let mut v___x_1853_: u8 = 0;
        crate::leanh::lean_dec(v_stop_1850_);
        v___x_1853_ = lean_nat_dec_le(v_start_1849_, v___x_1851_);
        if v___x_1853_ == 0 {
            let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_start_1849_);
            v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1854_, 0, v_as_1848_);
            crate::leanh::lean_ctor_set(v___x_1854_, 1, v___x_1851_);
            crate::leanh::lean_ctor_set(v___x_1854_, 2, v___x_1851_);
            return v___x_1854_;
        } else {
            let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1855_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1855_, 0, v_as_1848_);
            crate::leanh::lean_ctor_set(v___x_1855_, 1, v_start_1849_);
            crate::leanh::lean_ctor_set(v___x_1855_, 2, v___x_1851_);
            return v___x_1855_;
        }
    } else {
        let mut v___x_1856_: u8 = 0;
        v___x_1856_ = lean_nat_dec_le(v_start_1849_, v_stop_1850_);
        if v___x_1856_ == 0 {
            let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_start_1849_);
            crate::leanh::lean_inc(v_stop_1850_);
            v___x_1857_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1857_, 0, v_as_1848_);
            crate::leanh::lean_ctor_set(v___x_1857_, 1, v_stop_1850_);
            crate::leanh::lean_ctor_set(v___x_1857_, 2, v_stop_1850_);
            return v___x_1857_;
        } else {
            let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1858_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1858_, 0, v_as_1848_);
            crate::leanh::lean_ctor_set(v___x_1858_, 1, v_start_1849_);
            crate::leanh::lean_ctor_set(v___x_1858_, 2, v_stop_1850_);
            return v___x_1858_;
        }
    }
}
pub unsafe fn l_Array_toSubarray(
    mut v_00_u03b1_1859_: *mut crate::leanh::LeanObject,
    mut v_as_1860_: *mut crate::leanh::LeanObject,
    mut v_start_1861_: *mut crate::leanh::LeanObject,
    mut v_stop_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Array_toSubarray___redArg(v_as_1860_, v_start_1861_, v_stop_1862_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__5;
    v___x_1981_ = l_String_toRawSubstring_x27(v___x_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(
    mut v_x_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    v___x_1998_ = l_Array_term_____x5b___x3a___x5d___closed__2;
    crate::leanh::lean_inc(v_x_1995_);
    v___x_1999_ = l_Lean_Syntax_isOfKind(v_x_1995_, v___x_1998_);
    if v___x_1999_ == 0 {
        let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1995_);
        v___x_2000_ = crate::leanh::lean_box(1);
        v___x_2001_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_2000_);
        crate::leanh::lean_ctor_set(v___x_2001_, 1, v_a_1997_);
        return v___x_2001_;
    } else {
        let mut v_quotContext_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: u8 = 0;
        let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2002_ = crate::leanh::lean_ctor_get(v_a_1996_, 1);
        v_currMacroScope_2003_ = crate::leanh::lean_ctor_get(v_a_1996_, 2);
        v_ref_2004_ = crate::leanh::lean_ctor_get(v_a_1996_, 5);
        v___x_2005_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2006_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2005_);
        v___x_2007_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2008_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2007_);
        v___x_2009_ = crate::leanh::lean_unsigned_to_nat(4);
        v___x_2010_ = l_Lean_Syntax_getArg(v_x_1995_, v___x_2009_);
        crate::leanh::lean_dec(v_x_1995_);
        v___x_2011_ = 0;
        v___x_2012_ = l_Lean_SourceInfo_fromRef(v_ref_2004_, v___x_2011_);
        v___x_2013_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2015_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        crate::leanh::lean_inc(v_currMacroScope_2003_);
        crate::leanh::lean_inc(v_quotContext_2002_);
        v___x_2016_ =
            l_Lean_addMacroScope(v_quotContext_2002_, v___x_2015_, v_currMacroScope_2003_);
        v___x_2017_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10;
        crate::leanh::lean_inc_n(v___x_2012_, 2);
        v___x_2018_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2018_, 0, v___x_2012_);
        crate::leanh::lean_ctor_set(v___x_2018_, 1, v___x_2014_);
        crate::leanh::lean_ctor_set(v___x_2018_, 2, v___x_2016_);
        crate::leanh::lean_ctor_set(v___x_2018_, 3, v___x_2017_);
        v___x_2019_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2020_ = l_Lean_Syntax_node3(
            v___x_2012_,
            v___x_2019_,
            v___x_2006_,
            v___x_2008_,
            v___x_2010_,
        );
        v___x_2021_ = l_Lean_Syntax_node2(v___x_2012_, v___x_2013_, v___x_2018_, v___x_2020_);
        v___x_2022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
        crate::leanh::lean_ctor_set(v___x_2022_, 1, v_a_1997_);
        return v___x_2022_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___boxed(
    mut v_x_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1(v_x_2023_, v_a_2024_, v_a_2025_);
    crate::leanh::lean_dec_ref(v_a_2024_);
    return v_res_2026_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(
    mut v_x_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    v___x_2034_ = l_Array_term_____x5b_x3a___x5d___closed__1;
    crate::leanh::lean_inc(v_x_2031_);
    v___x_2035_ = l_Lean_Syntax_isOfKind(v_x_2031_, v___x_2034_);
    if v___x_2035_ == 0 {
        let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2031_);
        v___x_2036_ = crate::leanh::lean_box(1);
        v___x_2037_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2037_, 1, v_a_2033_);
        return v___x_2037_;
    } else {
        let mut v_quotContext_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: u8 = 0;
        let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2038_ = crate::leanh::lean_ctor_get(v_a_2032_, 1);
        v_currMacroScope_2039_ = crate::leanh::lean_ctor_get(v_a_2032_, 2);
        v_ref_2040_ = crate::leanh::lean_ctor_get(v_a_2032_, 5);
        v___x_2041_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2042_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2041_);
        v___x_2043_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_2044_ = l_Lean_Syntax_getArg(v_x_2031_, v___x_2043_);
        crate::leanh::lean_dec(v_x_2031_);
        v___x_2045_ = 0;
        v___x_2046_ = l_Lean_SourceInfo_fromRef(v_ref_2040_, v___x_2045_);
        v___x_2047_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2049_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        crate::leanh::lean_inc(v_currMacroScope_2039_);
        crate::leanh::lean_inc(v_quotContext_2038_);
        v___x_2050_ =
            l_Lean_addMacroScope(v_quotContext_2038_, v___x_2049_, v_currMacroScope_2039_);
        v___x_2051_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__10;
        crate::leanh::lean_inc_n(v___x_2046_, 4);
        v___x_2052_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2046_);
        crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2048_);
        crate::leanh::lean_ctor_set(v___x_2052_, 2, v___x_2050_);
        crate::leanh::lean_ctor_set(v___x_2052_, 3, v___x_2051_);
        v___x_2053_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2054_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__1;
        v___x_2055_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___closed__2;
        v___x_2056_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2046_);
        crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        v___x_2057_ = l_Lean_Syntax_node1(v___x_2046_, v___x_2054_, v___x_2056_);
        v___x_2058_ = l_Lean_Syntax_node3(
            v___x_2046_,
            v___x_2053_,
            v___x_2042_,
            v___x_2057_,
            v___x_2044_,
        );
        v___x_2059_ = l_Lean_Syntax_node2(v___x_2046_, v___x_2047_, v___x_2052_, v___x_2058_);
        v___x_2060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
        crate::leanh::lean_ctor_set(v___x_2060_, 1, v_a_2033_);
        return v___x_2060_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1___boxed(
    mut v_x_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b_x3a___x5d__1(v_x_2061_, v_a_2062_, v_a_2063_);
    crate::leanh::lean_dec_ref(v_a_2062_);
    return v_res_2064_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_2077_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__11;
    v___x_2098_ = l_String_toRawSubstring_x27(v___x_2097_);
    return v___x_2098_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__18;
    v___x_2111_ = l_String_toRawSubstring_x27(v___x_2110_);
    return v___x_2111_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(
    mut v_x_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    v___x_2119_ = l_Array_term_____x5b___x3a_x5d___closed__1;
    crate::leanh::lean_inc(v_x_2116_);
    v___x_2120_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2119_);
    if v___x_2120_ == 0 {
        let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2116_);
        v___x_2121_ = crate::leanh::lean_box(1);
        v___x_2122_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2122_, 0, v___x_2121_);
        crate::leanh::lean_ctor_set(v___x_2122_, 1, v_a_2118_);
        return v___x_2122_;
    } else {
        let mut v_quotContext_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: u8 = 0;
        let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2123_ = crate::leanh::lean_ctor_get(v_a_2117_, 1);
        v_currMacroScope_2124_ = crate::leanh::lean_ctor_get(v_a_2117_, 2);
        v_ref_2125_ = crate::leanh::lean_ctor_get(v_a_2117_, 5);
        v___x_2126_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2127_ = l_Lean_Syntax_getArg(v_x_2116_, v___x_2126_);
        v___x_2128_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2129_ = l_Lean_Syntax_getArg(v_x_2116_, v___x_2128_);
        crate::leanh::lean_dec(v_x_2116_);
        v___x_2130_ = 0;
        v___x_2131_ = l_Lean_SourceInfo_fromRef(v_ref_2125_, v___x_2130_);
        v___x_2132_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__0;
        v___x_2133_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__1;
        crate::leanh::lean_inc_n(v___x_2131_, 13);
        v___x_2134_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2134_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2134_, 1, v___x_2132_);
        v___x_2135_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__3;
        v___x_2136_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__12;
        v___x_2137_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__4);
        v___x_2138_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2136_);
        crate::leanh::lean_ctor_set(v___x_2138_, 2, v___x_2137_);
        crate::leanh::lean_inc_ref_n(v___x_2138_, 2);
        v___x_2139_ = l_Lean_Syntax_node1(v___x_2131_, v___x_2135_, v___x_2138_);
        v___x_2140_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__6;
        v___x_2141_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__8;
        v___x_2142_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__10;
        v___x_2143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__12);
        v___x_2144_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__13;
        crate::leanh::lean_inc_n(v_currMacroScope_2124_, 3);
        crate::leanh::lean_inc_n(v_quotContext_2123_, 3);
        v___x_2145_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2144_, v_currMacroScope_2124_);
        v___x_2146_ = crate::leanh::lean_box(0);
        v___x_2147_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2143_);
        crate::leanh::lean_ctor_set(v___x_2147_, 2, v___x_2145_);
        crate::leanh::lean_ctor_set(v___x_2147_, 3, v___x_2146_);
        crate::leanh::lean_inc_ref(v___x_2147_);
        v___x_2148_ = l_Lean_Syntax_node1(v___x_2131_, v___x_2142_, v___x_2147_);
        v___x_2149_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__14;
        v___x_2150_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2150_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
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
        v___x_2154_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2154_, 1, v___x_2153_);
        v___x_2155_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__4;
        v___x_2156_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__6);
        v___x_2157_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a___x5d__1___closed__8;
        v___x_2158_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2157_, v_currMacroScope_2124_);
        v___x_2159_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__17;
        v___x_2160_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2160_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2160_, 1, v___x_2156_);
        crate::leanh::lean_ctor_set(v___x_2160_, 2, v___x_2158_);
        crate::leanh::lean_ctor_set(v___x_2160_, 3, v___x_2159_);
        v___x_2161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19_once), _init_l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__19);
        v___x_2162_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___closed__21;
        v___x_2163_ =
            l_Lean_addMacroScope(v_quotContext_2123_, v___x_2162_, v_currMacroScope_2124_);
        v___x_2164_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2164_, 1, v___x_2161_);
        crate::leanh::lean_ctor_set(v___x_2164_, 2, v___x_2163_);
        crate::leanh::lean_ctor_set(v___x_2164_, 3, v___x_2146_);
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
        v___x_2168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2168_, 0, v___x_2167_);
        crate::leanh::lean_ctor_set(v___x_2168_, 1, v_a_2118_);
        return v___x_2168_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1___boxed(
    mut v_x_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2172_ = l_Array___aux__Init__Data__Array__Subarray______macroRules__Array__term_____x5b___x3a_x5d__1(v_x_2169_, v_a_2170_, v_a_2171_);
    crate::leanh::lean_dec_ref(v_a_2170_);
    return v_res_2172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Subarray(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Subarray(
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
pub unsafe fn initialize_Init_Data_Array_Subarray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Subarray(builtin);
}
