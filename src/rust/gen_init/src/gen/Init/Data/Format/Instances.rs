// Lean compiler output
// Module: Init.Data.Format.Instances
// Imports: Init.Data.String.Search Init.Data.ToString.Basic Init.Data.Iterators.Consumers.Collect
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_joinSep___redArg;
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
    lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
pub static l_instToFormatOfToString___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToFormatOfToString___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToFormatOfToString___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatOfToString___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [91, 93, 0],
    };
static mut l_List_format___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_format___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_format___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_List_format___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_format___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_format___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_format___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_format___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__5_value: crate::leanh::LeanStringObject<2> =
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
static mut l_List_format___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__6_value: crate::leanh::LeanStringObject<2> =
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
static mut l_List_format___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_List_format___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_format___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_format___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_format___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_format___redArg___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_format___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_format___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_format___redArg___closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_format___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_format___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_instToFormatArray___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_instToFormatArray___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToFormatArray___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instToFormatArray___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_format___redArg___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Option_format___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_format___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Option_format___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Option_format___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_format___redArg___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [115, 111, 109, 101, 32, 0],
    };
static mut l_Option_format___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_format___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Option_format___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Option_format___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_instToFormatProd___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_instToFormatProd___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_instToFormatProd___redArg___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToFormatProd___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToFormatProd___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToFormatProd___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instToFormatProd___redArg___lam__0___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instToFormatProd___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instToFormatProd___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_String_toFormat___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_String_toFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_toFormat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToFormatRaw___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToFormatRaw___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToFormatRaw___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToFormatRaw: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToFormatRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_instToFormatOfToString___redArg___lam__0(
    mut v_a_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_253_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_253_, 0, v_a_252_);
    return v___x_253_;
}
pub unsafe fn l_instToFormatOfToString___redArg(
    mut v_inst_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_256_ = l_instToFormatOfToString___redArg___closed__0;
    v___x_257_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_257_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_257_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_257_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_257_, 3, v___f_256_);
    crate::leanh::lean_closure_set(v___x_257_, 4, v_inst_255_);
    return v___x_257_;
}
pub unsafe fn l_instToFormatOfToString(
    mut v_00_u03b1_258_: *mut crate::leanh::LeanObject,
    mut v_inst_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = l_instToFormatOfToString___redArg(v_inst_259_);
    return v___x_260_;
}
pub unsafe fn _init_l_List_format___redArg___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_List_format___redArg___closed__5;
    v___x_273_ = lean_string_length(v___x_272_);
    return v___x_273_;
}
pub unsafe fn _init_l_List_format___redArg___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_format___redArg___closed__7),
        core::ptr::addr_of_mut!(l_List_format___redArg___closed__7_once),
        _init_l_List_format___redArg___closed__7,
    );
    v___x_275_ = lean_nat_to_int(v___x_274_);
    return v___x_275_;
}
pub unsafe fn l_List_format___redArg(
    mut v_inst_280_: *mut crate::leanh::LeanObject,
    mut v_x_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_281_) == 0 {
        let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_280_);
        v___x_282_ = l_List_format___redArg___closed__1;
        return v___x_282_;
    } else {
        let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: u8 = 0;
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_283_ = l_List_format___redArg___closed__4;
        v___x_284_ = l_Std_Format_joinSep___redArg(v_inst_280_, v_x_281_, v___x_283_);
        v___x_285_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_List_format___redArg___closed__8),
            core::ptr::addr_of_mut!(l_List_format___redArg___closed__8_once),
            _init_l_List_format___redArg___closed__8,
        );
        v___x_286_ = l_List_format___redArg___closed__9;
        v___x_287_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
        crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_284_);
        v___x_288_ = l_List_format___redArg___closed__10;
        v___x_289_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_289_, 0, v___x_287_);
        crate::leanh::lean_ctor_set(v___x_289_, 1, v___x_288_);
        v___x_290_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_290_, 0, v___x_285_);
        crate::leanh::lean_ctor_set(v___x_290_, 1, v___x_289_);
        v___x_291_ = 0;
        v___x_292_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_292_, 0, v___x_290_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_292_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_291_,
        );
        return v___x_292_;
    }
}
pub unsafe fn l_List_format(
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_x_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_296_ = l_List_format___redArg(v_inst_294_, v_x_295_);
    return v___x_296_;
}
pub unsafe fn l_instToFormatList___redArg(
    mut v_inst_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = crate::leanh::lean_alloc_closure(l_List_format as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_298_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_298_, 1, v_inst_297_);
    return v___x_298_;
}
pub unsafe fn l_instToFormatList(
    mut v_00_u03b1_299_: *mut crate::leanh::LeanObject,
    mut v_inst_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = crate::leanh::lean_alloc_closure(l_List_format as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_301_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_301_, 1, v_inst_300_);
    return v___x_301_;
}
pub unsafe fn l_instToFormatArray___redArg___lam__0(
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_a_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_instToFormatArray___redArg___lam__0___closed__1;
    v___x_308_ = lean_array_to_list(v_a_306_);
    v___x_309_ = l_List_format___redArg(v_inst_305_, v___x_308_);
    v___x_310_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_310_, 0, v___x_307_);
    crate::leanh::lean_ctor_set(v___x_310_, 1, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_instToFormatArray___redArg(
    mut v_inst_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_312_ = crate::leanh::lean_alloc_closure(
        l_instToFormatArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_312_, 0, v_inst_311_);
    return v___f_312_;
}
pub unsafe fn l_instToFormatArray(
    mut v_00_u03b1_313_: *mut crate::leanh::LeanObject,
    mut v_inst_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_315_ = crate::leanh::lean_alloc_closure(
        l_instToFormatArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_315_, 0, v_inst_314_);
    return v___f_315_;
}
pub unsafe fn l_Option_format___redArg(
    mut v_inst_322_: *mut crate::leanh::LeanObject,
    mut v_x_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_323_) == 0 {
        let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_322_);
        v___x_324_ = l_Option_format___redArg___closed__1;
        return v___x_324_;
    } else {
        let mut v_val_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_325_ = crate::leanh::lean_ctor_get(v_x_323_, 0);
        crate::leanh::lean_inc(v_val_325_);
        crate::leanh::lean_dec_ref_known(v_x_323_, 1);
        v___x_326_ = l_Option_format___redArg___closed__3;
        v___x_327_ = crate::leanh::lean_apply_1(v_inst_322_, v_val_325_);
        v___x_328_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
        crate::leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
        return v___x_328_;
    }
}
pub unsafe fn l_Option_format(
    mut v_00_u03b1_329_: *mut crate::leanh::LeanObject,
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_x_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Option_format___redArg(v_inst_330_, v_x_331_);
    return v___x_332_;
}
pub unsafe fn l_instToFormatOption___redArg(
    mut v_inst_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = crate::leanh::lean_alloc_closure(l_Option_format as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_334_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_334_, 1, v_inst_333_);
    return v___x_334_;
}
pub unsafe fn l_instToFormatOption(
    mut v_00_u03b1_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ = crate::leanh::lean_alloc_closure(l_Option_format as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_337_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_337_, 1, v_inst_336_);
    return v___x_337_;
}
pub unsafe fn _init_l_instToFormatProd___redArg___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = l_instToFormatProd___redArg___lam__0___closed__0;
    v___x_341_ = lean_string_length(v___x_340_);
    return v___x_341_;
}
pub unsafe fn _init_l_instToFormatProd___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__2_once),
        _init_l_instToFormatProd___redArg___lam__0___closed__2,
    );
    v___x_343_ = lean_nat_to_int(v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_instToFormatProd___redArg___lam__0(
    mut v_inst_348_: *mut crate::leanh::LeanObject,
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_x_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_355_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_351_ = crate::leanh::lean_ctor_get(v_x_350_, 0);
                v_snd_352_ = crate::leanh::lean_ctor_get(v_x_350_, 1);
                v_isSharedCheck_373_ = (!crate::leanh::lean_is_exclusive(v_x_350_)) as u8;
                if v_isSharedCheck_373_ == 0 {
                    v___x_354_ = v_x_350_;
                    v_isShared_355_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_352_);
                    crate::leanh::lean_inc(v_fst_351_);
                    crate::leanh::lean_dec(v_x_350_);
                    v___x_354_ = crate::leanh::lean_box(0);
                    v_isShared_355_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_356_ = crate::leanh::lean_apply_1(v_inst_348_, v_fst_351_);
                v___x_357_ = l_List_format___redArg___closed__3;
                if v_isShared_355_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_354_, 5);
                    crate::leanh::lean_ctor_set(v___x_354_, 1, v___x_357_);
                    crate::leanh::lean_ctor_set(v___x_354_, 0, v___x_356_);
                    v___x_359_ = v___x_354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_372_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_357_);
                    v___x_359_ = v_reuseFailAlloc_372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_360_ = crate::leanh::lean_box(1);
                v___x_361_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_361_, 0, v___x_359_);
                crate::leanh::lean_ctor_set(v___x_361_, 1, v___x_360_);
                v___x_362_ = crate::leanh::lean_apply_1(v_inst_349_, v_snd_352_);
                v___x_363_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_363_, 0, v___x_361_);
                crate::leanh::lean_ctor_set(v___x_363_, 1, v___x_362_);
                v___x_364_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__3_once),
                    _init_l_instToFormatProd___redArg___lam__0___closed__3,
                );
                v___x_365_ = l_instToFormatProd___redArg___lam__0___closed__4;
                v___x_366_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_366_, 0, v___x_365_);
                crate::leanh::lean_ctor_set(v___x_366_, 1, v___x_363_);
                v___x_367_ = l_instToFormatProd___redArg___lam__0___closed__5;
                v___x_368_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_368_, 0, v___x_366_);
                crate::leanh::lean_ctor_set(v___x_368_, 1, v___x_367_);
                v___x_369_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_369_, 0, v___x_364_);
                crate::leanh::lean_ctor_set(v___x_369_, 1, v___x_368_);
                v___x_370_ = 0;
                v___x_371_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_371_, 0, v___x_369_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_370_,
                );
                return v___x_371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToFormatProd___redArg(
    mut v_inst_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_376_ = crate::leanh::lean_alloc_closure(
        l_instToFormatProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_376_, 0, v_inst_374_);
    crate::leanh::lean_closure_set(v___f_376_, 1, v_inst_375_);
    return v___f_376_;
}
pub unsafe fn l_instToFormatProd(
    mut v_00_u03b1_377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_378_: *mut crate::leanh::LeanObject,
    mut v_inst_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_381_ = crate::leanh::lean_alloc_closure(
        l_instToFormatProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_381_, 0, v_inst_379_);
    crate::leanh::lean_closure_set(v___f_381_, 1, v_inst_380_);
    return v___f_381_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(
    mut v_s_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0;
    return v___x_385_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___boxed(
    mut v_s_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v_s_386_);
    crate::leanh::lean_dec_ref(v_s_386_);
    return v_res_387_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(
    mut v_x_388_: *mut crate::leanh::LeanObject,
    mut v_x_389_: *mut crate::leanh::LeanObject,
    mut v_x_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v_str_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_390_) == 0 {
                    crate::leanh::lean_dec(v_x_388_);
                    return v_x_389_;
                } else {
                    v_head_391_ = crate::leanh::lean_ctor_get(v_x_390_, 0);
                    v_tail_392_ = crate::leanh::lean_ctor_get(v_x_390_, 1);
                    v_isSharedCheck_406_ = (!crate::leanh::lean_is_exclusive(v_x_390_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v___x_394_ = v_x_390_;
                        v_isShared_395_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_392_);
                        crate::leanh::lean_inc(v_head_391_);
                        crate::leanh::lean_dec(v_x_390_);
                        v___x_394_ = crate::leanh::lean_box(0);
                        v_isShared_395_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_396_ = crate::leanh::lean_ctor_get(v_head_391_, 0);
                crate::leanh::lean_inc_ref(v_str_396_);
                v_startInclusive_397_ = crate::leanh::lean_ctor_get(v_head_391_, 1);
                crate::leanh::lean_inc(v_startInclusive_397_);
                v_endExclusive_398_ = crate::leanh::lean_ctor_get(v_head_391_, 2);
                crate::leanh::lean_inc(v_endExclusive_398_);
                crate::leanh::lean_dec(v_head_391_);
                crate::leanh::lean_inc(v_x_388_);
                if v_isShared_395_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_394_, 5);
                    crate::leanh::lean_ctor_set(v___x_394_, 1, v_x_388_);
                    crate::leanh::lean_ctor_set(v___x_394_, 0, v_x_389_);
                    v___x_400_ = v___x_394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_405_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_388_);
                    v___x_400_ = v_reuseFailAlloc_405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_401_ = lean_string_utf8_extract(
                    v_str_396_,
                    v_startInclusive_397_,
                    v_endExclusive_398_,
                );
                crate::leanh::lean_dec(v_endExclusive_398_);
                crate::leanh::lean_dec(v_startInclusive_397_);
                crate::leanh::lean_dec_ref(v_str_396_);
                v___x_402_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_402_, 0, v___x_401_);
                v___x_403_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_403_, 0, v___x_400_);
                crate::leanh::lean_ctor_set(v___x_403_, 1, v___x_402_);
                v_x_389_ = v___x_403_;
                v_x_390_ = v_tail_392_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00String_toFormat_spec__2(
    mut v_x_407_: *mut crate::leanh::LeanObject,
    mut v_x_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_407_) == 0 {
        let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_408_);
        v___x_409_ = crate::leanh::lean_box(0);
        return v___x_409_;
    } else {
        let mut v_tail_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_410_ = crate::leanh::lean_ctor_get(v_x_407_, 1);
        if crate::leanh::lean_obj_tag(v_tail_410_) == 0 {
            let mut v_head_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_startInclusive_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_endExclusive_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_408_);
            v_head_411_ = crate::leanh::lean_ctor_get(v_x_407_, 0);
            crate::leanh::lean_inc(v_head_411_);
            crate::leanh::lean_dec_ref_known(v_x_407_, 2);
            v_str_412_ = crate::leanh::lean_ctor_get(v_head_411_, 0);
            crate::leanh::lean_inc_ref(v_str_412_);
            v_startInclusive_413_ = crate::leanh::lean_ctor_get(v_head_411_, 1);
            crate::leanh::lean_inc(v_startInclusive_413_);
            v_endExclusive_414_ = crate::leanh::lean_ctor_get(v_head_411_, 2);
            crate::leanh::lean_inc(v_endExclusive_414_);
            crate::leanh::lean_dec(v_head_411_);
            v___x_415_ =
                lean_string_utf8_extract(v_str_412_, v_startInclusive_413_, v_endExclusive_414_);
            crate::leanh::lean_dec(v_endExclusive_414_);
            crate::leanh::lean_dec(v_startInclusive_413_);
            crate::leanh::lean_dec_ref(v_str_412_);
            v___x_416_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_415_);
            return v___x_416_;
        } else {
            let mut v_head_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_startInclusive_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_endExclusive_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_410_);
            v_head_417_ = crate::leanh::lean_ctor_get(v_x_407_, 0);
            crate::leanh::lean_inc(v_head_417_);
            crate::leanh::lean_dec_ref_known(v_x_407_, 2);
            v_str_418_ = crate::leanh::lean_ctor_get(v_head_417_, 0);
            crate::leanh::lean_inc_ref(v_str_418_);
            v_startInclusive_419_ = crate::leanh::lean_ctor_get(v_head_417_, 1);
            crate::leanh::lean_inc(v_startInclusive_419_);
            v_endExclusive_420_ = crate::leanh::lean_ctor_get(v_head_417_, 2);
            crate::leanh::lean_inc(v_endExclusive_420_);
            crate::leanh::lean_dec(v_head_417_);
            v___x_421_ =
                lean_string_utf8_extract(v_str_418_, v_startInclusive_419_, v_endExclusive_420_);
            crate::leanh::lean_dec(v_endExclusive_420_);
            crate::leanh::lean_dec(v_startInclusive_419_);
            crate::leanh::lean_dec_ref(v_str_418_);
            v___x_422_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
            v___x_423_ =
                l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(
                    v_x_408_,
                    v___x_422_,
                    v_tail_410_,
                );
            return v___x_423_;
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(
    mut v_s_424_: *mut crate::leanh::LeanObject,
    mut v___x_425_: *mut crate::leanh::LeanObject,
    mut v___x_426_: *mut crate::leanh::LeanObject,
    mut v_a_427_: *mut crate::leanh::LeanObject,
    mut v_b_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_440_: u8 = 0;
    let mut v_startInclusive_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: u32 = 0;
    let mut v___x_446_: u32 = 0;
    let mut v___x_447_: u8 = 0;
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_427_) == 0 {
                    v_currPos_436_ = crate::leanh::lean_ctor_get(v_a_427_, 0);
                    v_searcher_437_ = crate::leanh::lean_ctor_get(v_a_427_, 1);
                    v_isSharedCheck_463_ = (!crate::leanh::lean_is_exclusive(v_a_427_)) as u8;
                    if v_isSharedCheck_463_ == 0 {
                        v___x_439_ = v_a_427_;
                        v_isShared_440_ = v_isSharedCheck_463_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_437_);
                        crate::leanh::lean_inc(v_currPos_436_);
                        crate::leanh::lean_dec(v_a_427_);
                        v___x_439_ = crate::leanh::lean_box(0);
                        v_isShared_440_ = v_isSharedCheck_463_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_426_);
                    crate::leanh::lean_dec_ref(v_s_424_);
                    return v_b_428_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_424_);
                v___x_433_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_433_, 0, v_s_424_);
                crate::leanh::lean_ctor_set(v___x_433_, 1, v_startInclusive_431_);
                crate::leanh::lean_ctor_set(v___x_433_, 2, v_endExclusive_432_);
                v___x_434_ = lean_array_push(v_b_428_, v___x_433_);
                v_a_427_ = v_it_430_;
                v_b_428_ = v___x_434_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_441_ = crate::leanh::lean_ctor_get(v___x_425_, 1);
                v_endExclusive_442_ = crate::leanh::lean_ctor_get(v___x_425_, 2);
                v___x_443_ = lean_nat_sub(v_endExclusive_442_, v_startInclusive_441_);
                v___x_444_ = lean_nat_dec_eq(v_searcher_437_, v___x_443_);
                crate::leanh::lean_dec(v___x_443_);
                if v___x_444_ == 0 {
                    v___x_445_ = 10;
                    v___x_446_ = lean_string_utf8_get_fast(v_s_424_, v_searcher_437_);
                    v___x_447_ = lean_uint32_dec_eq(v___x_446_, v___x_445_);
                    if v___x_447_ == 0 {
                        v___x_448_ = lean_string_utf8_next_fast(v_s_424_, v_searcher_437_);
                        crate::leanh::lean_dec(v_searcher_437_);
                        if v_isShared_440_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_439_, 1, v___x_448_);
                            v___x_450_ = v___x_439_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_452_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v_currPos_436_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_448_);
                            v___x_450_ = v_reuseFailAlloc_452_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_453_ = lean_string_utf8_next_fast(v_s_424_, v_searcher_437_);
                        v___x_454_ = lean_nat_sub(v___x_453_, v_searcher_437_);
                        v___x_455_ = lean_nat_add(v_searcher_437_, v___x_454_);
                        crate::leanh::lean_dec(v___x_454_);
                        v_slice_456_ = l_String_Slice_subslice_x21(
                            v___x_425_,
                            v_currPos_436_,
                            v_searcher_437_,
                        );
                        crate::leanh::lean_inc(v___x_455_);
                        if v_isShared_440_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_439_, 1, v___x_455_);
                            crate::leanh::lean_ctor_set(v___x_439_, 0, v___x_455_);
                            v_nextIt_458_ = v___x_439_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_455_);
                            v_nextIt_458_ = v_reuseFailAlloc_461_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_439_);
                    crate::leanh::lean_dec(v_searcher_437_);
                    v___x_462_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_426_);
                    v_it_430_ = v___x_462_;
                    v_startInclusive_431_ = v_currPos_436_;
                    v_endExclusive_432_ = v___x_426_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_427_ = v___x_450_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_459_ = crate::leanh::lean_ctor_get(v_slice_456_, 0);
                crate::leanh::lean_inc(v_startInclusive_459_);
                v_endExclusive_460_ = crate::leanh::lean_ctor_get(v_slice_456_, 1);
                crate::leanh::lean_inc(v_endExclusive_460_);
                crate::leanh::lean_dec_ref(v_slice_456_);
                v_it_430_ = v_nextIt_458_;
                v_startInclusive_431_ = v_startInclusive_459_;
                v_endExclusive_432_ = v_endExclusive_460_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg___boxed(
    mut v_s_464_: *mut crate::leanh::LeanObject,
    mut v___x_465_: *mut crate::leanh::LeanObject,
    mut v___x_466_: *mut crate::leanh::LeanObject,
    mut v_a_467_: *mut crate::leanh::LeanObject,
    mut v_b_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_464_, v___x_465_, v___x_466_, v_a_467_, v_b_468_);
    crate::leanh::lean_dec_ref(v___x_465_);
    return v_res_469_;
}
pub unsafe fn l_String_toFormat(
    mut v_s_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_474_ = lean_string_utf8_byte_size(v_s_472_);
    crate::leanh::lean_inc_ref(v_s_472_);
    v___x_475_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_475_, 0, v_s_472_);
    crate::leanh::lean_ctor_set(v___x_475_, 1, v___x_473_);
    crate::leanh::lean_ctor_set(v___x_475_, 2, v___x_474_);
    v___x_476_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v___x_475_);
    v___x_477_ = l_String_toFormat___closed__0;
    v___x_478_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_472_, v___x_475_, v___x_474_, v___x_476_, v___x_477_);
    crate::leanh::lean_dec_ref_known(v___x_475_, 3);
    v___x_479_ = lean_array_to_list(v___x_478_);
    v___x_480_ = crate::leanh::lean_box(1);
    v___x_481_ = l_Std_Format_joinSep___at___00String_toFormat_spec__2(v___x_479_, v___x_480_);
    return v___x_481_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(
    mut v_s_482_: *mut crate::leanh::LeanObject,
    mut v___x_483_: *mut crate::leanh::LeanObject,
    mut v___x_484_: *mut crate::leanh::LeanObject,
    mut v_inst_485_: *mut crate::leanh::LeanObject,
    mut v_R_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_b_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_482_, v___x_483_, v___x_484_, v_a_487_, v_b_488_);
    return v___x_489_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___boxed(
    mut v_s_490_: *mut crate::leanh::LeanObject,
    mut v___x_491_: *mut crate::leanh::LeanObject,
    mut v___x_492_: *mut crate::leanh::LeanObject,
    mut v_inst_493_: *mut crate::leanh::LeanObject,
    mut v_R_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
    mut v_b_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_497_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(v_s_490_, v___x_491_, v___x_492_, v_inst_493_, v_R_494_, v_a_495_, v_b_496_);
    crate::leanh::lean_dec_ref(v___x_491_);
    return v_res_497_;
}
pub unsafe fn l_instToFormatRaw___lam__0(
    mut v_p_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Nat_reprFast(v_p_498_);
    v___x_500_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_500_, 0, v___x_499_);
    return v___x_500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Instances(
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
pub unsafe fn initialize_Init_Data_Format_Instances(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Format_Instances(builtin);
}
