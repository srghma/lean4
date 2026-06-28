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
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_instToFormatOfToString___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToFormatOfToString___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToFormatOfToString___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatOfToString___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_format___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_List_format___redArg___closed__0_value) as *mut LeanObject],
};
static mut l_List_format___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_format___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_List_format___redArg___closed__2_value) as *mut LeanObject],
};
static mut l_List_format___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_format___redArg___closed__3_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_List_format___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__5_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_format___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__6_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_List_format___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__6_value) as *mut LeanObject;
static mut l_List_format___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_format___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_List_format___redArg___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_format___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_List_format___redArg___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_List_format___redArg___closed__5_value) as *mut LeanObject],
};
static mut l_List_format___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__9_value) as *mut LeanObject;
pub static l_List_format___redArg___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_List_format___redArg___closed__6_value) as *mut LeanObject],
};
static mut l_List_format___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_List_format___redArg___closed__10_value) as *mut LeanObject;
pub static l_instToFormatArray___redArg___lam__0___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_instToFormatArray___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instToFormatArray___redArg___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_instToFormatArray___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatArray___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Option_format___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Option_format___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__0_value) as *mut LeanObject;
pub static l_Option_format___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Option_format___redArg___closed__0_value) as *mut LeanObject],
};
static mut l_Option_format___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__1_value) as *mut LeanObject;
pub static l_Option_format___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Option_format___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__2_value) as *mut LeanObject;
pub static l_Option_format___redArg___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Option_format___redArg___closed__2_value) as *mut LeanObject],
};
static mut l_Option_format___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Option_format___redArg___closed__3_value) as *mut LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_instToFormatProd___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_instToFormatProd___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l_instToFormatProd___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instToFormatProd___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_instToFormatProd___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instToFormatProd___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_instToFormatProd___redArg___lam__0___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_instToFormatProd___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_instToFormatProd___redArg___lam__0___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_instToFormatProd___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatProd___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_String_toFormat___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_String_toFormat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_toFormat___closed__0_value) as *mut LeanObject;
pub static l_instToFormatRaw___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToFormatRaw___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToFormatRaw___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatRaw___closed__0_value) as *mut LeanObject;
pub static mut l_instToFormatRaw: *mut LeanObject =
    core::ptr::addr_of!(l_instToFormatRaw___closed__0_value) as *mut LeanObject;
pub unsafe fn l_instToFormatOfToString___redArg___lam__0(
    mut v_a_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v___x_253_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_253_, 0, v_a_252_);
    return v___x_253_;
}
pub unsafe fn l_instToFormatOfToString___redArg(
    mut v_inst_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    v___f_256_ = l_instToFormatOfToString___redArg___closed__0;
    v___x_257_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_257_, 0, lean_box(0));
    lean_closure_set(v___x_257_, 1, lean_box(0));
    lean_closure_set(v___x_257_, 2, lean_box(0));
    lean_closure_set(v___x_257_, 3, v___f_256_);
    lean_closure_set(v___x_257_, 4, v_inst_255_);
    return v___x_257_;
}
pub unsafe fn l_instToFormatOfToString(
    mut v_00_u03b1_258_: *mut LeanObject,
    mut v_inst_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = l_instToFormatOfToString___redArg(v_inst_259_);
    return v___x_260_;
}
pub unsafe fn _init_l_List_format___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    v___x_272_ = l_List_format___redArg___closed__5;
    v___x_273_ = lean_string_length(v___x_272_);
    return v___x_273_;
}
pub unsafe fn _init_l_List_format___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_format___redArg___closed__7),
        core::ptr::addr_of_mut!(l_List_format___redArg___closed__7_once),
        _init_l_List_format___redArg___closed__7,
    );
    v___x_275_ = lean_nat_to_int(v___x_274_);
    return v___x_275_;
}
pub unsafe fn l_List_format___redArg(
    mut v_inst_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_281_) == 0 {
        let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_280_);
        v___x_282_ = l_List_format___redArg___closed__1;
        return v___x_282_;
    } else {
        let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: u8 = 0;
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        v___x_283_ = l_List_format___redArg___closed__4;
        v___x_284_ = l_Std_Format_joinSep___redArg(v_inst_280_, v_x_281_, v___x_283_);
        v___x_285_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_List_format___redArg___closed__8),
            core::ptr::addr_of_mut!(l_List_format___redArg___closed__8_once),
            _init_l_List_format___redArg___closed__8,
        );
        v___x_286_ = l_List_format___redArg___closed__9;
        v___x_287_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_287_, 0, v___x_286_);
        lean_ctor_set(v___x_287_, 1, v___x_284_);
        v___x_288_ = l_List_format___redArg___closed__10;
        v___x_289_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_289_, 0, v___x_287_);
        lean_ctor_set(v___x_289_, 1, v___x_288_);
        v___x_290_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_290_, 0, v___x_285_);
        lean_ctor_set(v___x_290_, 1, v___x_289_);
        v___x_291_ = 0;
        v___x_292_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_292_, 0, v___x_290_);
        lean_ctor_set_uint8(
            v___x_292_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_291_,
        );
        return v___x_292_;
    }
}
pub unsafe fn l_List_format(
    mut v_00_u03b1_293_: *mut LeanObject,
    mut v_inst_294_: *mut LeanObject,
    mut v_x_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    v___x_296_ = l_List_format___redArg(v_inst_294_, v_x_295_);
    return v___x_296_;
}
pub unsafe fn l_instToFormatList___redArg(mut v_inst_297_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_alloc_closure(l_List_format as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_298_, 0, lean_box(0));
    lean_closure_set(v___x_298_, 1, v_inst_297_);
    return v___x_298_;
}
pub unsafe fn l_instToFormatList(
    mut v_00_u03b1_299_: *mut LeanObject,
    mut v_inst_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_alloc_closure(l_List_format as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_301_, 0, lean_box(0));
    lean_closure_set(v___x_301_, 1, v_inst_300_);
    return v___x_301_;
}
pub unsafe fn l_instToFormatArray___redArg___lam__0(
    mut v_inst_305_: *mut LeanObject,
    mut v_a_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_307_ = l_instToFormatArray___redArg___lam__0___closed__1;
    v___x_308_ = lean_array_to_list(v_a_306_);
    v___x_309_ = l_List_format___redArg(v_inst_305_, v___x_308_);
    v___x_310_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_310_, 0, v___x_307_);
    lean_ctor_set(v___x_310_, 1, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_instToFormatArray___redArg(mut v_inst_311_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_312_: *mut LeanObject = core::ptr::null_mut();
    v___f_312_ = lean_alloc_closure(
        l_instToFormatArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_312_, 0, v_inst_311_);
    return v___f_312_;
}
pub unsafe fn l_instToFormatArray(
    mut v_00_u03b1_313_: *mut LeanObject,
    mut v_inst_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_315_: *mut LeanObject = core::ptr::null_mut();
    v___f_315_ = lean_alloc_closure(
        l_instToFormatArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_315_, 0, v_inst_314_);
    return v___f_315_;
}
pub unsafe fn l_Option_format___redArg(
    mut v_inst_322_: *mut LeanObject,
    mut v_x_323_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_323_) == 0 {
        let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_322_);
        v___x_324_ = l_Option_format___redArg___closed__1;
        return v___x_324_;
    } else {
        let mut v_val_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        v_val_325_ = lean_ctor_get(v_x_323_, 0);
        lean_inc(v_val_325_);
        lean_dec_ref_known(v_x_323_, 1);
        v___x_326_ = l_Option_format___redArg___closed__3;
        v___x_327_ = lean_apply_1(v_inst_322_, v_val_325_);
        v___x_328_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_328_, 0, v___x_326_);
        lean_ctor_set(v___x_328_, 1, v___x_327_);
        return v___x_328_;
    }
}
pub unsafe fn l_Option_format(
    mut v_00_u03b1_329_: *mut LeanObject,
    mut v_inst_330_: *mut LeanObject,
    mut v_x_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Option_format___redArg(v_inst_330_, v_x_331_);
    return v___x_332_;
}
pub unsafe fn l_instToFormatOption___redArg(mut v_inst_333_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    v___x_334_ = lean_alloc_closure(l_Option_format as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_334_, 0, lean_box(0));
    lean_closure_set(v___x_334_, 1, v_inst_333_);
    return v___x_334_;
}
pub unsafe fn l_instToFormatOption(
    mut v_00_u03b1_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_alloc_closure(l_Option_format as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_337_, 0, lean_box(0));
    lean_closure_set(v___x_337_, 1, v_inst_336_);
    return v___x_337_;
}
pub unsafe fn _init_l_instToFormatProd___redArg___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = l_instToFormatProd___redArg___lam__0___closed__0;
    v___x_341_ = lean_string_length(v___x_340_);
    return v___x_341_;
}
pub unsafe fn _init_l_instToFormatProd___redArg___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__2_once),
        _init_l_instToFormatProd___redArg___lam__0___closed__2,
    );
    v___x_343_ = lean_nat_to_int(v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_instToFormatProd___redArg___lam__0(
    mut v_inst_348_: *mut LeanObject,
    mut v_inst_349_: *mut LeanObject,
    mut v_x_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_355_: u8 = 0;
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_351_ = lean_ctor_get(v_x_350_, 0);
                v_snd_352_ = lean_ctor_get(v_x_350_, 1);
                v_isSharedCheck_373_ = (!lean_is_exclusive(v_x_350_)) as u8;
                if v_isSharedCheck_373_ == 0 {
                    v___x_354_ = v_x_350_;
                    v_isShared_355_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_352_);
                    lean_inc(v_fst_351_);
                    lean_dec(v_x_350_);
                    v___x_354_ = lean_box(0);
                    v_isShared_355_ = v_isSharedCheck_373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_356_ = lean_apply_1(v_inst_348_, v_fst_351_);
                v___x_357_ = l_List_format___redArg___closed__3;
                if v_isShared_355_ == 0 {
                    lean_ctor_set_tag(v___x_354_, 5);
                    lean_ctor_set(v___x_354_, 1, v___x_357_);
                    lean_ctor_set(v___x_354_, 0, v___x_356_);
                    v___x_359_ = v___x_354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_372_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_356_);
                    lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_357_);
                    v___x_359_ = v_reuseFailAlloc_372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_360_ = lean_box(1);
                v___x_361_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_361_, 0, v___x_359_);
                lean_ctor_set(v___x_361_, 1, v___x_360_);
                v___x_362_ = lean_apply_1(v_inst_349_, v_snd_352_);
                v___x_363_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_363_, 0, v___x_361_);
                lean_ctor_set(v___x_363_, 1, v___x_362_);
                v___x_364_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_instToFormatProd___redArg___lam__0___closed__3_once),
                    _init_l_instToFormatProd___redArg___lam__0___closed__3,
                );
                v___x_365_ = l_instToFormatProd___redArg___lam__0___closed__4;
                v___x_366_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_366_, 0, v___x_365_);
                lean_ctor_set(v___x_366_, 1, v___x_363_);
                v___x_367_ = l_instToFormatProd___redArg___lam__0___closed__5;
                v___x_368_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_368_, 0, v___x_366_);
                lean_ctor_set(v___x_368_, 1, v___x_367_);
                v___x_369_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_369_, 0, v___x_364_);
                lean_ctor_set(v___x_369_, 1, v___x_368_);
                v___x_370_ = 0;
                v___x_371_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_371_, 0, v___x_369_);
                lean_ctor_set_uint8(
                    v___x_371_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_370_,
                );
                return v___x_371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToFormatProd___redArg(
    mut v_inst_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_376_: *mut LeanObject = core::ptr::null_mut();
    v___f_376_ = lean_alloc_closure(
        l_instToFormatProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_376_, 0, v_inst_374_);
    lean_closure_set(v___f_376_, 1, v_inst_375_);
    return v___f_376_;
}
pub unsafe fn l_instToFormatProd(
    mut v_00_u03b1_377_: *mut LeanObject,
    mut v_00_u03b2_378_: *mut LeanObject,
    mut v_inst_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_381_: *mut LeanObject = core::ptr::null_mut();
    v___f_381_ = lean_alloc_closure(
        l_instToFormatProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_381_, 0, v_inst_379_);
    lean_closure_set(v___f_381_, 1, v_inst_380_);
    return v___f_381_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(
    mut v_s_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___closed__0;
    return v___x_385_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0___boxed(
    mut v_s_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v_s_386_);
    lean_dec_ref(v_s_386_);
    return v_res_387_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00String_toFormat_spec__2_spec__2(
    mut v_x_388_: *mut LeanObject,
    mut v_x_389_: *mut LeanObject,
    mut v_x_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v_str_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_390_) == 0 {
                    lean_dec(v_x_388_);
                    return v_x_389_;
                } else {
                    v_head_391_ = lean_ctor_get(v_x_390_, 0);
                    v_tail_392_ = lean_ctor_get(v_x_390_, 1);
                    v_isSharedCheck_406_ = (!lean_is_exclusive(v_x_390_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v___x_394_ = v_x_390_;
                        v_isShared_395_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_392_);
                        lean_inc(v_head_391_);
                        lean_dec(v_x_390_);
                        v___x_394_ = lean_box(0);
                        v_isShared_395_ = v_isSharedCheck_406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_str_396_ = lean_ctor_get(v_head_391_, 0);
                lean_inc_ref(v_str_396_);
                v_startInclusive_397_ = lean_ctor_get(v_head_391_, 1);
                lean_inc(v_startInclusive_397_);
                v_endExclusive_398_ = lean_ctor_get(v_head_391_, 2);
                lean_inc(v_endExclusive_398_);
                lean_dec(v_head_391_);
                lean_inc(v_x_388_);
                if v_isShared_395_ == 0 {
                    lean_ctor_set_tag(v___x_394_, 5);
                    lean_ctor_set(v___x_394_, 1, v_x_388_);
                    lean_ctor_set(v___x_394_, 0, v_x_389_);
                    v___x_400_ = v___x_394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_405_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_389_);
                    lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_388_);
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
                lean_dec(v_endExclusive_398_);
                lean_dec(v_startInclusive_397_);
                lean_dec_ref(v_str_396_);
                v___x_402_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_402_, 0, v___x_401_);
                v___x_403_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_403_, 0, v___x_400_);
                lean_ctor_set(v___x_403_, 1, v___x_402_);
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
    mut v_x_407_: *mut LeanObject,
    mut v_x_408_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_407_) == 0 {
        let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_408_);
        v___x_409_ = lean_box(0);
        return v___x_409_;
    } else {
        let mut v_tail_410_: *mut LeanObject = core::ptr::null_mut();
        v_tail_410_ = lean_ctor_get(v_x_407_, 1);
        if lean_obj_tag(v_tail_410_) == 0 {
            let mut v_head_411_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_412_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startInclusive_413_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endExclusive_414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_408_);
            v_head_411_ = lean_ctor_get(v_x_407_, 0);
            lean_inc(v_head_411_);
            lean_dec_ref_known(v_x_407_, 2);
            v_str_412_ = lean_ctor_get(v_head_411_, 0);
            lean_inc_ref(v_str_412_);
            v_startInclusive_413_ = lean_ctor_get(v_head_411_, 1);
            lean_inc(v_startInclusive_413_);
            v_endExclusive_414_ = lean_ctor_get(v_head_411_, 2);
            lean_inc(v_endExclusive_414_);
            lean_dec(v_head_411_);
            v___x_415_ =
                lean_string_utf8_extract(v_str_412_, v_startInclusive_413_, v_endExclusive_414_);
            lean_dec(v_endExclusive_414_);
            lean_dec(v_startInclusive_413_);
            lean_dec_ref(v_str_412_);
            v___x_416_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_416_, 0, v___x_415_);
            return v___x_416_;
        } else {
            let mut v_head_417_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startInclusive_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endExclusive_420_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_410_);
            v_head_417_ = lean_ctor_get(v_x_407_, 0);
            lean_inc(v_head_417_);
            lean_dec_ref_known(v_x_407_, 2);
            v_str_418_ = lean_ctor_get(v_head_417_, 0);
            lean_inc_ref(v_str_418_);
            v_startInclusive_419_ = lean_ctor_get(v_head_417_, 1);
            lean_inc(v_startInclusive_419_);
            v_endExclusive_420_ = lean_ctor_get(v_head_417_, 2);
            lean_inc(v_endExclusive_420_);
            lean_dec(v_head_417_);
            v___x_421_ =
                lean_string_utf8_extract(v_str_418_, v_startInclusive_419_, v_endExclusive_420_);
            lean_dec(v_endExclusive_420_);
            lean_dec(v_startInclusive_419_);
            lean_dec_ref(v_str_418_);
            v___x_422_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_422_, 0, v___x_421_);
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
    mut v_s_424_: *mut LeanObject,
    mut v___x_425_: *mut LeanObject,
    mut v___x_426_: *mut LeanObject,
    mut v_a_427_: *mut LeanObject,
    mut v_b_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_440_: u8 = 0;
    let mut v_startInclusive_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: u32 = 0;
    let mut v___x_446_: u32 = 0;
    let mut v___x_447_: u8 = 0;
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_427_) == 0 {
                    v_currPos_436_ = lean_ctor_get(v_a_427_, 0);
                    v_searcher_437_ = lean_ctor_get(v_a_427_, 1);
                    v_isSharedCheck_463_ = (!lean_is_exclusive(v_a_427_)) as u8;
                    if v_isSharedCheck_463_ == 0 {
                        v___x_439_ = v_a_427_;
                        v_isShared_440_ = v_isSharedCheck_463_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_437_);
                        lean_inc(v_currPos_436_);
                        lean_dec(v_a_427_);
                        v___x_439_ = lean_box(0);
                        v_isShared_440_ = v_isSharedCheck_463_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_426_);
                    lean_dec_ref(v_s_424_);
                    return v_b_428_;
                }
            }
            1 => {
                lean_inc_ref(v_s_424_);
                v___x_433_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_433_, 0, v_s_424_);
                lean_ctor_set(v___x_433_, 1, v_startInclusive_431_);
                lean_ctor_set(v___x_433_, 2, v_endExclusive_432_);
                v___x_434_ = lean_array_push(v_b_428_, v___x_433_);
                v_a_427_ = v_it_430_;
                v_b_428_ = v___x_434_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_441_ = lean_ctor_get(v___x_425_, 1);
                v_endExclusive_442_ = lean_ctor_get(v___x_425_, 2);
                v___x_443_ = lean_nat_sub(v_endExclusive_442_, v_startInclusive_441_);
                v___x_444_ = lean_nat_dec_eq(v_searcher_437_, v___x_443_);
                lean_dec(v___x_443_);
                if v___x_444_ == 0 {
                    v___x_445_ = 10;
                    v___x_446_ = lean_string_utf8_get_fast(v_s_424_, v_searcher_437_);
                    v___x_447_ = lean_uint32_dec_eq(v___x_446_, v___x_445_);
                    if v___x_447_ == 0 {
                        v___x_448_ = lean_string_utf8_next_fast(v_s_424_, v_searcher_437_);
                        lean_dec(v_searcher_437_);
                        if v_isShared_440_ == 0 {
                            lean_ctor_set(v___x_439_, 1, v___x_448_);
                            v___x_450_ = v___x_439_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_452_, 0, v_currPos_436_);
                            lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_448_);
                            v___x_450_ = v_reuseFailAlloc_452_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_453_ = lean_string_utf8_next_fast(v_s_424_, v_searcher_437_);
                        v___x_454_ = lean_nat_sub(v___x_453_, v_searcher_437_);
                        v___x_455_ = lean_nat_add(v_searcher_437_, v___x_454_);
                        lean_dec(v___x_454_);
                        v_slice_456_ = l_String_Slice_subslice_x21(
                            v___x_425_,
                            v_currPos_436_,
                            v_searcher_437_,
                        );
                        lean_inc(v___x_455_);
                        if v_isShared_440_ == 0 {
                            lean_ctor_set(v___x_439_, 1, v___x_455_);
                            lean_ctor_set(v___x_439_, 0, v___x_455_);
                            v_nextIt_458_ = v___x_439_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
                            lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_455_);
                            v_nextIt_458_ = v_reuseFailAlloc_461_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_439_);
                    lean_dec(v_searcher_437_);
                    v___x_462_ = lean_box(1);
                    lean_inc(v___x_426_);
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
                v_startInclusive_459_ = lean_ctor_get(v_slice_456_, 0);
                lean_inc(v_startInclusive_459_);
                v_endExclusive_460_ = lean_ctor_get(v_slice_456_, 1);
                lean_inc(v_endExclusive_460_);
                lean_dec_ref(v_slice_456_);
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
    mut v_s_464_: *mut LeanObject,
    mut v___x_465_: *mut LeanObject,
    mut v___x_466_: *mut LeanObject,
    mut v_a_467_: *mut LeanObject,
    mut v_b_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_469_: *mut LeanObject = core::ptr::null_mut();
    v_res_469_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_464_, v___x_465_, v___x_466_, v_a_467_, v_b_468_);
    lean_dec_ref(v___x_465_);
    return v_res_469_;
}
pub unsafe fn l_String_toFormat(mut v_s_472_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_473_ = lean_unsigned_to_nat(0);
    v___x_474_ = lean_string_utf8_byte_size(v_s_472_);
    lean_inc_ref(v_s_472_);
    v___x_475_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_475_, 0, v_s_472_);
    lean_ctor_set(v___x_475_, 1, v___x_473_);
    lean_ctor_set(v___x_475_, 2, v___x_474_);
    v___x_476_ = l_String_Slice_splitToSubslice___at___00String_toFormat_spec__0(v___x_475_);
    v___x_477_ = l_String_toFormat___closed__0;
    v___x_478_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_472_, v___x_475_, v___x_474_, v___x_476_, v___x_477_);
    lean_dec_ref_known(v___x_475_, 3);
    v___x_479_ = lean_array_to_list(v___x_478_);
    v___x_480_ = lean_box(1);
    v___x_481_ = l_Std_Format_joinSep___at___00String_toFormat_spec__2(v___x_479_, v___x_480_);
    return v___x_481_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(
    mut v_s_482_: *mut LeanObject,
    mut v___x_483_: *mut LeanObject,
    mut v___x_484_: *mut LeanObject,
    mut v_inst_485_: *mut LeanObject,
    mut v_R_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_b_488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v___x_489_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___redArg(v_s_482_, v___x_483_, v___x_484_, v_a_487_, v_b_488_);
    return v___x_489_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1___boxed(
    mut v_s_490_: *mut LeanObject,
    mut v___x_491_: *mut LeanObject,
    mut v___x_492_: *mut LeanObject,
    mut v_inst_493_: *mut LeanObject,
    mut v_R_494_: *mut LeanObject,
    mut v_a_495_: *mut LeanObject,
    mut v_b_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_497_: *mut LeanObject = core::ptr::null_mut();
    v_res_497_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00String_toFormat_spec__1(v_s_490_, v___x_491_, v___x_492_, v_inst_493_, v_R_494_, v_a_495_, v_b_496_);
    lean_dec_ref(v___x_491_);
    return v_res_497_;
}
pub unsafe fn l_instToFormatRaw___lam__0(mut v_p_498_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Nat_reprFast(v_p_498_);
    v___x_500_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_500_, 0, v___x_499_);
    return v___x_500_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Instances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Instances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Instances(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Format_Instances(builtin);
}
