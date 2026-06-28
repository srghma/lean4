// Lean compiler output
// Module: Std.Sync.StreamMap
// Imports: Std.Data Init.Data.Queue Std.Async.IO
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Queue::{
    initialize_Init_Data_Queue, runtime_initialize_Init_Data_Queue,
};
use crate::r#gen::Std::Async::IO::{initialize_Std_Async_IO, runtime_initialize_Std_Async_IO};
use crate::r#gen::Std::Async::Select::{
    l_Std_Async_Selectable_combine___redArg, l_Std_Async_Selectable_one___redArg,
    l_Std_Async_Selectable_tryOne___redArg,
};
use crate::r#gen::Std::Data::{initialize_Std_Data, runtime_initialize_Std_Data};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Std_StreamMap_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_StreamMap_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_empty___closed__0_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_register___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_StreamMap_register___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__7_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_StreamMap_register___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_StreamMap_register___redArg___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_StreamMap_register___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_register___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_StreamMap_ofArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_StreamMap_ofArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_StreamMap_ofArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_ofArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_StreamMap_get_x3f___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
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
static mut l_Std_StreamMap_get_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_StreamMap_get_x3f___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_AnyAsyncStream_getSelector___redArg(
    mut v_x_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_next_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inst_631_ = lean_ctor_get(v_x_630_, 0);
                lean_inc_ref(v_inst_631_);
                v_a_632_ = lean_ctor_get(v_x_630_, 1);
                lean_inc(v_a_632_);
                lean_dec_ref(v_x_630_);
                v_next_633_ = lean_ctor_get(v_inst_631_, 0);
                v_stop_634_ = lean_ctor_get(v_inst_631_, 1);
                v_isSharedCheck_643_ = (!lean_is_exclusive(v_inst_631_)) as u8;
                if v_isSharedCheck_643_ == 0 {
                    v___x_636_ = v_inst_631_;
                    v_isShared_637_ = v_isSharedCheck_643_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_634_);
                    lean_inc(v_next_633_);
                    lean_dec(v_inst_631_);
                    v___x_636_ = lean_box(0);
                    v_isShared_637_ = v_isSharedCheck_643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_632_);
                v___x_638_ = lean_apply_1(v_next_633_, v_a_632_);
                v___x_639_ = lean_apply_1(v_stop_634_, v_a_632_);
                if v_isShared_637_ == 0 {
                    lean_ctor_set(v___x_636_, 1, v___x_639_);
                    lean_ctor_set(v___x_636_, 0, v___x_638_);
                    v___x_641_ = v___x_636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_638_);
                    lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_639_);
                    v___x_641_ = v_reuseFailAlloc_642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_AnyAsyncStream_getSelector(
    mut v_00_u03b1_644_: *mut LeanObject,
    mut v_x_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Std_AnyAsyncStream_getSelector___redArg(v_x_645_);
    return v___x_646_;
}
pub unsafe fn l_Std_instCoeDepAnyAsyncStreamOfAsyncStream___redArg(
    mut v_x_647_: *mut LeanObject,
    mut v_inst_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    v___x_649_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_649_, 0, v_inst_648_);
    lean_ctor_set(v___x_649_, 1, v_x_647_);
    return v___x_649_;
}
pub unsafe fn l_Std_instCoeDepAnyAsyncStreamOfAsyncStream(
    mut v_t_650_: *mut LeanObject,
    mut v_00_u03b1_651_: *mut LeanObject,
    mut v_x_652_: *mut LeanObject,
    mut v_inst_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_654_, 0, v_inst_653_);
    lean_ctor_set(v___x_654_, 1, v_x_652_);
    return v___x_654_;
}
pub unsafe fn l_Std_StreamMap_empty(
    mut v_00_u03b2_657_: *mut LeanObject,
    mut v_00_u03b1_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    v___x_659_ = l_Std_StreamMap_empty___closed__0;
    return v___x_659_;
}
pub unsafe fn l_Std_StreamMap_register___redArg___lam__0(
    mut v_inst_660_: *mut LeanObject,
    mut v_name_661_: *mut LeanObject,
    mut v_x1_662_: *mut LeanObject,
    mut v_x2_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    v_fst_664_ = lean_ctor_get(v_x2_663_, 0);
    lean_inc(v_fst_664_);
    v___x_665_ = lean_apply_2(v_inst_660_, v_fst_664_, v_name_661_);
    v___x_666_ = (lean_unbox(v___x_665_) as u8);
    if v___x_666_ == 0 {
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        v___x_667_ = lean_array_push(v_x1_662_, v_x2_663_);
        return v___x_667_;
    } else {
        lean_dec_ref(v_x2_663_);
        return v_x1_662_;
    }
}
pub unsafe fn l_Std_StreamMap_register___redArg(
    mut v_inst_687_: *mut LeanObject,
    mut v_inst_688_: *mut LeanObject,
    mut v_sm_689_: *mut LeanObject,
    mut v_name_690_: *mut LeanObject,
    mut v_reader_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_next_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_696_: u8 = 0;
    let mut v_newSelector_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    let mut v___f_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u8 = 0;
    let mut v___x_713_: usize = 0;
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: usize = 0;
    let mut v___x_717_: usize = 0;
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_692_ = lean_ctor_get(v_inst_688_, 0);
                v_stop_693_ = lean_ctor_get(v_inst_688_, 1);
                v_isSharedCheck_719_ = (!lean_is_exclusive(v_inst_688_)) as u8;
                if v_isSharedCheck_719_ == 0 {
                    v___x_695_ = v_inst_688_;
                    v_isShared_696_ = v_isSharedCheck_719_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_693_);
                    lean_inc(v_next_692_);
                    lean_dec(v_inst_688_);
                    v___x_695_ = lean_box(0);
                    v_isShared_696_ = v_isSharedCheck_719_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_reader_691_);
                v_newSelector_697_ = lean_apply_1(v_next_692_, v_reader_691_);
                v___x_706_ = lean_unsigned_to_nat(0);
                v___x_707_ = lean_array_get_size(v_sm_689_);
                v___x_708_ = l_Std_StreamMap_empty___closed__0;
                v___x_709_ = l_Std_StreamMap_register___redArg___closed__9;
                v___x_710_ = lean_nat_dec_lt(v___x_706_, v___x_707_);
                if v___x_710_ == 0 {
                    lean_dec_ref(v_sm_689_);
                    lean_dec_ref(v_inst_687_);
                    v___y_699_ = v___x_708_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_name_690_);
                    v___f_711_ = lean_alloc_closure(
                        l_Std_StreamMap_register___redArg___lam__0 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_711_, 0, v_inst_687_);
                    lean_closure_set(v___f_711_, 1, v_name_690_);
                    v___x_712_ = lean_nat_dec_le(v___x_707_, v___x_707_);
                    if v___x_712_ == 0 {
                        if v___x_710_ == 0 {
                            lean_dec_ref(v___f_711_);
                            lean_dec_ref(v_sm_689_);
                            v___y_699_ = v___x_708_;
                            state = 2;
                            continue;
                        } else {
                            v___x_713_ = 0usize;
                            v___x_714_ = lean_usize_of_nat(v___x_707_);
                            v___x_715_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_709_,
                                    v___f_711_,
                                    v_sm_689_,
                                    v___x_713_,
                                    v___x_714_,
                                    v___x_708_,
                                );
                            v___y_699_ = v___x_715_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_716_ = 0usize;
                        v___x_717_ = lean_usize_of_nat(v___x_707_);
                        v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_709_,
                            v___f_711_,
                            v_sm_689_,
                            v___x_716_,
                            v___x_717_,
                            v___x_708_,
                        );
                        v___y_699_ = v___x_718_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_700_ = lean_apply_1(v_stop_693_, v_reader_691_);
                if v_isShared_696_ == 0 {
                    lean_ctor_set(v___x_695_, 1, v___x_700_);
                    lean_ctor_set(v___x_695_, 0, v_newSelector_697_);
                    v___x_702_ = v___x_695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_705_, 0, v_newSelector_697_);
                    lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_700_);
                    v___x_702_ = v_reuseFailAlloc_705_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_703_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_703_, 0, v_name_690_);
                lean_ctor_set(v___x_703_, 1, v___x_702_);
                v___x_704_ = lean_array_push(v___y_699_, v___x_703_);
                return v___x_704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_StreamMap_register(
    mut v_00_u03b1_720_: *mut LeanObject,
    mut v_t_721_: *mut LeanObject,
    mut v_00_u03b2_722_: *mut LeanObject,
    mut v_inst_723_: *mut LeanObject,
    mut v_inst_724_: *mut LeanObject,
    mut v_sm_725_: *mut LeanObject,
    mut v_name_726_: *mut LeanObject,
    mut v_reader_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Std_StreamMap_register___redArg(
        v_inst_723_,
        v_inst_724_,
        v_sm_725_,
        v_name_726_,
        v_reader_727_,
    );
    return v___x_728_;
}
pub unsafe fn l_Std_StreamMap_ofArray___redArg___lam__0(
    mut v_x_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_734_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_730_ = lean_ctor_get(v_x_729_, 0);
                v_snd_731_ = lean_ctor_get(v_x_729_, 1);
                v_isSharedCheck_739_ = (!lean_is_exclusive(v_x_729_)) as u8;
                if v_isSharedCheck_739_ == 0 {
                    v___x_733_ = v_x_729_;
                    v_isShared_734_ = v_isSharedCheck_739_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_731_);
                    lean_inc(v_fst_730_);
                    lean_dec(v_x_729_);
                    v___x_733_ = lean_box(0);
                    v_isShared_734_ = v_isSharedCheck_739_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_735_ = l_Std_AnyAsyncStream_getSelector___redArg(v_snd_731_);
                if v_isShared_734_ == 0 {
                    lean_ctor_set(v___x_733_, 1, v___x_735_);
                    v___x_737_ = v___x_733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_730_);
                    lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
                    v___x_737_ = v_reuseFailAlloc_738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_StreamMap_ofArray___redArg(
    mut v_streams_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_744_: usize = 0;
    let mut v___x_745_: usize = 0;
    let mut v_arrayOfSelectors_746_: *mut LeanObject = core::ptr::null_mut();
    v___f_742_ = l_Std_StreamMap_ofArray___redArg___closed__0;
    v___x_743_ = l_Std_StreamMap_register___redArg___closed__9;
    v_sz_744_ = lean_array_size(v_streams_741_);
    v___x_745_ = 0usize;
    v_arrayOfSelectors_746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_743_,
        v___f_742_,
        v_sz_744_,
        v___x_745_,
        v_streams_741_,
    );
    return v_arrayOfSelectors_746_;
}
pub unsafe fn l_Std_StreamMap_ofArray(
    mut v_00_u03b1_747_: *mut LeanObject,
    mut v_00_u03b2_748_: *mut LeanObject,
    mut v_inst_749_: *mut LeanObject,
    mut v_streams_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_751_ = l_Std_StreamMap_ofArray___redArg(v_streams_750_);
    return v___x_751_;
}
pub unsafe fn l_Std_StreamMap_ofArray___boxed(
    mut v_00_u03b1_752_: *mut LeanObject,
    mut v_00_u03b2_753_: *mut LeanObject,
    mut v_inst_754_: *mut LeanObject,
    mut v_streams_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Std_StreamMap_ofArray(
        v_00_u03b1_752_,
        v_00_u03b2_753_,
        v_inst_754_,
        v_streams_755_,
    );
    lean_dec_ref(v_inst_754_);
    return v_res_756_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(
    mut v_fst_757_: *mut LeanObject,
    mut v_x_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_760_, 0, v_fst_757_);
    lean_ctor_set(v___x_760_, 1, v_x_758_);
    v___x_761_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_761_, 0, v___x_760_);
    v___x_762_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_762_, 0, v___x_761_);
    return v___x_762_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed(
    mut v_fst_763_: *mut LeanObject,
    mut v_x_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_766_: *mut LeanObject = core::ptr::null_mut();
    v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0(v_fst_763_, v_x_764_);
    return v_res_766_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(
    mut v_sz_767_: usize,
    mut v_i_768_: usize,
    mut v_bs_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: u8 = 0;
    let mut v_v_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: usize = 0;
    let mut v___x_784_: usize = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut v_unused_789_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_770_ = lean_usize_dec_lt(v_i_768_, v_sz_767_);
                if v___x_770_ == 0 {
                    return v_bs_769_;
                } else {
                    v_v_771_ = lean_array_uget_borrowed(v_bs_769_, v_i_768_);
                    v_snd_772_ = lean_ctor_get(v_v_771_, 1);
                    lean_inc(v_snd_772_);
                    v_fst_773_ = lean_ctor_get(v_v_771_, 0);
                    lean_inc(v_fst_773_);
                    v_fst_774_ = lean_ctor_get(v_snd_772_, 0);
                    v_isSharedCheck_788_ = (!lean_is_exclusive(v_snd_772_)) as u8;
                    if v_isSharedCheck_788_ == 0 {
                        v_unused_789_ = lean_ctor_get(v_snd_772_, 1);
                        lean_dec(v_unused_789_);
                        v___x_776_ = v_snd_772_;
                        v_isShared_777_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_774_);
                        lean_dec(v_snd_772_);
                        v___x_776_ = lean_box(0);
                        v_isShared_777_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_778_ = lean_unsigned_to_nat(0);
                v_bs_x27_779_ = lean_array_uset(v_bs_769_, v_i_768_, v___x_778_);
                v___f_780_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_780_, 0, v_fst_773_);
                if v_isShared_777_ == 0 {
                    lean_ctor_set(v___x_776_, 1, v___f_780_);
                    v___x_782_ = v___x_776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_787_, 0, v_fst_774_);
                    lean_ctor_set(v_reuseFailAlloc_787_, 1, v___f_780_);
                    v___x_782_ = v_reuseFailAlloc_787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_783_ = 1usize;
                v___x_784_ = lean_usize_add(v_i_768_, v___x_783_);
                v___x_785_ = lean_array_uset(v_bs_x27_779_, v_i_768_, v___x_782_);
                v_i_768_ = v___x_784_;
                v_bs_769_ = v___x_785_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg___boxed(
    mut v_sz_790_: *mut LeanObject,
    mut v_i_791_: *mut LeanObject,
    mut v_bs_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_793_: usize = 0;
    let mut v_i_boxed_794_: usize = 0;
    let mut v_res_795_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_793_ = lean_unbox_usize(v_sz_790_);
    lean_dec(v_sz_790_);
    v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
    lean_dec(v_i_791_);
    v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_boxed_793_, v_i_boxed_794_, v_bs_792_);
    return v_res_795_;
}
pub unsafe fn l_Std_StreamMap_selector___redArg(
    mut v_stream_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_801_: usize = 0;
    let mut v___x_802_: usize = 0;
    let mut v_selectables_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_808_: u8 = 0;
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_812_: u8 = 0;
    let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_801_ = lean_array_size(v_stream_796_);
                v___x_802_ = 0usize;
                v_selectables_803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_801_, v___x_802_, v_stream_796_);
                v___x_804_ = l_Std_Async_Selectable_combine___redArg(v_selectables_803_);
                if lean_obj_tag(v___x_804_) == 0 {
                    v_a_805_ = lean_ctor_get(v___x_804_, 0);
                    v_isSharedCheck_812_ = (!lean_is_exclusive(v___x_804_)) as u8;
                    if v_isSharedCheck_812_ == 0 {
                        v___x_807_ = v___x_804_;
                        v_isShared_808_ = v_isSharedCheck_812_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_805_);
                        lean_dec(v___x_804_);
                        v___x_807_ = lean_box(0);
                        v_isShared_808_ = v_isSharedCheck_812_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_813_ = lean_ctor_get(v___x_804_, 0);
                    v_isSharedCheck_820_ = (!lean_is_exclusive(v___x_804_)) as u8;
                    if v_isSharedCheck_820_ == 0 {
                        v___x_815_ = v___x_804_;
                        v_isShared_816_ = v_isSharedCheck_820_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_813_);
                        lean_dec(v___x_804_);
                        v___x_815_ = lean_box(0);
                        v_isShared_816_ = v_isSharedCheck_820_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_800_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_800_, 0, v_val_799_);
                return v___x_800_;
            }
            2 => {
                if v_isShared_808_ == 0 {
                    lean_ctor_set_tag(v___x_807_, 1);
                    v___x_810_ = v___x_807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
                    v___x_810_ = v_reuseFailAlloc_811_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_799_ = v___x_810_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_816_ == 0 {
                    lean_ctor_set_tag(v___x_815_, 0);
                    v___x_818_ = v___x_815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
                    v___x_818_ = v_reuseFailAlloc_819_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_799_ = v___x_818_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_StreamMap_selector___redArg___boxed(
    mut v_stream_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_823_: *mut LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_StreamMap_selector___redArg(v_stream_821_);
    return v_res_823_;
}
pub unsafe fn l_Std_StreamMap_selector(
    mut v_00_u03b1_824_: *mut LeanObject,
    mut v_00_u03b2_825_: *mut LeanObject,
    mut v_stream_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ = l_Std_StreamMap_selector___redArg(v_stream_826_);
    return v___x_828_;
}
pub unsafe fn l_Std_StreamMap_selector___boxed(
    mut v_00_u03b1_829_: *mut LeanObject,
    mut v_00_u03b2_830_: *mut LeanObject,
    mut v_stream_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_833_: *mut LeanObject = core::ptr::null_mut();
    v_res_833_ = l_Std_StreamMap_selector(v_00_u03b1_829_, v_00_u03b2_830_, v_stream_831_);
    return v_res_833_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(
    mut v_00_u03b1_834_: *mut LeanObject,
    mut v_00_u03b2_835_: *mut LeanObject,
    mut v_sz_836_: usize,
    mut v_i_837_: usize,
    mut v_bs_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_836_, v_i_837_, v_bs_838_);
    return v___x_839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___boxed(
    mut v_00_u03b1_840_: *mut LeanObject,
    mut v_00_u03b2_841_: *mut LeanObject,
    mut v_sz_842_: *mut LeanObject,
    mut v_i_843_: *mut LeanObject,
    mut v_bs_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_845_: usize = 0;
    let mut v_i_boxed_846_: usize = 0;
    let mut v_res_847_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_845_ = lean_unbox_usize(v_sz_842_);
    lean_dec(v_sz_842_);
    v_i_boxed_846_ = lean_unbox_usize(v_i_843_);
    lean_dec(v_i_843_);
    v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0(v_00_u03b1_840_, v_00_u03b2_841_, v_sz_boxed_845_, v_i_boxed_846_, v_bs_844_);
    return v_res_847_;
}
pub unsafe fn l_Std_StreamMap_recv___redArg(mut v_stream_848_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sz_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v_selectables_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v_sz_850_ = lean_array_size(v_stream_848_);
    v___x_851_ = 0usize;
    v_selectables_852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_850_, v___x_851_, v_stream_848_);
    v___x_853_ = l_Std_Async_Selectable_one___redArg(v_selectables_852_);
    return v___x_853_;
}
pub unsafe fn l_Std_StreamMap_recv___redArg___boxed(
    mut v_stream_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_856_: *mut LeanObject = core::ptr::null_mut();
    v_res_856_ = l_Std_StreamMap_recv___redArg(v_stream_854_);
    return v_res_856_;
}
pub unsafe fn l_Std_StreamMap_recv(
    mut v_00_u03b1_857_: *mut LeanObject,
    mut v_00_u03b2_858_: *mut LeanObject,
    mut v_stream_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Std_StreamMap_recv___redArg(v_stream_859_);
    return v___x_861_;
}
pub unsafe fn l_Std_StreamMap_recv___boxed(
    mut v_00_u03b1_862_: *mut LeanObject,
    mut v_00_u03b2_863_: *mut LeanObject,
    mut v_stream_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_866_: *mut LeanObject = core::ptr::null_mut();
    v_res_866_ = l_Std_StreamMap_recv(v_00_u03b1_862_, v_00_u03b2_863_, v_stream_864_);
    return v_res_866_;
}
pub unsafe fn l_Std_StreamMap_tryRecv___redArg(
    mut v_stream_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_869_: usize = 0;
    let mut v___x_870_: usize = 0;
    let mut v_selectables_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    v_sz_869_ = lean_array_size(v_stream_867_);
    v___x_870_ = 0usize;
    v_selectables_871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_selector_spec__0___redArg(v_sz_869_, v___x_870_, v_stream_867_);
    v___x_872_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_871_);
    return v___x_872_;
}
pub unsafe fn l_Std_StreamMap_tryRecv___redArg___boxed(
    mut v_stream_873_: *mut LeanObject,
    mut v_a_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_875_: *mut LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Std_StreamMap_tryRecv___redArg(v_stream_873_);
    return v_res_875_;
}
pub unsafe fn l_Std_StreamMap_tryRecv(
    mut v_00_u03b1_876_: *mut LeanObject,
    mut v_00_u03b2_877_: *mut LeanObject,
    mut v_stream_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = l_Std_StreamMap_tryRecv___redArg(v_stream_878_);
    return v___x_880_;
}
pub unsafe fn l_Std_StreamMap_tryRecv___boxed(
    mut v_00_u03b1_881_: *mut LeanObject,
    mut v_00_u03b2_882_: *mut LeanObject,
    mut v_stream_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_885_: *mut LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Std_StreamMap_tryRecv(v_00_u03b1_881_, v_00_u03b2_882_, v_stream_883_);
    return v_res_885_;
}
pub unsafe fn l_Std_StreamMap_unregister___redArg(
    mut v_inst_886_: *mut LeanObject,
    mut v_sm_887_: *mut LeanObject,
    mut v_name_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    v___x_889_ = lean_unsigned_to_nat(0);
    v___x_890_ = lean_array_get_size(v_sm_887_);
    v___x_891_ = l_Std_StreamMap_empty___closed__0;
    v___x_892_ = l_Std_StreamMap_register___redArg___closed__9;
    v___x_893_ = lean_nat_dec_lt(v___x_889_, v___x_890_);
    if v___x_893_ == 0 {
        lean_dec(v_name_888_);
        lean_dec_ref(v_sm_887_);
        lean_dec_ref(v_inst_886_);
        return v___x_891_;
    } else {
        let mut v___f_894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_895_: u8 = 0;
        v___f_894_ = lean_alloc_closure(
            l_Std_StreamMap_register___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_894_, 0, v_inst_886_);
        lean_closure_set(v___f_894_, 1, v_name_888_);
        v___x_895_ = lean_nat_dec_le(v___x_890_, v___x_890_);
        if v___x_895_ == 0 {
            if v___x_893_ == 0 {
                lean_dec_ref(v___f_894_);
                lean_dec_ref(v_sm_887_);
                return v___x_891_;
            } else {
                let mut v___x_896_: usize = 0;
                let mut v___x_897_: usize = 0;
                let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
                v___x_896_ = 0usize;
                v___x_897_ = lean_usize_of_nat(v___x_890_);
                v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_892_,
                    v___f_894_,
                    v_sm_887_,
                    v___x_896_,
                    v___x_897_,
                    v___x_891_,
                );
                return v___x_898_;
            }
        } else {
            let mut v___x_899_: usize = 0;
            let mut v___x_900_: usize = 0;
            let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
            v___x_899_ = 0usize;
            v___x_900_ = lean_usize_of_nat(v___x_890_);
            v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_892_,
                v___f_894_,
                v_sm_887_,
                v___x_899_,
                v___x_900_,
                v___x_891_,
            );
            return v___x_901_;
        }
    }
}
pub unsafe fn l_Std_StreamMap_unregister(
    mut v_00_u03b1_902_: *mut LeanObject,
    mut v_00_u03b2_903_: *mut LeanObject,
    mut v_inst_904_: *mut LeanObject,
    mut v_sm_905_: *mut LeanObject,
    mut v_name_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = l_Std_StreamMap_unregister___redArg(v_inst_904_, v_sm_905_, v_name_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_StreamMap_contains___redArg___lam__0(
    mut v_inst_908_: *mut LeanObject,
    mut v_name_909_: *mut LeanObject,
    mut v_x_910_: *mut LeanObject,
) -> u8 {
    let mut v_fst_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: u8 = 0;
    v_fst_911_ = lean_ctor_get(v_x_910_, 0);
    lean_inc(v_fst_911_);
    lean_dec_ref(v_x_910_);
    v___x_912_ = lean_apply_2(v_inst_908_, v_fst_911_, v_name_909_);
    v___x_913_ = (lean_unbox(v___x_912_) as u8);
    return v___x_913_;
}
pub unsafe fn l_Std_StreamMap_contains___redArg___lam__0___boxed(
    mut v_inst_914_: *mut LeanObject,
    mut v_name_915_: *mut LeanObject,
    mut v_x_916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_917_: u8 = 0;
    let mut v_r_918_: *mut LeanObject = core::ptr::null_mut();
    v_res_917_ = l_Std_StreamMap_contains___redArg___lam__0(v_inst_914_, v_name_915_, v_x_916_);
    v_r_918_ = lean_box((v_res_917_) as usize);
    return v_r_918_;
}
pub unsafe fn l_Std_StreamMap_contains___redArg(
    mut v_inst_919_: *mut LeanObject,
    mut v_sm_920_: *mut LeanObject,
    mut v_name_921_: *mut LeanObject,
) -> u8 {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    v___x_922_ = lean_unsigned_to_nat(0);
    v___x_923_ = lean_array_get_size(v_sm_920_);
    v___x_924_ = l_Std_StreamMap_register___redArg___closed__9;
    v___x_925_ = lean_nat_dec_lt(v___x_922_, v___x_923_);
    if v___x_925_ == 0 {
        lean_dec(v_name_921_);
        lean_dec_ref(v_sm_920_);
        lean_dec_ref(v_inst_919_);
        return v___x_925_;
    } else {
        if v___x_925_ == 0 {
            lean_dec(v_name_921_);
            lean_dec_ref(v_sm_920_);
            lean_dec_ref(v_inst_919_);
            return v___x_925_;
        } else {
            let mut v___f_926_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_927_: usize = 0;
            let mut v___x_928_: usize = 0;
            let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_930_: u8 = 0;
            v___f_926_ = lean_alloc_closure(
                l_Std_StreamMap_contains___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_926_, 0, v_inst_919_);
            lean_closure_set(v___f_926_, 1, v_name_921_);
            v___x_927_ = 0usize;
            v___x_928_ = lean_usize_of_nat(v___x_923_);
            v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                lean_box(0),
                lean_box(0),
                v___x_924_,
                v___f_926_,
                v_sm_920_,
                v___x_927_,
                v___x_928_,
            );
            v___x_930_ = (lean_unbox(v___x_929_) as u8);
            lean_dec(v___x_929_);
            return v___x_930_;
        }
    }
}
pub unsafe fn l_Std_StreamMap_contains___redArg___boxed(
    mut v_inst_931_: *mut LeanObject,
    mut v_sm_932_: *mut LeanObject,
    mut v_name_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_934_: u8 = 0;
    let mut v_r_935_: *mut LeanObject = core::ptr::null_mut();
    v_res_934_ = l_Std_StreamMap_contains___redArg(v_inst_931_, v_sm_932_, v_name_933_);
    v_r_935_ = lean_box((v_res_934_) as usize);
    return v_r_935_;
}
pub unsafe fn l_Std_StreamMap_contains(
    mut v_00_u03b1_936_: *mut LeanObject,
    mut v_00_u03b2_937_: *mut LeanObject,
    mut v_inst_938_: *mut LeanObject,
    mut v_sm_939_: *mut LeanObject,
    mut v_name_940_: *mut LeanObject,
) -> u8 {
    let mut v___x_941_: u8 = 0;
    v___x_941_ = l_Std_StreamMap_contains___redArg(v_inst_938_, v_sm_939_, v_name_940_);
    return v___x_941_;
}
pub unsafe fn l_Std_StreamMap_contains___boxed(
    mut v_00_u03b1_942_: *mut LeanObject,
    mut v_00_u03b2_943_: *mut LeanObject,
    mut v_inst_944_: *mut LeanObject,
    mut v_sm_945_: *mut LeanObject,
    mut v_name_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_947_: u8 = 0;
    let mut v_r_948_: *mut LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Std_StreamMap_contains(
        v_00_u03b1_942_,
        v_00_u03b2_943_,
        v_inst_944_,
        v_sm_945_,
        v_name_946_,
    );
    v_r_948_ = lean_box((v_res_947_) as usize);
    return v_r_948_;
}
pub unsafe fn l_Std_StreamMap_size___redArg(mut v_sm_949_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_950_ = lean_array_get_size(v_sm_949_);
    return v___x_950_;
}
pub unsafe fn l_Std_StreamMap_size___redArg___boxed(
    mut v_sm_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Std_StreamMap_size___redArg(v_sm_951_);
    lean_dec_ref(v_sm_951_);
    return v_res_952_;
}
pub unsafe fn l_Std_StreamMap_size(
    mut v_00_u03b1_953_: *mut LeanObject,
    mut v_00_u03b2_954_: *mut LeanObject,
    mut v_sm_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    v___x_956_ = lean_array_get_size(v_sm_955_);
    return v___x_956_;
}
pub unsafe fn l_Std_StreamMap_size___boxed(
    mut v_00_u03b1_957_: *mut LeanObject,
    mut v_00_u03b2_958_: *mut LeanObject,
    mut v_sm_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_960_: *mut LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Std_StreamMap_size(v_00_u03b1_957_, v_00_u03b2_958_, v_sm_959_);
    lean_dec_ref(v_sm_959_);
    return v_res_960_;
}
pub unsafe fn l_Std_StreamMap_isEmpty___redArg(mut v_sm_961_: *mut LeanObject) -> u8 {
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    v___x_962_ = lean_array_get_size(v_sm_961_);
    v___x_963_ = lean_unsigned_to_nat(0);
    v___x_964_ = lean_nat_dec_eq(v___x_962_, v___x_963_);
    return v___x_964_;
}
pub unsafe fn l_Std_StreamMap_isEmpty___redArg___boxed(
    mut v_sm_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: u8 = 0;
    let mut v_r_967_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Std_StreamMap_isEmpty___redArg(v_sm_965_);
    lean_dec_ref(v_sm_965_);
    v_r_967_ = lean_box((v_res_966_) as usize);
    return v_r_967_;
}
pub unsafe fn l_Std_StreamMap_isEmpty(
    mut v_00_u03b1_968_: *mut LeanObject,
    mut v_00_u03b2_969_: *mut LeanObject,
    mut v_sm_970_: *mut LeanObject,
) -> u8 {
    let mut v___x_971_: u8 = 0;
    v___x_971_ = l_Std_StreamMap_isEmpty___redArg(v_sm_970_);
    return v___x_971_;
}
pub unsafe fn l_Std_StreamMap_isEmpty___boxed(
    mut v_00_u03b1_972_: *mut LeanObject,
    mut v_00_u03b2_973_: *mut LeanObject,
    mut v_sm_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_975_: u8 = 0;
    let mut v_r_976_: *mut LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Std_StreamMap_isEmpty(v_00_u03b1_972_, v_00_u03b2_973_, v_sm_974_);
    lean_dec_ref(v_sm_974_);
    v_r_976_ = lean_box((v_res_975_) as usize);
    return v_r_976_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(
    mut v_sz_977_: usize,
    mut v_i_978_: usize,
    mut v_bs_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_980_: u8 = 0;
    let mut v_v_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: usize = 0;
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_980_ = lean_usize_dec_lt(v_i_978_, v_sz_977_);
                if v___x_980_ == 0 {
                    return v_bs_979_;
                } else {
                    v_v_981_ = lean_array_uget_borrowed(v_bs_979_, v_i_978_);
                    v_fst_982_ = lean_ctor_get(v_v_981_, 0);
                    lean_inc(v_fst_982_);
                    v___x_983_ = lean_unsigned_to_nat(0);
                    v_bs_x27_984_ = lean_array_uset(v_bs_979_, v_i_978_, v___x_983_);
                    v___x_985_ = 1usize;
                    v___x_986_ = lean_usize_add(v_i_978_, v___x_985_);
                    v___x_987_ = lean_array_uset(v_bs_x27_984_, v_i_978_, v_fst_982_);
                    v_i_978_ = v___x_986_;
                    v_bs_979_ = v___x_987_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg___boxed(
    mut v_sz_989_: *mut LeanObject,
    mut v_i_990_: *mut LeanObject,
    mut v_bs_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_992_: usize = 0;
    let mut v_i_boxed_993_: usize = 0;
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_992_ = lean_unbox_usize(v_sz_989_);
    lean_dec(v_sz_989_);
    v_i_boxed_993_ = lean_unbox_usize(v_i_990_);
    lean_dec(v_i_990_);
    v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_boxed_992_, v_i_boxed_993_, v_bs_991_);
    return v_res_994_;
}
pub unsafe fn l_Std_StreamMap_keys___redArg(mut v_sm_995_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sz_996_: usize = 0;
    let mut v___x_997_: usize = 0;
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v_sz_996_ = lean_array_size(v_sm_995_);
    v___x_997_ = 0usize;
    v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_996_, v___x_997_, v_sm_995_);
    return v___x_998_;
}
pub unsafe fn l_Std_StreamMap_keys(
    mut v_00_u03b1_999_: *mut LeanObject,
    mut v_00_u03b2_1000_: *mut LeanObject,
    mut v_sm_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    v___x_1002_ = l_Std_StreamMap_keys___redArg(v_sm_1001_);
    return v___x_1002_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(
    mut v_00_u03b1_1003_: *mut LeanObject,
    mut v_00_u03b2_1004_: *mut LeanObject,
    mut v_sz_1005_: usize,
    mut v_i_1006_: usize,
    mut v_bs_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___redArg(v_sz_1005_, v_i_1006_, v_bs_1007_);
    return v___x_1008_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0___boxed(
    mut v_00_u03b1_1009_: *mut LeanObject,
    mut v_00_u03b2_1010_: *mut LeanObject,
    mut v_sz_1011_: *mut LeanObject,
    mut v_i_1012_: *mut LeanObject,
    mut v_bs_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1014_: usize = 0;
    let mut v_i_boxed_1015_: usize = 0;
    let mut v_res_1016_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1011_);
    lean_dec(v_sz_1011_);
    v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
    lean_dec(v_i_1012_);
    v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_keys_spec__0(v_00_u03b1_1009_, v_00_u03b2_1010_, v_sz_boxed_1014_, v_i_boxed_1015_, v_bs_1013_);
    return v_res_1016_;
}
pub unsafe fn l_Std_StreamMap_get_x3f___redArg___lam__0(
    mut v_inst_1017_: *mut LeanObject,
    mut v_name_1018_: *mut LeanObject,
    mut v___x_1019_: *mut LeanObject,
    mut v___x_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_x_1022_: *mut LeanObject,
    mut v___y_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    v_fst_1024_ = lean_ctor_get(v_a_1021_, 0);
    lean_inc(v_fst_1024_);
    v___x_1025_ = lean_apply_2(v_inst_1017_, v_fst_1024_, v_name_1018_);
    v___x_1026_ = (lean_unbox(v___x_1025_) as u8);
    if v___x_1026_ == 0 {
        let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_1021_);
        v___x_1027_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1027_, 0, v___x_1019_);
        return v___x_1027_;
    } else {
        let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_1019_);
        v___x_1028_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1028_, 0, v_a_1021_);
        v___x_1029_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1029_, 0, v___x_1028_);
        v___x_1030_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1030_, 0, v___x_1029_);
        lean_ctor_set(v___x_1030_, 1, v___x_1020_);
        v___x_1031_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1031_, 0, v___x_1030_);
        return v___x_1031_;
    }
}
pub unsafe fn l_Std_StreamMap_get_x3f___redArg___lam__0___boxed(
    mut v_inst_1032_: *mut LeanObject,
    mut v_name_1033_: *mut LeanObject,
    mut v___x_1034_: *mut LeanObject,
    mut v___x_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_x_1037_: *mut LeanObject,
    mut v___y_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1039_: *mut LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Std_StreamMap_get_x3f___redArg___lam__0(
        v_inst_1032_,
        v_name_1033_,
        v___x_1034_,
        v___x_1035_,
        v_a_1036_,
        v_x_1037_,
        v___y_1038_,
    );
    lean_dec_ref(v___y_1038_);
    return v_res_1039_;
}
pub unsafe fn l_Std_StreamMap_get_x3f___redArg(
    mut v_inst_1043_: *mut LeanObject,
    mut v_sm_1044_: *mut LeanObject,
    mut v_name_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1051_: usize = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v_snd_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1046_ = l_Std_StreamMap_register___redArg___closed__9;
                v___x_1047_ = lean_box(0);
                v___x_1048_ = lean_box(0);
                v___x_1049_ = l_Std_StreamMap_get_x3f___redArg___closed__0;
                v___f_1050_ = lean_alloc_closure(
                    l_Std_StreamMap_get_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    4,
                );
                lean_closure_set(v___f_1050_, 0, v_inst_1043_);
                lean_closure_set(v___f_1050_, 1, v_name_1045_);
                lean_closure_set(v___f_1050_, 2, v___x_1049_);
                lean_closure_set(v___f_1050_, 3, v___x_1048_);
                v_sz_1051_ = lean_array_size(v_sm_1044_);
                v___x_1052_ = 0usize;
                v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1046_,
                    v_sm_1044_,
                    v___f_1050_,
                    v_sz_1051_,
                    v___x_1052_,
                    v___x_1049_,
                );
                v_fst_1054_ = lean_ctor_get(v___x_1053_, 0);
                lean_inc(v_fst_1054_);
                lean_dec(v___x_1053_);
                if lean_obj_tag(v_fst_1054_) == 0 {
                    return v___x_1047_;
                } else {
                    v_val_1055_ = lean_ctor_get(v_fst_1054_, 0);
                    lean_inc(v_val_1055_);
                    lean_dec_ref_known(v_fst_1054_, 1);
                    if lean_obj_tag(v_val_1055_) == 0 {
                        return v___x_1047_;
                    } else {
                        v_val_1056_ = lean_ctor_get(v_val_1055_, 0);
                        v_isSharedCheck_1065_ = (!lean_is_exclusive(v_val_1055_)) as u8;
                        if v_isSharedCheck_1065_ == 0 {
                            v___x_1058_ = v_val_1055_;
                            v_isShared_1059_ = v_isSharedCheck_1065_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1056_);
                            lean_dec(v_val_1055_);
                            v___x_1058_ = lean_box(0);
                            v_isShared_1059_ = v_isSharedCheck_1065_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_1060_ = lean_ctor_get(v_val_1056_, 1);
                lean_inc(v_snd_1060_);
                lean_dec(v_val_1056_);
                v_fst_1061_ = lean_ctor_get(v_snd_1060_, 0);
                lean_inc(v_fst_1061_);
                lean_dec(v_snd_1060_);
                if v_isShared_1059_ == 0 {
                    lean_ctor_set(v___x_1058_, 0, v_fst_1061_);
                    v___x_1063_ = v___x_1058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_fst_1061_);
                    v___x_1063_ = v_reuseFailAlloc_1064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_StreamMap_get_x3f(
    mut v_00_u03b1_1066_: *mut LeanObject,
    mut v_00_u03b2_1067_: *mut LeanObject,
    mut v_inst_1068_: *mut LeanObject,
    mut v_sm_1069_: *mut LeanObject,
    mut v_name_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = l_Std_StreamMap_get_x3f___redArg(v_inst_1068_, v_sm_1069_, v_name_1070_);
    return v___x_1071_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(
    mut v_pred_1072_: *mut LeanObject,
    mut v_as_1073_: *mut LeanObject,
    mut v_i_1074_: usize,
    mut v_stop_1075_: usize,
    mut v_b_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: usize = 0;
    let mut v___x_1080_: usize = 0;
    let mut v___x_1082_: u8 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1082_ = lean_usize_dec_eq(v_i_1074_, v_stop_1075_);
                if v___x_1082_ == 0 {
                    v___x_1083_ = lean_array_uget_borrowed(v_as_1073_, v_i_1074_);
                    v_fst_1084_ = lean_ctor_get(v___x_1083_, 0);
                    lean_inc_ref(v_pred_1072_);
                    lean_inc(v_fst_1084_);
                    v___x_1085_ = lean_apply_1(v_pred_1072_, v_fst_1084_);
                    v___x_1086_ = (lean_unbox(v___x_1085_) as u8);
                    if v___x_1086_ == 0 {
                        v___y_1078_ = v_b_1076_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_1083_);
                        v___x_1087_ = lean_array_push(v_b_1076_, v___x_1083_);
                        v___y_1078_ = v___x_1087_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pred_1072_);
                    return v_b_1076_;
                }
            }
            1 => {
                v___x_1079_ = 1usize;
                v___x_1080_ = lean_usize_add(v_i_1074_, v___x_1079_);
                v_i_1074_ = v___x_1080_;
                v_b_1076_ = v___y_1078_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg___boxed(
    mut v_pred_1088_: *mut LeanObject,
    mut v_as_1089_: *mut LeanObject,
    mut v_i_1090_: *mut LeanObject,
    mut v_stop_1091_: *mut LeanObject,
    mut v_b_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1093_: usize = 0;
    let mut v_stop_boxed_1094_: usize = 0;
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1093_ = lean_unbox_usize(v_i_1090_);
    lean_dec(v_i_1090_);
    v_stop_boxed_1094_ = lean_unbox_usize(v_stop_1091_);
    lean_dec(v_stop_1091_);
    v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_1088_, v_as_1089_, v_i_boxed_1093_, v_stop_boxed_1094_, v_b_1092_);
    lean_dec_ref(v_as_1089_);
    return v_res_1095_;
}
pub unsafe fn l_Std_StreamMap_filterByName___redArg(
    mut v_sm_1096_: *mut LeanObject,
    mut v_pred_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    v___x_1098_ = lean_unsigned_to_nat(0);
    v___x_1099_ = lean_array_get_size(v_sm_1096_);
    v___x_1100_ = l_Std_StreamMap_empty___closed__0;
    v___x_1101_ = lean_nat_dec_lt(v___x_1098_, v___x_1099_);
    if v___x_1101_ == 0 {
        lean_dec_ref(v_pred_1097_);
        return v___x_1100_;
    } else {
        let mut v___x_1102_: u8 = 0;
        v___x_1102_ = lean_nat_dec_le(v___x_1099_, v___x_1099_);
        if v___x_1102_ == 0 {
            if v___x_1101_ == 0 {
                lean_dec_ref(v_pred_1097_);
                return v___x_1100_;
            } else {
                let mut v___x_1103_: usize = 0;
                let mut v___x_1104_: usize = 0;
                let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
                v___x_1103_ = 0usize;
                v___x_1104_ = lean_usize_of_nat(v___x_1099_);
                v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_1097_, v_sm_1096_, v___x_1103_, v___x_1104_, v___x_1100_);
                return v___x_1105_;
            }
        } else {
            let mut v___x_1106_: usize = 0;
            let mut v___x_1107_: usize = 0;
            let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
            v___x_1106_ = 0usize;
            v___x_1107_ = lean_usize_of_nat(v___x_1099_);
            v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_1097_, v_sm_1096_, v___x_1106_, v___x_1107_, v___x_1100_);
            return v___x_1108_;
        }
    }
}
pub unsafe fn l_Std_StreamMap_filterByName___redArg___boxed(
    mut v_sm_1109_: *mut LeanObject,
    mut v_pred_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1111_: *mut LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_Std_StreamMap_filterByName___redArg(v_sm_1109_, v_pred_1110_);
    lean_dec_ref(v_sm_1109_);
    return v_res_1111_;
}
pub unsafe fn l_Std_StreamMap_filterByName(
    mut v_00_u03b1_1112_: *mut LeanObject,
    mut v_00_u03b2_1113_: *mut LeanObject,
    mut v_sm_1114_: *mut LeanObject,
    mut v_pred_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    v___x_1116_ = l_Std_StreamMap_filterByName___redArg(v_sm_1114_, v_pred_1115_);
    return v___x_1116_;
}
pub unsafe fn l_Std_StreamMap_filterByName___boxed(
    mut v_00_u03b1_1117_: *mut LeanObject,
    mut v_00_u03b2_1118_: *mut LeanObject,
    mut v_sm_1119_: *mut LeanObject,
    mut v_pred_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1121_: *mut LeanObject = core::ptr::null_mut();
    v_res_1121_ =
        l_Std_StreamMap_filterByName(v_00_u03b1_1117_, v_00_u03b2_1118_, v_sm_1119_, v_pred_1120_);
    lean_dec_ref(v_sm_1119_);
    return v_res_1121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(
    mut v_00_u03b1_1122_: *mut LeanObject,
    mut v_00_u03b2_1123_: *mut LeanObject,
    mut v_pred_1124_: *mut LeanObject,
    mut v_as_1125_: *mut LeanObject,
    mut v_i_1126_: usize,
    mut v_stop_1127_: usize,
    mut v_b_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___redArg(v_pred_1124_, v_as_1125_, v_i_1126_, v_stop_1127_, v_b_1128_);
    return v___x_1129_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0___boxed(
    mut v_00_u03b1_1130_: *mut LeanObject,
    mut v_00_u03b2_1131_: *mut LeanObject,
    mut v_pred_1132_: *mut LeanObject,
    mut v_as_1133_: *mut LeanObject,
    mut v_i_1134_: *mut LeanObject,
    mut v_stop_1135_: *mut LeanObject,
    mut v_b_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1137_: usize = 0;
    let mut v_stop_boxed_1138_: usize = 0;
    let mut v_res_1139_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1137_ = lean_unbox_usize(v_i_1134_);
    lean_dec(v_i_1134_);
    v_stop_boxed_1138_ = lean_unbox_usize(v_stop_1135_);
    lean_dec(v_stop_1135_);
    v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_filterByName_spec__0(v_00_u03b1_1130_, v_00_u03b2_1131_, v_pred_1132_, v_as_1133_, v_i_boxed_1137_, v_stop_boxed_1138_, v_b_1136_);
    lean_dec_ref(v_as_1133_);
    return v_res_1139_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(
    mut v_sz_1140_: usize,
    mut v_i_1141_: usize,
    mut v_bs_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: u8 = 0;
    let mut v_v_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: usize = 0;
    let mut v___x_1156_: usize = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_unused_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1143_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
                if v___x_1143_ == 0 {
                    return v_bs_1142_;
                } else {
                    v_v_1144_ = lean_array_uget_borrowed(v_bs_1142_, v_i_1141_);
                    v_snd_1145_ = lean_ctor_get(v_v_1144_, 1);
                    lean_inc(v_snd_1145_);
                    v_fst_1146_ = lean_ctor_get(v_v_1144_, 0);
                    lean_inc(v_fst_1146_);
                    v_fst_1147_ = lean_ctor_get(v_snd_1145_, 0);
                    v_isSharedCheck_1160_ = (!lean_is_exclusive(v_snd_1145_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v_unused_1161_ = lean_ctor_get(v_snd_1145_, 1);
                        lean_dec(v_unused_1161_);
                        v___x_1149_ = v_snd_1145_;
                        v_isShared_1150_ = v_isSharedCheck_1160_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_1147_);
                        lean_dec(v_snd_1145_);
                        v___x_1149_ = lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1160_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1151_ = lean_unsigned_to_nat(0);
                v_bs_x27_1152_ = lean_array_uset(v_bs_1142_, v_i_1141_, v___x_1151_);
                if v_isShared_1150_ == 0 {
                    lean_ctor_set(v___x_1149_, 1, v_fst_1147_);
                    lean_ctor_set(v___x_1149_, 0, v_fst_1146_);
                    v___x_1154_ = v___x_1149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_fst_1146_);
                    lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_fst_1147_);
                    v___x_1154_ = v_reuseFailAlloc_1159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = 1usize;
                v___x_1156_ = lean_usize_add(v_i_1141_, v___x_1155_);
                v___x_1157_ = lean_array_uset(v_bs_x27_1152_, v_i_1141_, v___x_1154_);
                v_i_1141_ = v___x_1156_;
                v_bs_1142_ = v___x_1157_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg___boxed(
    mut v_sz_1162_: *mut LeanObject,
    mut v_i_1163_: *mut LeanObject,
    mut v_bs_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1165_: usize = 0;
    let mut v_i_boxed_1166_: usize = 0;
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1165_ = lean_unbox_usize(v_sz_1162_);
    lean_dec(v_sz_1162_);
    v_i_boxed_1166_ = lean_unbox_usize(v_i_1163_);
    lean_dec(v_i_1163_);
    v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_boxed_1165_, v_i_boxed_1166_, v_bs_1164_);
    return v_res_1167_;
}
pub unsafe fn l_Std_StreamMap_toArray___redArg(mut v_sm_1168_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sz_1169_: usize = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1169_ = lean_array_size(v_sm_1168_);
    v___x_1170_ = 0usize;
    v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_1169_, v___x_1170_, v_sm_1168_);
    return v___x_1171_;
}
pub unsafe fn l_Std_StreamMap_toArray(
    mut v_00_u03b1_1172_: *mut LeanObject,
    mut v_00_u03b2_1173_: *mut LeanObject,
    mut v_sm_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Std_StreamMap_toArray___redArg(v_sm_1174_);
    return v___x_1175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(
    mut v_00_u03b1_1176_: *mut LeanObject,
    mut v_00_u03b2_1177_: *mut LeanObject,
    mut v_sz_1178_: usize,
    mut v_i_1179_: usize,
    mut v_bs_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___redArg(v_sz_1178_, v_i_1179_, v_bs_1180_);
    return v___x_1181_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0___boxed(
    mut v_00_u03b1_1182_: *mut LeanObject,
    mut v_00_u03b2_1183_: *mut LeanObject,
    mut v_sz_1184_: *mut LeanObject,
    mut v_i_1185_: *mut LeanObject,
    mut v_bs_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1187_: usize = 0;
    let mut v_i_boxed_1188_: usize = 0;
    let mut v_res_1189_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1187_ = lean_unbox_usize(v_sz_1184_);
    lean_dec(v_sz_1184_);
    v_i_boxed_1188_ = lean_unbox_usize(v_i_1185_);
    lean_dec(v_i_1185_);
    v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_StreamMap_toArray_spec__0(v_00_u03b1_1182_, v_00_u03b2_1183_, v_sz_boxed_1187_, v_i_boxed_1188_, v_bs_1186_);
    return v_res_1189_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(
    mut v_as_1190_: *mut LeanObject,
    mut v_i_1191_: usize,
    mut v_stop_1192_: usize,
    mut v_b_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: usize = 0;
    let mut v___x_1202_: usize = 0;
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1195_ = lean_usize_dec_eq(v_i_1191_, v_stop_1192_);
                if v___x_1195_ == 0 {
                    v___x_1196_ = lean_array_uget_borrowed(v_as_1190_, v_i_1191_);
                    v_snd_1197_ = lean_ctor_get(v___x_1196_, 1);
                    v_snd_1198_ = lean_ctor_get(v_snd_1197_, 1);
                    lean_inc(v_snd_1198_);
                    v___x_1199_ = lean_apply_1(v_snd_1198_, lean_box(0));
                    if lean_obj_tag(v___x_1199_) == 0 {
                        v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
                        lean_inc(v_a_1200_);
                        lean_dec_ref_known(v___x_1199_, 1);
                        v___x_1201_ = 1usize;
                        v___x_1202_ = lean_usize_add(v_i_1191_, v___x_1201_);
                        v_i_1191_ = v___x_1202_;
                        v_b_1193_ = v_a_1200_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1199_;
                    }
                } else {
                    v___x_1204_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1204_, 0, v_b_1193_);
                    return v___x_1204_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg___boxed(
    mut v_as_1205_: *mut LeanObject,
    mut v_i_1206_: *mut LeanObject,
    mut v_stop_1207_: *mut LeanObject,
    mut v_b_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1210_: usize = 0;
    let mut v_stop_boxed_1211_: usize = 0;
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1210_ = lean_unbox_usize(v_i_1206_);
    lean_dec(v_i_1206_);
    v_stop_boxed_1211_ = lean_unbox_usize(v_stop_1207_);
    lean_dec(v_stop_1207_);
    v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_1205_, v_i_boxed_1210_, v_stop_boxed_1211_, v_b_1208_);
    lean_dec_ref(v_as_1205_);
    return v_res_1212_;
}
pub unsafe fn l_Std_StreamMap_close___redArg(mut v_sm_1213_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    v___x_1215_ = lean_unsigned_to_nat(0);
    v___x_1216_ = lean_array_get_size(v_sm_1213_);
    v___x_1217_ = lean_box(0);
    v___x_1218_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
    if v___x_1218_ == 0 {
        let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
        v___x_1219_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1219_, 0, v___x_1217_);
        return v___x_1219_;
    } else {
        let mut v___x_1220_: u8 = 0;
        v___x_1220_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
        if v___x_1220_ == 0 {
            if v___x_1218_ == 0 {
                let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
                v___x_1221_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1221_, 0, v___x_1217_);
                return v___x_1221_;
            } else {
                let mut v___x_1222_: usize = 0;
                let mut v___x_1223_: usize = 0;
                let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
                v___x_1222_ = 0usize;
                v___x_1223_ = lean_usize_of_nat(v___x_1216_);
                v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_1213_, v___x_1222_, v___x_1223_, v___x_1217_);
                return v___x_1224_;
            }
        } else {
            let mut v___x_1225_: usize = 0;
            let mut v___x_1226_: usize = 0;
            let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
            v___x_1225_ = 0usize;
            v___x_1226_ = lean_usize_of_nat(v___x_1216_);
            v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_sm_1213_, v___x_1225_, v___x_1226_, v___x_1217_);
            return v___x_1227_;
        }
    }
}
pub unsafe fn l_Std_StreamMap_close___redArg___boxed(
    mut v_sm_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1230_: *mut LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Std_StreamMap_close___redArg(v_sm_1228_);
    lean_dec_ref(v_sm_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Std_StreamMap_close(
    mut v_00_u03b1_1231_: *mut LeanObject,
    mut v_00_u03b2_1232_: *mut LeanObject,
    mut v_sm_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1235_ = l_Std_StreamMap_close___redArg(v_sm_1233_);
    return v___x_1235_;
}
pub unsafe fn l_Std_StreamMap_close___boxed(
    mut v_00_u03b1_1236_: *mut LeanObject,
    mut v_00_u03b2_1237_: *mut LeanObject,
    mut v_sm_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1240_: *mut LeanObject = core::ptr::null_mut();
    v_res_1240_ = l_Std_StreamMap_close(v_00_u03b1_1236_, v_00_u03b2_1237_, v_sm_1238_);
    lean_dec_ref(v_sm_1238_);
    return v_res_1240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(
    mut v_00_u03b1_1241_: *mut LeanObject,
    mut v_00_u03b2_1242_: *mut LeanObject,
    mut v_as_1243_: *mut LeanObject,
    mut v_i_1244_: usize,
    mut v_stop_1245_: usize,
    mut v_b_1246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___redArg(v_as_1243_, v_i_1244_, v_stop_1245_, v_b_1246_);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0___boxed(
    mut v_00_u03b1_1249_: *mut LeanObject,
    mut v_00_u03b2_1250_: *mut LeanObject,
    mut v_as_1251_: *mut LeanObject,
    mut v_i_1252_: *mut LeanObject,
    mut v_stop_1253_: *mut LeanObject,
    mut v_b_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1256_: usize = 0;
    let mut v_stop_boxed_1257_: usize = 0;
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1256_ = lean_unbox_usize(v_i_1252_);
    lean_dec(v_i_1252_);
    v_stop_boxed_1257_ = lean_unbox_usize(v_stop_1253_);
    lean_dec(v_stop_1253_);
    v_res_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_StreamMap_close_spec__0(v_00_u03b1_1249_, v_00_u03b2_1250_, v_as_1251_, v_i_boxed_1256_, v_stop_boxed_1257_, v_b_1254_);
    lean_dec_ref(v_as_1251_);
    return v_res_1258_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_StreamMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Queue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_StreamMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_StreamMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Queue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_StreamMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_StreamMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_StreamMap(builtin);
}
