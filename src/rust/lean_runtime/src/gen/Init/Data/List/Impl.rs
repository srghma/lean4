// Lean compiler output
// Module: Init.Data.List.Impl
// Imports: Init.Ext Init.Data.Array.Bootstrap Init.Data.Bool Init.Data.List.Lemmas Init.Data.Option.Lemmas
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold, l_Array_append___redArg,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_pop, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_usize_dec_eq,
};
pub static l_List_setTR___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_List_setTR___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_setTR___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_reduceOption___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_List_reduceOption___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceOption___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_flattenTR___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_List_flattenTR___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_flattenTR___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value:
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
    m_fun: l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(
    mut v_as_1135_: *mut crate::leanh::LeanObject,
    mut v_i_1136_: usize,
    mut v_stop_1137_: usize,
    mut v_b_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
                if v___x_1139_ == 0 {
                    v___x_1140_ = 1usize;
                    v___x_1141_ = lean_usize_sub(v_i_1136_, v___x_1140_);
                    v___x_1142_ = lean_array_uget_borrowed(v_as_1135_, v___x_1141_);
                    crate::leanh::lean_inc(v___x_1142_);
                    v___x_1143_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    crate::leanh::lean_ctor_set(v___x_1143_, 1, v_b_1138_);
                    v_i_1136_ = v___x_1141_;
                    v_b_1138_ = v___x_1143_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1138_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg___boxed(
    mut v_as_1145_: *mut crate::leanh::LeanObject,
    mut v_i_1146_: *mut crate::leanh::LeanObject,
    mut v_stop_1147_: *mut crate::leanh::LeanObject,
    mut v_b_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1149_: usize = 0;
    let mut v_stop_boxed_1150_: usize = 0;
    let mut v_res_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1149_ = crate::leanh::lean_unbox_usize(v_i_1146_);
    crate::leanh::lean_dec(v_i_1146_);
    v_stop_boxed_1150_ = crate::leanh::lean_unbox_usize(v_stop_1147_);
    crate::leanh::lean_dec(v_stop_1147_);
    v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1145_, v_i_boxed_1149_, v_stop_boxed_1150_, v_b_1148_);
    crate::leanh::lean_dec_ref(v_as_1145_);
    return v_res_1151_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
    mut v_l_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_zero_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1163_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1154_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1156_);
                    crate::leanh::lean_dec(v_a_1155_);
                    crate::leanh::lean_dec(v_a_1153_);
                    crate::leanh::lean_inc(v_l_1152_);
                    return v_l_1152_;
                } else {
                    v_head_1157_ = crate::leanh::lean_ctor_get(v_a_1154_, 0);
                    v_tail_1158_ = crate::leanh::lean_ctor_get(v_a_1154_, 1);
                    v_isSharedCheck_1176_ = (!crate::leanh::lean_is_exclusive(v_a_1154_)) as u8;
                    if v_isSharedCheck_1176_ == 0 {
                        v___x_1160_ = v_a_1154_;
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1158_);
                        crate::leanh::lean_inc(v_head_1157_);
                        crate::leanh::lean_dec(v_a_1154_);
                        v___x_1160_ = crate::leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1162_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1163_ = lean_nat_dec_eq(v_a_1155_, v_zero_1162_);
                if v_isZero_1163_ == 1 {
                    crate::leanh::lean_dec(v_head_1157_);
                    crate::leanh::lean_dec(v_a_1155_);
                    if v_isShared_1161_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1160_, 0, v_a_1153_);
                        v___x_1165_ = v___x_1160_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1153_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_tail_1158_);
                        v___x_1165_ = v_reuseFailAlloc_1171_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1160_);
                    v_one_1172_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1173_ = lean_nat_sub(v_a_1155_, v_one_1172_);
                    crate::leanh::lean_dec(v_a_1155_);
                    v___x_1174_ = lean_array_push(v_a_1156_, v_head_1157_);
                    v_a_1154_ = v_tail_1158_;
                    v_a_1155_ = v_n_1173_;
                    v_a_1156_ = v___x_1174_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1166_ = lean_array_get_size(v_a_1156_);
                v___x_1167_ = lean_nat_dec_lt(v_zero_1162_, v___x_1166_);
                if v___x_1167_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_1156_);
                    return v___x_1165_;
                } else {
                    v___x_1168_ = lean_usize_of_nat(v___x_1166_);
                    v___x_1169_ = 0usize;
                    v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1156_, v___x_1168_, v___x_1169_, v___x_1165_);
                    crate::leanh::lean_dec_ref(v_a_1156_);
                    return v___x_1170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(
    mut v_l_1177_: *mut crate::leanh::LeanObject,
    mut v_a_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v_a_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_,
    );
    crate::leanh::lean_dec(v_l_1177_);
    return v_res_1182_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go(
    mut v_00_u03b1_1183_: *mut crate::leanh::LeanObject,
    mut v_l_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_,
    );
    return v___x_1189_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(
    mut v_00_u03b1_1190_: *mut crate::leanh::LeanObject,
    mut v_l_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Init_Data_List_Impl_0__List_setTR_go(
        v_00_u03b1_1190_,
        v_l_1191_,
        v_a_1192_,
        v_a_1193_,
        v_a_1194_,
        v_a_1195_,
    );
    crate::leanh::lean_dec(v_l_1191_);
    return v_res_1196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(
    mut v_00_u03b1_1197_: *mut crate::leanh::LeanObject,
    mut v_as_1198_: *mut crate::leanh::LeanObject,
    mut v_i_1199_: usize,
    mut v_stop_1200_: usize,
    mut v_b_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1198_, v_i_1199_, v_stop_1200_, v_b_1201_);
    return v___x_1202_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(
    mut v_00_u03b1_1203_: *mut crate::leanh::LeanObject,
    mut v_as_1204_: *mut crate::leanh::LeanObject,
    mut v_i_1205_: *mut crate::leanh::LeanObject,
    mut v_stop_1206_: *mut crate::leanh::LeanObject,
    mut v_b_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1208_: usize = 0;
    let mut v_stop_boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1208_ = crate::leanh::lean_unbox_usize(v_i_1205_);
    crate::leanh::lean_dec(v_i_1205_);
    v_stop_boxed_1209_ = crate::leanh::lean_unbox_usize(v_stop_1206_);
    crate::leanh::lean_dec(v_stop_1206_);
    v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(v_00_u03b1_1203_, v_as_1204_, v_i_boxed_1208_, v_stop_boxed_1209_, v_b_1207_);
    crate::leanh::lean_dec_ref(v_as_1204_);
    return v_res_1210_;
}
pub unsafe fn l_List_setTR___redArg(
    mut v_l_1213_: *mut crate::leanh::LeanObject,
    mut v_n_1214_: *mut crate::leanh::LeanObject,
    mut v_a_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1213_);
    v___x_1217_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1213_,
        v_a_1215_,
        v_l_1213_,
        v_n_1214_,
        v___x_1216_,
    );
    crate::leanh::lean_dec(v_l_1213_);
    return v___x_1217_;
}
pub unsafe fn l_List_setTR(
    mut v_00_u03b1_1218_: *mut crate::leanh::LeanObject,
    mut v_l_1219_: *mut crate::leanh::LeanObject,
    mut v_n_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1219_);
    v___x_1223_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1219_,
        v_a_1221_,
        v_l_1219_,
        v_n_1220_,
        v___x_1222_,
    );
    crate::leanh::lean_dec(v_l_1219_);
    return v___x_1223_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(
    mut v_x_1224_: *mut crate::leanh::LeanObject,
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_h__1_1227_: *mut crate::leanh::LeanObject,
    mut v_h__2_1228_: *mut crate::leanh::LeanObject,
    mut v_h__3_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1224_) == 0 {
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1229_);
        crate::leanh::lean_dec(v_h__2_1228_);
        v___x_1230_ = crate::leanh::lean_apply_2(v_h__1_1227_, v_x_1225_, v_x_1226_);
        return v___x_1230_;
    } else {
        let mut v_head_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1234_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1227_);
        v_head_1231_ = crate::leanh::lean_ctor_get(v_x_1224_, 0);
        crate::leanh::lean_inc(v_head_1231_);
        v_tail_1232_ = crate::leanh::lean_ctor_get(v_x_1224_, 1);
        crate::leanh::lean_inc(v_tail_1232_);
        crate::leanh::lean_dec_ref_known(v_x_1224_, 2);
        v_zero_1233_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_1234_ = lean_nat_dec_eq(v_x_1225_, v_zero_1233_);
        if v_isZero_1234_ == 1 {
            let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1229_);
            crate::leanh::lean_dec(v_x_1225_);
            v___x_1235_ =
                crate::leanh::lean_apply_3(v_h__2_1228_, v_head_1231_, v_tail_1232_, v_x_1226_);
            return v___x_1235_;
        } else {
            let mut v_one_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1228_);
            v_one_1236_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1237_ = lean_nat_sub(v_x_1225_, v_one_1236_);
            crate::leanh::lean_dec(v_x_1225_);
            v___x_1238_ = crate::leanh::lean_apply_4(
                v_h__3_1229_,
                v_head_1231_,
                v_tail_1232_,
                v_n_1237_,
                v_x_1226_,
            );
            return v___x_1238_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter(
    mut v_00_u03b1_1239_: *mut crate::leanh::LeanObject,
    mut v_motive_1240_: *mut crate::leanh::LeanObject,
    mut v_x_1241_: *mut crate::leanh::LeanObject,
    mut v_x_1242_: *mut crate::leanh::LeanObject,
    mut v_x_1243_: *mut crate::leanh::LeanObject,
    mut v_h__1_1244_: *mut crate::leanh::LeanObject,
    mut v_h__2_1245_: *mut crate::leanh::LeanObject,
    mut v_h__3_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1241_) == 0 {
        let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1246_);
        crate::leanh::lean_dec(v_h__2_1245_);
        v___x_1247_ = crate::leanh::lean_apply_2(v_h__1_1244_, v_x_1242_, v_x_1243_);
        return v___x_1247_;
    } else {
        let mut v_head_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1251_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1244_);
        v_head_1248_ = crate::leanh::lean_ctor_get(v_x_1241_, 0);
        crate::leanh::lean_inc(v_head_1248_);
        v_tail_1249_ = crate::leanh::lean_ctor_get(v_x_1241_, 1);
        crate::leanh::lean_inc(v_tail_1249_);
        crate::leanh::lean_dec_ref_known(v_x_1241_, 2);
        v_zero_1250_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_1251_ = lean_nat_dec_eq(v_x_1242_, v_zero_1250_);
        if v_isZero_1251_ == 1 {
            let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1246_);
            crate::leanh::lean_dec(v_x_1242_);
            v___x_1252_ =
                crate::leanh::lean_apply_3(v_h__2_1245_, v_head_1248_, v_tail_1249_, v_x_1243_);
            return v___x_1252_;
        } else {
            let mut v_one_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1245_);
            v_one_1253_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1254_ = lean_nat_sub(v_x_1242_, v_one_1253_);
            crate::leanh::lean_dec(v_x_1242_);
            v___x_1255_ = crate::leanh::lean_apply_4(
                v_h__3_1246_,
                v_head_1248_,
                v_tail_1249_,
                v_n_1254_,
                v_x_1243_,
            );
            return v___x_1255_;
        }
    }
}
pub unsafe fn l_List_filterMapTR_go___redArg(
    mut v_f_1256_: *mut crate::leanh::LeanObject,
    mut v_a_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1257_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_1256_);
                    v___x_1259_ = lean_array_to_list(v_a_1258_);
                    return v___x_1259_;
                } else {
                    v_head_1260_ = crate::leanh::lean_ctor_get(v_a_1257_, 0);
                    crate::leanh::lean_inc(v_head_1260_);
                    v_tail_1261_ = crate::leanh::lean_ctor_get(v_a_1257_, 1);
                    crate::leanh::lean_inc(v_tail_1261_);
                    crate::leanh::lean_dec_ref_known(v_a_1257_, 2);
                    crate::leanh::lean_inc_ref(v_f_1256_);
                    v___x_1262_ = crate::leanh::lean_apply_1(v_f_1256_, v_head_1260_);
                    if crate::leanh::lean_obj_tag(v___x_1262_) == 0 {
                        v_a_1257_ = v_tail_1261_;
                        state = 0;
                        continue;
                    } else {
                        v_val_1264_ = crate::leanh::lean_ctor_get(v___x_1262_, 0);
                        crate::leanh::lean_inc(v_val_1264_);
                        crate::leanh::lean_dec_ref_known(v___x_1262_, 1);
                        v___x_1265_ = lean_array_push(v_a_1258_, v_val_1264_);
                        v_a_1257_ = v_tail_1261_;
                        v_a_1258_ = v___x_1265_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapTR_go(
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1268_: *mut crate::leanh::LeanObject,
    mut v_f_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_List_filterMapTR_go___redArg(v_f_1269_, v_a_1270_, v_a_1271_);
    return v___x_1272_;
}
pub unsafe fn l_List_filterMapTR___redArg(
    mut v_f_1273_: *mut crate::leanh::LeanObject,
    mut v_l_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_List_setTR___redArg___closed__0;
    v___x_1276_ = l_List_filterMapTR_go___redArg(v_f_1273_, v_l_1274_, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_List_filterMapTR(
    mut v_00_u03b1_1277_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1278_: *mut crate::leanh::LeanObject,
    mut v_f_1279_: *mut crate::leanh::LeanObject,
    mut v_l_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_List_setTR___redArg___closed__0;
    v___x_1282_ = l_List_filterMapTR_go___redArg(v_f_1279_, v_l_1280_, v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(
    mut v_x_1283_: *mut crate::leanh::LeanObject,
    mut v_x_1284_: *mut crate::leanh::LeanObject,
    mut v_h__1_1285_: *mut crate::leanh::LeanObject,
    mut v_h__2_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1283_) == 0 {
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1286_);
        v___x_1287_ = crate::leanh::lean_apply_1(v_h__1_1285_, v_x_1284_);
        return v___x_1287_;
    } else {
        let mut v_head_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1285_);
        v_head_1288_ = crate::leanh::lean_ctor_get(v_x_1283_, 0);
        crate::leanh::lean_inc(v_head_1288_);
        v_tail_1289_ = crate::leanh::lean_ctor_get(v_x_1283_, 1);
        crate::leanh::lean_inc(v_tail_1289_);
        crate::leanh::lean_dec_ref_known(v_x_1283_, 2);
        v___x_1290_ =
            crate::leanh::lean_apply_3(v_h__2_1286_, v_head_1288_, v_tail_1289_, v_x_1284_);
        return v___x_1290_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(
    mut v_00_u03b1_1291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1292_: *mut crate::leanh::LeanObject,
    mut v_motive_1293_: *mut crate::leanh::LeanObject,
    mut v_x_1294_: *mut crate::leanh::LeanObject,
    mut v_x_1295_: *mut crate::leanh::LeanObject,
    mut v_h__1_1296_: *mut crate::leanh::LeanObject,
    mut v_h__2_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1294_) == 0 {
        let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1297_);
        v___x_1298_ = crate::leanh::lean_apply_1(v_h__1_1296_, v_x_1295_);
        return v___x_1298_;
    } else {
        let mut v_head_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1296_);
        v_head_1299_ = crate::leanh::lean_ctor_get(v_x_1294_, 0);
        crate::leanh::lean_inc(v_head_1299_);
        v_tail_1300_ = crate::leanh::lean_ctor_get(v_x_1294_, 1);
        crate::leanh::lean_inc(v_tail_1300_);
        crate::leanh::lean_dec_ref_known(v_x_1294_, 2);
        v___x_1301_ =
            crate::leanh::lean_apply_3(v_h__2_1297_, v_head_1299_, v_tail_1300_, v_x_1295_);
        return v___x_1301_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(
    mut v_x_1302_: *mut crate::leanh::LeanObject,
    mut v_h__1_1303_: *mut crate::leanh::LeanObject,
    mut v_h__2_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1302_) == 0 {
        let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1304_);
        v___x_1305_ = crate::leanh::lean_box(0);
        v___x_1306_ = crate::leanh::lean_apply_1(v_h__1_1303_, v___x_1305_);
        return v___x_1306_;
    } else {
        let mut v_val_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1303_);
        v_val_1307_ = crate::leanh::lean_ctor_get(v_x_1302_, 0);
        crate::leanh::lean_inc(v_val_1307_);
        crate::leanh::lean_dec_ref_known(v_x_1302_, 1);
        v___x_1308_ = crate::leanh::lean_apply_1(v_h__2_1304_, v_val_1307_);
        return v___x_1308_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(
    mut v_00_u03b2_1309_: *mut crate::leanh::LeanObject,
    mut v_motive_1310_: *mut crate::leanh::LeanObject,
    mut v_x_1311_: *mut crate::leanh::LeanObject,
    mut v_h__1_1312_: *mut crate::leanh::LeanObject,
    mut v_h__2_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1311_) == 0 {
        let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1313_);
        v___x_1314_ = crate::leanh::lean_box(0);
        v___x_1315_ = crate::leanh::lean_apply_1(v_h__1_1312_, v___x_1314_);
        return v___x_1315_;
    } else {
        let mut v_val_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1312_);
        v_val_1316_ = crate::leanh::lean_ctor_get(v_x_1311_, 0);
        crate::leanh::lean_inc(v_val_1316_);
        crate::leanh::lean_dec_ref_known(v_x_1311_, 1);
        v___x_1317_ = crate::leanh::lean_apply_1(v_h__2_1313_, v_val_1316_);
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_1318_: *mut crate::leanh::LeanObject,
    mut v_h__1_1319_: *mut crate::leanh::LeanObject,
    mut v_h__2_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1318_) == 0 {
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1320_);
        v___x_1321_ = crate::leanh::lean_box(0);
        v___x_1322_ = crate::leanh::lean_apply_1(v_h__1_1319_, v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v_val_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1319_);
        v_val_1323_ = crate::leanh::lean_ctor_get(v_x_1318_, 0);
        crate::leanh::lean_inc(v_val_1323_);
        crate::leanh::lean_dec_ref_known(v_x_1318_, 1);
        v___x_1324_ = crate::leanh::lean_apply_1(v_h__2_1320_, v_val_1323_);
        return v___x_1324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_1325_: *mut crate::leanh::LeanObject,
    mut v_motive_1326_: *mut crate::leanh::LeanObject,
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_h__1_1328_: *mut crate::leanh::LeanObject,
    mut v_h__2_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1327_) == 0 {
        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1329_);
        v___x_1330_ = crate::leanh::lean_box(0);
        v___x_1331_ = crate::leanh::lean_apply_1(v_h__1_1328_, v___x_1330_);
        return v___x_1331_;
    } else {
        let mut v_val_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1328_);
        v_val_1332_ = crate::leanh::lean_ctor_get(v_x_1327_, 0);
        crate::leanh::lean_inc(v_val_1332_);
        crate::leanh::lean_dec_ref_known(v_x_1327_, 1);
        v___x_1333_ = crate::leanh::lean_apply_1(v_h__2_1329_, v_val_1332_);
        return v___x_1333_;
    }
}
pub unsafe fn l_List_reduceOption___redArg(
    mut v_a_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_List_reduceOption___redArg___closed__0;
    v___x_1337_ = l_List_setTR___redArg___closed__0;
    v___x_1338_ = l_List_filterMapTR_go___redArg(v___x_1336_, v_a_1335_, v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_List_reduceOption(
    mut v_00_u03b1_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = l_List_reduceOption___redArg___closed__0;
    v___x_1342_ = l_List_setTR___redArg___closed__0;
    v___x_1343_ = l_List_filterMapTR_go___redArg(v___x_1341_, v_a_1340_, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_List_foldrTR___redArg___lam__0(
    mut v_f_1344_: *mut crate::leanh::LeanObject,
    mut v_x1_1345_: *mut crate::leanh::LeanObject,
    mut v_x2_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = crate::leanh::lean_apply_2(v_f_1344_, v_x1_1345_, v_x2_1346_);
    return v___x_1347_;
}
pub unsafe fn l_List_foldrTR___redArg(
    mut v_f_1367_: *mut crate::leanh::LeanObject,
    mut v_init_1368_: *mut crate::leanh::LeanObject,
    mut v_l_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    v___x_1370_ = lean_array_mk(v_l_1369_);
    v___x_1371_ = lean_array_get_size(v___x_1370_);
    v___x_1372_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1373_ = l_List_foldrTR___redArg___closed__9;
    v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1371_);
    if v___x_1374_ == 0 {
        crate::leanh::lean_dec_ref(v___x_1370_);
        crate::leanh::lean_dec(v_f_1367_);
        return v_init_1368_;
    } else {
        let mut v___f_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: usize = 0;
        let mut v___x_1377_: usize = 0;
        let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1375_ = crate::leanh::lean_alloc_closure(
            l_List_foldrTR___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1375_, 0, v_f_1367_);
        v___x_1376_ = lean_usize_of_nat(v___x_1371_);
        v___x_1377_ = 0usize;
        v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1373_,
            v___f_1375_,
            v___x_1370_,
            v___x_1376_,
            v___x_1377_,
            v_init_1368_,
        );
        return v___x_1378_;
    }
}
pub unsafe fn l_List_foldrTR(
    mut v_00_u03b1_1379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1380_: *mut crate::leanh::LeanObject,
    mut v_f_1381_: *mut crate::leanh::LeanObject,
    mut v_init_1382_: *mut crate::leanh::LeanObject,
    mut v_l_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_List_foldrTR___redArg(v_f_1381_, v_init_1382_, v_l_1383_);
    return v___x_1384_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
    mut v_f_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1386_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_1385_);
                    v___x_1388_ = lean_array_to_list(v_a_1387_);
                    return v___x_1388_;
                } else {
                    v_head_1389_ = crate::leanh::lean_ctor_get(v_a_1386_, 0);
                    crate::leanh::lean_inc(v_head_1389_);
                    v_tail_1390_ = crate::leanh::lean_ctor_get(v_a_1386_, 1);
                    crate::leanh::lean_inc(v_tail_1390_);
                    crate::leanh::lean_dec_ref_known(v_a_1386_, 2);
                    crate::leanh::lean_inc_ref(v_f_1385_);
                    v___x_1391_ = crate::leanh::lean_apply_1(v_f_1385_, v_head_1389_);
                    v___x_1392_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_1387_,
                        v___x_1391_,
                    );
                    v_a_1386_ = v_tail_1390_;
                    v_a_1387_ = v___x_1392_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go(
    mut v_00_u03b1_1394_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1395_: *mut crate::leanh::LeanObject,
    mut v_f_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1396_, v_a_1397_, v_a_1398_,
    );
    return v___x_1399_;
}
pub unsafe fn l_List_flatMapTR___redArg(
    mut v_f_1400_: *mut crate::leanh::LeanObject,
    mut v_as_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_List_setTR___redArg___closed__0;
    v___x_1403_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1400_,
        v_as_1401_,
        v___x_1402_,
    );
    return v___x_1403_;
}
pub unsafe fn l_List_flatMapTR(
    mut v_00_u03b1_1404_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1405_: *mut crate::leanh::LeanObject,
    mut v_f_1406_: *mut crate::leanh::LeanObject,
    mut v_as_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l_List_setTR___redArg___closed__0;
    v___x_1409_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1406_,
        v_as_1407_,
        v___x_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_List_flattenTR___redArg(
    mut v_l_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_List_flattenTR___redArg___closed__0;
    v___x_1413_ = l_List_setTR___redArg___closed__0;
    v___x_1414_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v___x_1412_,
        v_l_1411_,
        v___x_1413_,
    );
    return v___x_1414_;
}
pub unsafe fn l_List_flattenTR(
    mut v_00_u03b1_1415_: *mut crate::leanh::LeanObject,
    mut v_l_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_List_flattenTR___redArg___closed__0;
    v___x_1418_ = l_List_setTR___redArg___closed__0;
    v___x_1419_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v___x_1417_,
        v_l_1416_,
        v___x_1418_,
    );
    return v___x_1419_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
    mut v_l_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1427_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1421_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1423_);
                    crate::leanh::lean_dec(v_a_1422_);
                    crate::leanh::lean_inc(v_l_1420_);
                    return v_l_1420_;
                } else {
                    v_head_1424_ = crate::leanh::lean_ctor_get(v_a_1421_, 0);
                    crate::leanh::lean_inc(v_head_1424_);
                    v_tail_1425_ = crate::leanh::lean_ctor_get(v_a_1421_, 1);
                    crate::leanh::lean_inc(v_tail_1425_);
                    crate::leanh::lean_dec_ref_known(v_a_1421_, 2);
                    v_zero_1426_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_1427_ = lean_nat_dec_eq(v_a_1422_, v_zero_1426_);
                    if v_isZero_1427_ == 1 {
                        crate::leanh::lean_dec(v_tail_1425_);
                        crate::leanh::lean_dec(v_head_1424_);
                        crate::leanh::lean_dec(v_a_1422_);
                        v___x_1428_ = lean_array_to_list(v_a_1423_);
                        return v___x_1428_;
                    } else {
                        v_one_1429_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1430_ = lean_nat_sub(v_a_1422_, v_one_1429_);
                        crate::leanh::lean_dec(v_a_1422_);
                        v___x_1431_ = lean_array_push(v_a_1423_, v_head_1424_);
                        v_a_1421_ = v_tail_1425_;
                        v_a_1422_ = v_n_1430_;
                        v_a_1423_ = v___x_1431_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(
    mut v_l_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
    mut v_a_1435_: *mut crate::leanh::LeanObject,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1433_, v_a_1434_, v_a_1435_, v_a_1436_,
    );
    crate::leanh::lean_dec(v_l_1433_);
    return v_res_1437_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go(
    mut v_00_u03b1_1438_: *mut crate::leanh::LeanObject,
    mut v_l_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
    mut v_a_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1439_, v_a_1440_, v_a_1441_, v_a_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(
    mut v_00_u03b1_1444_: *mut crate::leanh::LeanObject,
    mut v_l_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        v_00_u03b1_1444_,
        v_l_1445_,
        v_a_1446_,
        v_a_1447_,
        v_a_1448_,
    );
    crate::leanh::lean_dec(v_l_1445_);
    return v_res_1449_;
}
pub unsafe fn l_List_takeTR___redArg(
    mut v_n_1450_: *mut crate::leanh::LeanObject,
    mut v_l_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1451_);
    v___x_1453_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1451_,
        v_l_1451_,
        v_n_1450_,
        v___x_1452_,
    );
    crate::leanh::lean_dec(v_l_1451_);
    return v___x_1453_;
}
pub unsafe fn l_List_takeTR(
    mut v_00_u03b1_1454_: *mut crate::leanh::LeanObject,
    mut v_n_1455_: *mut crate::leanh::LeanObject,
    mut v_l_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1456_);
    v___x_1458_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1456_,
        v_l_1456_,
        v_n_1455_,
        v___x_1457_,
    );
    crate::leanh::lean_dec(v_l_1456_);
    return v___x_1458_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
    mut v_x_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_h__1_1461_: *mut crate::leanh::LeanObject,
    mut v_h__2_1462_: *mut crate::leanh::LeanObject,
    mut v_h__3_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1465_: u8 = 0;
    v_zero_1464_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1465_ = lean_nat_dec_eq(v_x_1459_, v_zero_1464_);
    if v_isZero_1465_ == 1 {
        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1463_);
        crate::leanh::lean_dec(v_h__2_1462_);
        v___x_1466_ = crate::leanh::lean_apply_1(v_h__1_1461_, v_x_1460_);
        return v___x_1466_;
    } else {
        let mut v_one_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1461_);
        v_one_1467_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1468_ = lean_nat_sub(v_x_1459_, v_one_1467_);
        if crate::leanh::lean_obj_tag(v_x_1460_) == 0 {
            let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1463_);
            v___x_1469_ = crate::leanh::lean_apply_1(v_h__2_1462_, v_n_1468_);
            return v___x_1469_;
        } else {
            let mut v_head_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1462_);
            v_head_1470_ = crate::leanh::lean_ctor_get(v_x_1460_, 0);
            crate::leanh::lean_inc(v_head_1470_);
            v_tail_1471_ = crate::leanh::lean_ctor_get(v_x_1460_, 1);
            crate::leanh::lean_inc(v_tail_1471_);
            crate::leanh::lean_dec_ref_known(v_x_1460_, 2);
            v___x_1472_ =
                crate::leanh::lean_apply_3(v_h__3_1463_, v_n_1468_, v_head_1470_, v_tail_1471_);
            return v___x_1472_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_1473_: *mut crate::leanh::LeanObject,
    mut v_x_1474_: *mut crate::leanh::LeanObject,
    mut v_h__1_1475_: *mut crate::leanh::LeanObject,
    mut v_h__2_1476_: *mut crate::leanh::LeanObject,
    mut v_h__3_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
        v_x_1473_,
        v_x_1474_,
        v_h__1_1475_,
        v_h__2_1476_,
        v_h__3_1477_,
    );
    crate::leanh::lean_dec(v_x_1473_);
    return v_res_1478_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
    mut v_00_u03b1_1479_: *mut crate::leanh::LeanObject,
    mut v_motive_1480_: *mut crate::leanh::LeanObject,
    mut v_x_1481_: *mut crate::leanh::LeanObject,
    mut v_x_1482_: *mut crate::leanh::LeanObject,
    mut v_h__1_1483_: *mut crate::leanh::LeanObject,
    mut v_h__2_1484_: *mut crate::leanh::LeanObject,
    mut v_h__3_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1487_: u8 = 0;
    v_zero_1486_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1487_ = lean_nat_dec_eq(v_x_1481_, v_zero_1486_);
    if v_isZero_1487_ == 1 {
        let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1485_);
        crate::leanh::lean_dec(v_h__2_1484_);
        v___x_1488_ = crate::leanh::lean_apply_1(v_h__1_1483_, v_x_1482_);
        return v___x_1488_;
    } else {
        let mut v_one_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1483_);
        v_one_1489_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1490_ = lean_nat_sub(v_x_1481_, v_one_1489_);
        if crate::leanh::lean_obj_tag(v_x_1482_) == 0 {
            let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1485_);
            v___x_1491_ = crate::leanh::lean_apply_1(v_h__2_1484_, v_n_1490_);
            return v___x_1491_;
        } else {
            let mut v_head_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1484_);
            v_head_1492_ = crate::leanh::lean_ctor_get(v_x_1482_, 0);
            crate::leanh::lean_inc(v_head_1492_);
            v_tail_1493_ = crate::leanh::lean_ctor_get(v_x_1482_, 1);
            crate::leanh::lean_inc(v_tail_1493_);
            crate::leanh::lean_dec_ref_known(v_x_1482_, 2);
            v___x_1494_ =
                crate::leanh::lean_apply_3(v_h__3_1485_, v_n_1490_, v_head_1492_, v_tail_1493_);
            return v___x_1494_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_1495_: *mut crate::leanh::LeanObject,
    mut v_motive_1496_: *mut crate::leanh::LeanObject,
    mut v_x_1497_: *mut crate::leanh::LeanObject,
    mut v_x_1498_: *mut crate::leanh::LeanObject,
    mut v_h__1_1499_: *mut crate::leanh::LeanObject,
    mut v_h__2_1500_: *mut crate::leanh::LeanObject,
    mut v_h__3_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
        v_00_u03b1_1495_,
        v_motive_1496_,
        v_x_1497_,
        v_x_1498_,
        v_h__1_1499_,
        v_h__2_1500_,
        v_h__3_1501_,
    );
    crate::leanh::lean_dec(v_x_1497_);
    return v_res_1502_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
    mut v_p_1503_: *mut crate::leanh::LeanObject,
    mut v_l_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1505_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1506_);
                    crate::leanh::lean_dec_ref(v_p_1503_);
                    crate::leanh::lean_inc(v_l_1504_);
                    return v_l_1504_;
                } else {
                    v_head_1507_ = crate::leanh::lean_ctor_get(v_a_1505_, 0);
                    crate::leanh::lean_inc_n(v_head_1507_, 2);
                    v_tail_1508_ = crate::leanh::lean_ctor_get(v_a_1505_, 1);
                    crate::leanh::lean_inc(v_tail_1508_);
                    crate::leanh::lean_dec_ref_known(v_a_1505_, 2);
                    crate::leanh::lean_inc_ref(v_p_1503_);
                    v___x_1509_ = crate::leanh::lean_apply_1(v_p_1503_, v_head_1507_);
                    v___x_1510_ = (crate::leanh::lean_unbox(v___x_1509_) as u8);
                    if v___x_1510_ == 0 {
                        crate::leanh::lean_dec(v_tail_1508_);
                        crate::leanh::lean_dec(v_head_1507_);
                        crate::leanh::lean_dec_ref(v_p_1503_);
                        v___x_1511_ = lean_array_to_list(v_a_1506_);
                        return v___x_1511_;
                    } else {
                        v___x_1512_ = lean_array_push(v_a_1506_, v_head_1507_);
                        v_a_1505_ = v_tail_1508_;
                        v_a_1506_ = v___x_1512_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(
    mut v_p_1514_: *mut crate::leanh::LeanObject,
    mut v_l_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
    mut v_a_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1514_, v_l_1515_, v_a_1516_, v_a_1517_,
    );
    crate::leanh::lean_dec(v_l_1515_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
    mut v_00_u03b1_1519_: *mut crate::leanh::LeanObject,
    mut v_p_1520_: *mut crate::leanh::LeanObject,
    mut v_l_1521_: *mut crate::leanh::LeanObject,
    mut v_a_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1520_, v_l_1521_, v_a_1522_, v_a_1523_,
    );
    return v___x_1524_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(
    mut v_00_u03b1_1525_: *mut crate::leanh::LeanObject,
    mut v_p_1526_: *mut crate::leanh::LeanObject,
    mut v_l_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
        v_00_u03b1_1525_,
        v_p_1526_,
        v_l_1527_,
        v_a_1528_,
        v_a_1529_,
    );
    crate::leanh::lean_dec(v_l_1527_);
    return v_res_1530_;
}
pub unsafe fn l_List_takeWhileTR___redArg(
    mut v_p_1531_: *mut crate::leanh::LeanObject,
    mut v_l_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1532_);
    v___x_1534_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1531_,
        v_l_1532_,
        v_l_1532_,
        v___x_1533_,
    );
    crate::leanh::lean_dec(v_l_1532_);
    return v___x_1534_;
}
pub unsafe fn l_List_takeWhileTR(
    mut v_00_u03b1_1535_: *mut crate::leanh::LeanObject,
    mut v_p_1536_: *mut crate::leanh::LeanObject,
    mut v_l_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1537_);
    v___x_1539_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1536_,
        v_l_1537_,
        v_l_1537_,
        v___x_1538_,
    );
    crate::leanh::lean_dec(v_l_1537_);
    return v___x_1539_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_1540_: *mut crate::leanh::LeanObject,
    mut v_h__1_1541_: *mut crate::leanh::LeanObject,
    mut v_h__2_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1540_) == 0 {
        let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1542_);
        v___x_1543_ = crate::leanh::lean_box(0);
        v___x_1544_ = crate::leanh::lean_apply_1(v_h__1_1541_, v___x_1543_);
        return v___x_1544_;
    } else {
        let mut v_head_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1541_);
        v_head_1545_ = crate::leanh::lean_ctor_get(v_x_1540_, 0);
        crate::leanh::lean_inc(v_head_1545_);
        v_tail_1546_ = crate::leanh::lean_ctor_get(v_x_1540_, 1);
        crate::leanh::lean_inc(v_tail_1546_);
        crate::leanh::lean_dec_ref_known(v_x_1540_, 2);
        v___x_1547_ = crate::leanh::lean_apply_2(v_h__2_1542_, v_head_1545_, v_tail_1546_);
        return v___x_1547_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_1548_: *mut crate::leanh::LeanObject,
    mut v_motive_1549_: *mut crate::leanh::LeanObject,
    mut v_x_1550_: *mut crate::leanh::LeanObject,
    mut v_h__1_1551_: *mut crate::leanh::LeanObject,
    mut v_h__2_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1550_) == 0 {
        let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1552_);
        v___x_1553_ = crate::leanh::lean_box(0);
        v___x_1554_ = crate::leanh::lean_apply_1(v_h__1_1551_, v___x_1553_);
        return v___x_1554_;
    } else {
        let mut v_head_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1551_);
        v_head_1555_ = crate::leanh::lean_ctor_get(v_x_1550_, 0);
        crate::leanh::lean_inc(v_head_1555_);
        v_tail_1556_ = crate::leanh::lean_ctor_get(v_x_1550_, 1);
        crate::leanh::lean_inc(v_tail_1556_);
        crate::leanh::lean_dec_ref_known(v_x_1550_, 2);
        v___x_1557_ = crate::leanh::lean_apply_2(v_h__2_1552_, v_head_1555_, v_tail_1556_);
        return v___x_1557_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
    mut v_x_1558_: u8,
    mut v_h__1_1559_: *mut crate::leanh::LeanObject,
    mut v_h__2_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1558_ == 0 {
        let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1559_);
        v___x_1561_ = crate::leanh::lean_box(0);
        v___x_1562_ = crate::leanh::lean_apply_1(v_h__2_1560_, v___x_1561_);
        return v___x_1562_;
    } else {
        let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1560_);
        v___x_1563_ = crate::leanh::lean_box(0);
        v___x_1564_ = crate::leanh::lean_apply_1(v_h__1_1559_, v___x_1563_);
        return v___x_1564_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1565_: *mut crate::leanh::LeanObject,
    mut v_h__1_1566_: *mut crate::leanh::LeanObject,
    mut v_h__2_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1568_: u8 = 0;
    let mut v_res_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1568_ = (crate::leanh::lean_unbox(v_x_1565_) as u8);
    v_res_1569_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_1568_,
        v_h__1_1566_,
        v_h__2_1567_,
    );
    return v_res_1569_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
    mut v_motive_1570_: *mut crate::leanh::LeanObject,
    mut v_x_1571_: u8,
    mut v_h__1_1572_: *mut crate::leanh::LeanObject,
    mut v_h__2_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1571_ == 0 {
        let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1572_);
        v___x_1574_ = crate::leanh::lean_box(0);
        v___x_1575_ = crate::leanh::lean_apply_1(v_h__2_1573_, v___x_1574_);
        return v___x_1575_;
    } else {
        let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1573_);
        v___x_1576_ = crate::leanh::lean_box(0);
        v___x_1577_ = crate::leanh::lean_apply_1(v_h__1_1572_, v___x_1576_);
        return v___x_1577_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1578_: *mut crate::leanh::LeanObject,
    mut v_x_1579_: *mut crate::leanh::LeanObject,
    mut v_h__1_1580_: *mut crate::leanh::LeanObject,
    mut v_h__2_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1582_ = (crate::leanh::lean_unbox(v_x_1579_) as u8);
    v_res_1583_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
        v_motive_1578_,
        v_x_37__boxed_1582_,
        v_h__1_1580_,
        v_h__2_1581_,
    );
    return v_res_1583_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(
    mut v_x_1584_: *mut crate::leanh::LeanObject,
    mut v_x_1585_: *mut crate::leanh::LeanObject,
    mut v_h__1_1586_: *mut crate::leanh::LeanObject,
    mut v_h__2_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1584_) == 0 {
        let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1587_);
        v___x_1588_ = crate::leanh::lean_apply_1(v_h__1_1586_, v_x_1585_);
        return v___x_1588_;
    } else {
        let mut v_head_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1586_);
        v_head_1589_ = crate::leanh::lean_ctor_get(v_x_1584_, 0);
        crate::leanh::lean_inc(v_head_1589_);
        v_tail_1590_ = crate::leanh::lean_ctor_get(v_x_1584_, 1);
        crate::leanh::lean_inc(v_tail_1590_);
        crate::leanh::lean_dec_ref_known(v_x_1584_, 2);
        v___x_1591_ =
            crate::leanh::lean_apply_3(v_h__2_1587_, v_head_1589_, v_tail_1590_, v_x_1585_);
        return v___x_1591_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(
    mut v_00_u03b1_1592_: *mut crate::leanh::LeanObject,
    mut v_motive_1593_: *mut crate::leanh::LeanObject,
    mut v_x_1594_: *mut crate::leanh::LeanObject,
    mut v_x_1595_: *mut crate::leanh::LeanObject,
    mut v_h__1_1596_: *mut crate::leanh::LeanObject,
    mut v_h__2_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1594_) == 0 {
        let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1597_);
        v___x_1598_ = crate::leanh::lean_apply_1(v_h__1_1596_, v_x_1595_);
        return v___x_1598_;
    } else {
        let mut v_head_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1596_);
        v_head_1599_ = crate::leanh::lean_ctor_get(v_x_1594_, 0);
        crate::leanh::lean_inc(v_head_1599_);
        v_tail_1600_ = crate::leanh::lean_ctor_get(v_x_1594_, 1);
        crate::leanh::lean_inc(v_tail_1600_);
        crate::leanh::lean_dec_ref_known(v_x_1594_, 2);
        v___x_1601_ =
            crate::leanh::lean_apply_3(v_h__2_1597_, v_head_1599_, v_tail_1600_, v_x_1595_);
        return v___x_1601_;
    }
}
pub unsafe fn l_List_dropLastTR___redArg(
    mut v_l_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_array_mk(v_l_1602_);
    v___x_1604_ = lean_array_pop(v___x_1603_);
    v___x_1605_ = lean_array_to_list(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn l_List_dropLastTR(
    mut v_00_u03b1_1606_: *mut crate::leanh::LeanObject,
    mut v_l_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_array_mk(v_l_1607_);
    v___x_1609_ = lean_array_pop(v___x_1608_);
    v___x_1610_ = lean_array_to_list(v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(
    mut v_p_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1612_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_1611_);
                    v___x_1613_ = crate::leanh::lean_box(0);
                    return v___x_1613_;
                } else {
                    v_head_1614_ = crate::leanh::lean_ctor_get(v_x_1612_, 0);
                    crate::leanh::lean_inc_n(v_head_1614_, 2);
                    v_tail_1615_ = crate::leanh::lean_ctor_get(v_x_1612_, 1);
                    crate::leanh::lean_inc(v_tail_1615_);
                    crate::leanh::lean_dec_ref_known(v_x_1612_, 2);
                    crate::leanh::lean_inc_ref(v_p_1611_);
                    v___x_1616_ = crate::leanh::lean_apply_1(v_p_1611_, v_head_1614_);
                    v___x_1617_ = (crate::leanh::lean_unbox(v___x_1616_) as u8);
                    if v___x_1617_ == 0 {
                        crate::leanh::lean_dec(v_head_1614_);
                        v_x_1612_ = v_tail_1615_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1615_);
                        crate::leanh::lean_dec_ref(v_p_1611_);
                        v___x_1619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1619_, 0, v_head_1614_);
                        return v___x_1619_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findRev_x3fTR___redArg(
    mut v_p_1620_: *mut crate::leanh::LeanObject,
    mut v_l_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_List_reverse___redArg(v_l_1621_);
    v___x_1623_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1620_, v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_List_findRev_x3fTR(
    mut v_00_u03b1_1624_: *mut crate::leanh::LeanObject,
    mut v_p_1625_: *mut crate::leanh::LeanObject,
    mut v_l_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_List_findRev_x3fTR___redArg(v_p_1625_, v_l_1626_);
    return v___x_1627_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(
    mut v_00_u03b1_1628_: *mut crate::leanh::LeanObject,
    mut v_p_1629_: *mut crate::leanh::LeanObject,
    mut v_x_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1629_, v_x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_1632_: *mut crate::leanh::LeanObject,
    mut v_h__1_1633_: *mut crate::leanh::LeanObject,
    mut v_h__2_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1632_) == 0 {
        let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1633_);
        v___x_1635_ = crate::leanh::lean_box(0);
        v___x_1636_ = crate::leanh::lean_apply_1(v_h__2_1634_, v___x_1635_);
        return v___x_1636_;
    } else {
        let mut v_val_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1634_);
        v_val_1637_ = crate::leanh::lean_ctor_get(v_x_1632_, 0);
        crate::leanh::lean_inc(v_val_1637_);
        crate::leanh::lean_dec_ref_known(v_x_1632_, 1);
        v___x_1638_ = crate::leanh::lean_apply_1(v_h__1_1633_, v_val_1637_);
        return v___x_1638_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_motive_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_h__1_1642_: *mut crate::leanh::LeanObject,
    mut v_h__2_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1641_) == 0 {
        let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1642_);
        v___x_1644_ = crate::leanh::lean_box(0);
        v___x_1645_ = crate::leanh::lean_apply_1(v_h__2_1643_, v___x_1644_);
        return v___x_1645_;
    } else {
        let mut v_val_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1643_);
        v_val_1646_ = crate::leanh::lean_ctor_get(v_x_1641_, 0);
        crate::leanh::lean_inc(v_val_1646_);
        crate::leanh::lean_dec_ref_known(v_x_1641_, 1);
        v___x_1647_ = crate::leanh::lean_apply_1(v_h__1_1642_, v_val_1646_);
        return v___x_1647_;
    }
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
    mut v_f_1648_: *mut crate::leanh::LeanObject,
    mut v_x_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1649_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_1648_);
                    v___x_1650_ = crate::leanh::lean_box(0);
                    return v___x_1650_;
                } else {
                    v_head_1651_ = crate::leanh::lean_ctor_get(v_x_1649_, 0);
                    crate::leanh::lean_inc(v_head_1651_);
                    v_tail_1652_ = crate::leanh::lean_ctor_get(v_x_1649_, 1);
                    crate::leanh::lean_inc(v_tail_1652_);
                    crate::leanh::lean_dec_ref_known(v_x_1649_, 2);
                    crate::leanh::lean_inc_ref(v_f_1648_);
                    v___x_1653_ = crate::leanh::lean_apply_1(v_f_1648_, v_head_1651_);
                    if crate::leanh::lean_obj_tag(v___x_1653_) == 0 {
                        v_x_1649_ = v_tail_1652_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_1652_);
                        crate::leanh::lean_dec_ref(v_f_1648_);
                        return v___x_1653_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findSomeRev_x3fTR___redArg(
    mut v_f_1655_: *mut crate::leanh::LeanObject,
    mut v_l_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = l_List_reverse___redArg(v_l_1656_);
    v___x_1658_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
        v_f_1655_,
        v___x_1657_,
    );
    return v___x_1658_;
}
pub unsafe fn l_List_findSomeRev_x3fTR(
    mut v_00_u03b1_1659_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1660_: *mut crate::leanh::LeanObject,
    mut v_f_1661_: *mut crate::leanh::LeanObject,
    mut v_l_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_List_findSomeRev_x3fTR___redArg(v_f_1661_, v_l_1662_);
    return v___x_1663_;
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1665_: *mut crate::leanh::LeanObject,
    mut v_f_1666_: *mut crate::leanh::LeanObject,
    mut v_x_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ =
        l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_1666_, v_x_1667_);
    return v___x_1668_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(
    mut v_x1_1669_: *mut crate::leanh::LeanObject,
    mut v_x2_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1671_, 0, v_x1_1669_);
    crate::leanh::lean_ctor_set(v___x_1671_, 1, v_x2_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_l_1674_: *mut crate::leanh::LeanObject,
    mut v_b_1675_: *mut crate::leanh::LeanObject,
    mut v_c_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v_a_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___f_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: usize = 0;
    let mut v___x_1696_: usize = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1677_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1678_);
                    crate::leanh::lean_dec(v_c_1676_);
                    crate::leanh::lean_dec(v_b_1675_);
                    crate::leanh::lean_dec_ref(v_inst_1673_);
                    crate::leanh::lean_inc(v_l_1674_);
                    return v_l_1674_;
                } else {
                    v_head_1679_ = crate::leanh::lean_ctor_get(v_a_1677_, 0);
                    v_tail_1680_ = crate::leanh::lean_ctor_get(v_a_1677_, 1);
                    v_isSharedCheck_1699_ = (!crate::leanh::lean_is_exclusive(v_a_1677_)) as u8;
                    if v_isSharedCheck_1699_ == 0 {
                        v___x_1682_ = v_a_1677_;
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1680_);
                        crate::leanh::lean_inc(v_head_1679_);
                        crate::leanh::lean_dec(v_a_1677_);
                        v___x_1682_ = crate::leanh::lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1673_);
                crate::leanh::lean_inc(v_head_1679_);
                crate::leanh::lean_inc(v_b_1675_);
                v___x_1684_ = crate::leanh::lean_apply_2(v_inst_1673_, v_b_1675_, v_head_1679_);
                v___x_1685_ = (crate::leanh::lean_unbox(v___x_1684_) as u8);
                if v___x_1685_ == 0 {
                    crate::leanh::lean_del_object(v___x_1682_);
                    v___x_1686_ = lean_array_push(v_a_1678_, v_head_1679_);
                    v_a_1677_ = v_tail_1680_;
                    v_a_1678_ = v___x_1686_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_head_1679_);
                    crate::leanh::lean_dec(v_b_1675_);
                    crate::leanh::lean_dec_ref(v_inst_1673_);
                    if v_isShared_1683_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1682_, 0, v_c_1676_);
                        v___x_1689_ = v___x_1682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_c_1676_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_tail_1680_);
                        v___x_1689_ = v_reuseFailAlloc_1698_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1690_ = lean_array_get_size(v_a_1678_);
                v___x_1691_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1692_ = l_List_foldrTR___redArg___closed__9;
                v___x_1693_ = lean_nat_dec_lt(v___x_1691_, v___x_1690_);
                if v___x_1693_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_1678_);
                    return v___x_1689_;
                } else {
                    v___f_1694_ =
                        l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                    v___x_1695_ = lean_usize_of_nat(v___x_1690_);
                    v___x_1696_ = 0usize;
                    v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1692_,
                        v___f_1694_,
                        v_a_1678_,
                        v___x_1695_,
                        v___x_1696_,
                        v___x_1689_,
                    );
                    return v___x_1697_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(
    mut v_inst_1700_: *mut crate::leanh::LeanObject,
    mut v_l_1701_: *mut crate::leanh::LeanObject,
    mut v_b_1702_: *mut crate::leanh::LeanObject,
    mut v_c_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1706_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1700_,
        v_l_1701_,
        v_b_1702_,
        v_c_1703_,
        v_a_1704_,
        v_a_1705_,
    );
    crate::leanh::lean_dec(v_l_1701_);
    return v_res_1706_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go(
    mut v_00_u03b1_1707_: *mut crate::leanh::LeanObject,
    mut v_inst_1708_: *mut crate::leanh::LeanObject,
    mut v_l_1709_: *mut crate::leanh::LeanObject,
    mut v_b_1710_: *mut crate::leanh::LeanObject,
    mut v_c_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1708_,
        v_l_1709_,
        v_b_1710_,
        v_c_1711_,
        v_a_1712_,
        v_a_1713_,
    );
    return v___x_1714_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(
    mut v_00_u03b1_1715_: *mut crate::leanh::LeanObject,
    mut v_inst_1716_: *mut crate::leanh::LeanObject,
    mut v_l_1717_: *mut crate::leanh::LeanObject,
    mut v_b_1718_: *mut crate::leanh::LeanObject,
    mut v_c_1719_: *mut crate::leanh::LeanObject,
    mut v_a_1720_: *mut crate::leanh::LeanObject,
    mut v_a_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(
        v_00_u03b1_1715_,
        v_inst_1716_,
        v_l_1717_,
        v_b_1718_,
        v_c_1719_,
        v_a_1720_,
        v_a_1721_,
    );
    crate::leanh::lean_dec(v_l_1717_);
    return v_res_1722_;
}
pub unsafe fn l_List_replaceTR___redArg(
    mut v_inst_1723_: *mut crate::leanh::LeanObject,
    mut v_l_1724_: *mut crate::leanh::LeanObject,
    mut v_b_1725_: *mut crate::leanh::LeanObject,
    mut v_c_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1724_);
    v___x_1728_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1723_,
        v_l_1724_,
        v_b_1725_,
        v_c_1726_,
        v_l_1724_,
        v___x_1727_,
    );
    crate::leanh::lean_dec(v_l_1724_);
    return v___x_1728_;
}
pub unsafe fn l_List_replaceTR(
    mut v_00_u03b1_1729_: *mut crate::leanh::LeanObject,
    mut v_inst_1730_: *mut crate::leanh::LeanObject,
    mut v_l_1731_: *mut crate::leanh::LeanObject,
    mut v_b_1732_: *mut crate::leanh::LeanObject,
    mut v_c_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1731_);
    v___x_1735_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1730_,
        v_l_1731_,
        v_b_1732_,
        v_c_1733_,
        v_l_1731_,
        v___x_1734_,
    );
    crate::leanh::lean_dec(v_l_1731_);
    return v___x_1735_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(
    mut v_x_1736_: *mut crate::leanh::LeanObject,
    mut v_x_1737_: *mut crate::leanh::LeanObject,
    mut v_x_1738_: *mut crate::leanh::LeanObject,
    mut v_h__1_1739_: *mut crate::leanh::LeanObject,
    mut v_h__2_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1736_) == 0 {
        let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1740_);
        v___x_1741_ = crate::leanh::lean_apply_2(v_h__1_1739_, v_x_1737_, v_x_1738_);
        return v___x_1741_;
    } else {
        let mut v_head_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1739_);
        v_head_1742_ = crate::leanh::lean_ctor_get(v_x_1736_, 0);
        crate::leanh::lean_inc(v_head_1742_);
        v_tail_1743_ = crate::leanh::lean_ctor_get(v_x_1736_, 1);
        crate::leanh::lean_inc(v_tail_1743_);
        crate::leanh::lean_dec_ref_known(v_x_1736_, 2);
        v___x_1744_ = crate::leanh::lean_apply_4(
            v_h__2_1740_,
            v_head_1742_,
            v_tail_1743_,
            v_x_1737_,
            v_x_1738_,
        );
        return v___x_1744_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(
    mut v_00_u03b1_1745_: *mut crate::leanh::LeanObject,
    mut v_motive_1746_: *mut crate::leanh::LeanObject,
    mut v_x_1747_: *mut crate::leanh::LeanObject,
    mut v_x_1748_: *mut crate::leanh::LeanObject,
    mut v_x_1749_: *mut crate::leanh::LeanObject,
    mut v_h__1_1750_: *mut crate::leanh::LeanObject,
    mut v_h__2_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1747_) == 0 {
        let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1751_);
        v___x_1752_ = crate::leanh::lean_apply_2(v_h__1_1750_, v_x_1748_, v_x_1749_);
        return v___x_1752_;
    } else {
        let mut v_head_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1750_);
        v_head_1753_ = crate::leanh::lean_ctor_get(v_x_1747_, 0);
        crate::leanh::lean_inc(v_head_1753_);
        v_tail_1754_ = crate::leanh::lean_ctor_get(v_x_1747_, 1);
        crate::leanh::lean_inc(v_tail_1754_);
        crate::leanh::lean_dec_ref_known(v_x_1747_, 2);
        v___x_1755_ = crate::leanh::lean_apply_4(
            v_h__2_1751_,
            v_head_1753_,
            v_tail_1754_,
            v_x_1748_,
            v_x_1749_,
        );
        return v___x_1755_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(
    mut v_f_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v_zero_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: usize = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1757_) == 0 {
                    crate::leanh::lean_dec(v_a_1758_);
                    crate::leanh::lean_dec(v_f_1756_);
                    v___x_1760_ = lean_array_to_list(v_a_1759_);
                    return v___x_1760_;
                } else {
                    v_head_1761_ = crate::leanh::lean_ctor_get(v_a_1757_, 0);
                    v_tail_1762_ = crate::leanh::lean_ctor_get(v_a_1757_, 1);
                    v_isSharedCheck_1781_ = (!crate::leanh::lean_is_exclusive(v_a_1757_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v___x_1764_ = v_a_1757_;
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1762_);
                        crate::leanh::lean_inc(v_head_1761_);
                        crate::leanh::lean_dec(v_a_1757_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1766_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1767_ = lean_nat_dec_eq(v_a_1758_, v_zero_1766_);
                if v_isZero_1767_ == 1 {
                    crate::leanh::lean_dec(v_a_1758_);
                    v___x_1768_ = crate::leanh::lean_apply_1(v_f_1756_, v_head_1761_);
                    if v_isShared_1765_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1764_, 0, v___x_1768_);
                        v___x_1770_ = v___x_1764_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1776_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_tail_1762_);
                        v___x_1770_ = v_reuseFailAlloc_1776_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1764_);
                    v_one_1777_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1778_ = lean_nat_sub(v_a_1758_, v_one_1777_);
                    crate::leanh::lean_dec(v_a_1758_);
                    v___x_1779_ = lean_array_push(v_a_1759_, v_head_1761_);
                    v_a_1757_ = v_tail_1762_;
                    v_a_1758_ = v_n_1778_;
                    v_a_1759_ = v___x_1779_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1771_ = lean_array_get_size(v_a_1759_);
                v___x_1772_ = lean_nat_dec_lt(v_zero_1766_, v___x_1771_);
                if v___x_1772_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_1759_);
                    return v___x_1770_;
                } else {
                    v___x_1773_ = lean_usize_of_nat(v___x_1771_);
                    v___x_1774_ = 0usize;
                    v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1759_, v___x_1773_, v___x_1774_, v___x_1770_);
                    crate::leanh::lean_dec_ref(v_a_1759_);
                    return v___x_1775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_modifyTR_go(
    mut v_00_u03b1_1782_: *mut crate::leanh::LeanObject,
    mut v_f_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(
        v_f_1783_, v_a_1784_, v_a_1785_, v_a_1786_,
    );
    return v___x_1787_;
}
pub unsafe fn l_List_modifyTR___redArg(
    mut v_l_1788_: *mut crate::leanh::LeanObject,
    mut v_i_1789_: *mut crate::leanh::LeanObject,
    mut v_f_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = l_List_setTR___redArg___closed__0;
    v___x_1792_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(
        v_f_1790_,
        v_l_1788_,
        v_i_1789_,
        v___x_1791_,
    );
    return v___x_1792_;
}
pub unsafe fn l_List_modifyTR(
    mut v_00_u03b1_1793_: *mut crate::leanh::LeanObject,
    mut v_l_1794_: *mut crate::leanh::LeanObject,
    mut v_i_1795_: *mut crate::leanh::LeanObject,
    mut v_f_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1797_ = l_List_modifyTR___redArg(v_l_1794_, v_i_1795_, v_f_1796_);
    return v___x_1797_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1802_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1803_ = lean_nat_dec_eq(v_a_1799_, v_zero_1802_);
                if v_isZero_1803_ == 1 {
                    crate::leanh::lean_dec(v_a_1799_);
                    v___x_1804_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1804_, 0, v_a_1798_);
                    crate::leanh::lean_ctor_set(v___x_1804_, 1, v_a_1800_);
                    v___x_1805_ = lean_array_get_size(v_a_1801_);
                    v___x_1806_ = lean_nat_dec_lt(v_zero_1802_, v___x_1805_);
                    if v___x_1806_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_1801_);
                        return v___x_1804_;
                    } else {
                        v___x_1807_ = lean_usize_of_nat(v___x_1805_);
                        v___x_1808_ = 0usize;
                        v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1801_, v___x_1807_, v___x_1808_, v___x_1804_);
                        crate::leanh::lean_dec_ref(v_a_1801_);
                        return v___x_1809_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_a_1800_) == 0 {
                        crate::leanh::lean_dec(v_a_1799_);
                        crate::leanh::lean_dec(v_a_1798_);
                        v___x_1810_ = lean_array_to_list(v_a_1801_);
                        return v___x_1810_;
                    } else {
                        v_head_1811_ = crate::leanh::lean_ctor_get(v_a_1800_, 0);
                        crate::leanh::lean_inc(v_head_1811_);
                        v_tail_1812_ = crate::leanh::lean_ctor_get(v_a_1800_, 1);
                        crate::leanh::lean_inc(v_tail_1812_);
                        crate::leanh::lean_dec_ref_known(v_a_1800_, 2);
                        v_one_1813_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1814_ = lean_nat_sub(v_a_1799_, v_one_1813_);
                        crate::leanh::lean_dec(v_a_1799_);
                        v___x_1815_ = lean_array_push(v_a_1801_, v_head_1811_);
                        v_a_1799_ = v_n_1814_;
                        v_a_1800_ = v_tail_1812_;
                        v_a_1801_ = v___x_1815_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(
    mut v_00_u03b1_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
        v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_,
    );
    return v___x_1822_;
}
pub unsafe fn l_List_insertIdxTR___redArg(
    mut v_l_1823_: *mut crate::leanh::LeanObject,
    mut v_n_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = l_List_setTR___redArg___closed__0;
    v___x_1827_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
        v_a_1825_,
        v_n_1824_,
        v_l_1823_,
        v___x_1826_,
    );
    return v___x_1827_;
}
pub unsafe fn l_List_insertIdxTR(
    mut v_00_u03b1_1828_: *mut crate::leanh::LeanObject,
    mut v_l_1829_: *mut crate::leanh::LeanObject,
    mut v_n_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_List_setTR___redArg___closed__0;
    v___x_1833_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
        v_a_1831_,
        v_n_1830_,
        v_l_1829_,
        v___x_1832_,
    );
    return v___x_1833_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(
    mut v_x_1834_: *mut crate::leanh::LeanObject,
    mut v_x_1835_: *mut crate::leanh::LeanObject,
    mut v_x_1836_: *mut crate::leanh::LeanObject,
    mut v_h__1_1837_: *mut crate::leanh::LeanObject,
    mut v_h__2_1838_: *mut crate::leanh::LeanObject,
    mut v_h__3_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1841_: u8 = 0;
    v_zero_1840_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1841_ = lean_nat_dec_eq(v_x_1834_, v_zero_1840_);
    if v_isZero_1841_ == 1 {
        let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1839_);
        crate::leanh::lean_dec(v_h__2_1838_);
        crate::leanh::lean_dec(v_x_1834_);
        v___x_1842_ = crate::leanh::lean_apply_2(v_h__1_1837_, v_x_1835_, v_x_1836_);
        return v___x_1842_;
    } else {
        crate::leanh::lean_dec(v_h__1_1837_);
        if crate::leanh::lean_obj_tag(v_x_1835_) == 0 {
            let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1839_);
            v___x_1843_ = crate::leanh::lean_apply_3(
                v_h__2_1838_,
                v_x_1834_,
                v_x_1836_,
                crate::leanh::lean_box(0),
            );
            return v___x_1843_;
        } else {
            let mut v_head_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1838_);
            v_head_1844_ = crate::leanh::lean_ctor_get(v_x_1835_, 0);
            crate::leanh::lean_inc(v_head_1844_);
            v_tail_1845_ = crate::leanh::lean_ctor_get(v_x_1835_, 1);
            crate::leanh::lean_inc(v_tail_1845_);
            crate::leanh::lean_dec_ref_known(v_x_1835_, 2);
            v_one_1846_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1847_ = lean_nat_sub(v_x_1834_, v_one_1846_);
            crate::leanh::lean_dec(v_x_1834_);
            v___x_1848_ = crate::leanh::lean_apply_4(
                v_h__3_1839_,
                v_n_1847_,
                v_head_1844_,
                v_tail_1845_,
                v_x_1836_,
            );
            return v___x_1848_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(
    mut v_00_u03b1_1849_: *mut crate::leanh::LeanObject,
    mut v_motive_1850_: *mut crate::leanh::LeanObject,
    mut v_x_1851_: *mut crate::leanh::LeanObject,
    mut v_x_1852_: *mut crate::leanh::LeanObject,
    mut v_x_1853_: *mut crate::leanh::LeanObject,
    mut v_h__1_1854_: *mut crate::leanh::LeanObject,
    mut v_h__2_1855_: *mut crate::leanh::LeanObject,
    mut v_h__3_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1858_: u8 = 0;
    v_zero_1857_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1858_ = lean_nat_dec_eq(v_x_1851_, v_zero_1857_);
    if v_isZero_1858_ == 1 {
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1856_);
        crate::leanh::lean_dec(v_h__2_1855_);
        crate::leanh::lean_dec(v_x_1851_);
        v___x_1859_ = crate::leanh::lean_apply_2(v_h__1_1854_, v_x_1852_, v_x_1853_);
        return v___x_1859_;
    } else {
        crate::leanh::lean_dec(v_h__1_1854_);
        if crate::leanh::lean_obj_tag(v_x_1852_) == 0 {
            let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1856_);
            v___x_1860_ = crate::leanh::lean_apply_3(
                v_h__2_1855_,
                v_x_1851_,
                v_x_1853_,
                crate::leanh::lean_box(0),
            );
            return v___x_1860_;
        } else {
            let mut v_head_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1855_);
            v_head_1861_ = crate::leanh::lean_ctor_get(v_x_1852_, 0);
            crate::leanh::lean_inc(v_head_1861_);
            v_tail_1862_ = crate::leanh::lean_ctor_get(v_x_1852_, 1);
            crate::leanh::lean_inc(v_tail_1862_);
            crate::leanh::lean_dec_ref_known(v_x_1852_, 2);
            v_one_1863_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1864_ = lean_nat_sub(v_x_1851_, v_one_1863_);
            crate::leanh::lean_dec(v_x_1851_);
            v___x_1865_ = crate::leanh::lean_apply_4(
                v_h__3_1856_,
                v_n_1864_,
                v_head_1861_,
                v_tail_1862_,
                v_x_1853_,
            );
            return v___x_1865_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_l_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___f_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1869_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1870_);
                    crate::leanh::lean_dec(v_a_1868_);
                    crate::leanh::lean_dec_ref(v_inst_1866_);
                    crate::leanh::lean_inc(v_l_1867_);
                    return v_l_1867_;
                } else {
                    v_head_1871_ = crate::leanh::lean_ctor_get(v_a_1869_, 0);
                    crate::leanh::lean_inc_n(v_head_1871_, 2);
                    v_tail_1872_ = crate::leanh::lean_ctor_get(v_a_1869_, 1);
                    crate::leanh::lean_inc(v_tail_1872_);
                    crate::leanh::lean_dec_ref_known(v_a_1869_, 2);
                    crate::leanh::lean_inc_ref(v_inst_1866_);
                    crate::leanh::lean_inc(v_a_1868_);
                    v___x_1873_ = crate::leanh::lean_apply_2(v_inst_1866_, v_head_1871_, v_a_1868_);
                    v___x_1874_ = (crate::leanh::lean_unbox(v___x_1873_) as u8);
                    if v___x_1874_ == 0 {
                        v___x_1875_ = lean_array_push(v_a_1870_, v_head_1871_);
                        v_a_1869_ = v_tail_1872_;
                        v_a_1870_ = v___x_1875_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_1871_);
                        crate::leanh::lean_dec(v_a_1868_);
                        crate::leanh::lean_dec_ref(v_inst_1866_);
                        v___x_1877_ = lean_array_get_size(v_a_1870_);
                        v___x_1878_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1879_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1880_ = lean_nat_dec_lt(v___x_1878_, v___x_1877_);
                        if v___x_1880_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1870_);
                            return v_tail_1872_;
                        } else {
                            v___f_1881_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1882_ = lean_usize_of_nat(v___x_1877_);
                            v___x_1883_ = 0usize;
                            v___x_1884_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_1879_,
                                    v___f_1881_,
                                    v_a_1870_,
                                    v___x_1882_,
                                    v___x_1883_,
                                    v_tail_1872_,
                                );
                            return v___x_1884_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
    mut v_l_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1885_,
        v_l_1886_,
        v_a_1887_,
        v_a_1888_,
        v_a_1889_,
    );
    crate::leanh::lean_dec(v_l_1886_);
    return v_res_1890_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go(
    mut v_00_u03b1_1891_: *mut crate::leanh::LeanObject,
    mut v_inst_1892_: *mut crate::leanh::LeanObject,
    mut v_l_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1892_,
        v_l_1893_,
        v_a_1894_,
        v_a_1895_,
        v_a_1896_,
    );
    return v___x_1897_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(
    mut v_00_u03b1_1898_: *mut crate::leanh::LeanObject,
    mut v_inst_1899_: *mut crate::leanh::LeanObject,
    mut v_l_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(
        v_00_u03b1_1898_,
        v_inst_1899_,
        v_l_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
    );
    crate::leanh::lean_dec(v_l_1900_);
    return v_res_1904_;
}
pub unsafe fn l_List_eraseTR___redArg(
    mut v_inst_1905_: *mut crate::leanh::LeanObject,
    mut v_l_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1906_);
    v___x_1909_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1905_,
        v_l_1906_,
        v_a_1907_,
        v_l_1906_,
        v___x_1908_,
    );
    crate::leanh::lean_dec(v_l_1906_);
    return v___x_1909_;
}
pub unsafe fn l_List_eraseTR(
    mut v_00_u03b1_1910_: *mut crate::leanh::LeanObject,
    mut v_inst_1911_: *mut crate::leanh::LeanObject,
    mut v_l_1912_: *mut crate::leanh::LeanObject,
    mut v_a_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1912_);
    v___x_1915_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1911_,
        v_l_1912_,
        v_a_1913_,
        v_l_1912_,
        v___x_1914_,
    );
    crate::leanh::lean_dec(v_l_1912_);
    return v___x_1915_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
    mut v_p_1916_: *mut crate::leanh::LeanObject,
    mut v_l_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
    mut v_a_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___f_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: usize = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1918_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1919_);
                    crate::leanh::lean_dec_ref(v_p_1916_);
                    crate::leanh::lean_inc(v_l_1917_);
                    return v_l_1917_;
                } else {
                    v_head_1920_ = crate::leanh::lean_ctor_get(v_a_1918_, 0);
                    crate::leanh::lean_inc_n(v_head_1920_, 2);
                    v_tail_1921_ = crate::leanh::lean_ctor_get(v_a_1918_, 1);
                    crate::leanh::lean_inc(v_tail_1921_);
                    crate::leanh::lean_dec_ref_known(v_a_1918_, 2);
                    crate::leanh::lean_inc_ref(v_p_1916_);
                    v___x_1922_ = crate::leanh::lean_apply_1(v_p_1916_, v_head_1920_);
                    v___x_1923_ = (crate::leanh::lean_unbox(v___x_1922_) as u8);
                    if v___x_1923_ == 0 {
                        v___x_1924_ = lean_array_push(v_a_1919_, v_head_1920_);
                        v_a_1918_ = v_tail_1921_;
                        v_a_1919_ = v___x_1924_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_1920_);
                        crate::leanh::lean_dec_ref(v_p_1916_);
                        v___x_1926_ = lean_array_get_size(v_a_1919_);
                        v___x_1927_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1928_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1929_ = lean_nat_dec_lt(v___x_1927_, v___x_1926_);
                        if v___x_1929_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1919_);
                            return v_tail_1921_;
                        } else {
                            v___f_1930_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1931_ = lean_usize_of_nat(v___x_1926_);
                            v___x_1932_ = 0usize;
                            v___x_1933_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_1928_,
                                    v___f_1930_,
                                    v_a_1919_,
                                    v___x_1931_,
                                    v___x_1932_,
                                    v_tail_1921_,
                                );
                            return v___x_1933_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(
    mut v_p_1934_: *mut crate::leanh::LeanObject,
    mut v_l_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1934_, v_l_1935_, v_a_1936_, v_a_1937_,
    );
    crate::leanh::lean_dec(v_l_1935_);
    return v_res_1938_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go(
    mut v_00_u03b1_1939_: *mut crate::leanh::LeanObject,
    mut v_p_1940_: *mut crate::leanh::LeanObject,
    mut v_l_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1940_, v_l_1941_, v_a_1942_, v_a_1943_,
    );
    return v___x_1944_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(
    mut v_00_u03b1_1945_: *mut crate::leanh::LeanObject,
    mut v_p_1946_: *mut crate::leanh::LeanObject,
    mut v_l_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(
        v_00_u03b1_1945_,
        v_p_1946_,
        v_l_1947_,
        v_a_1948_,
        v_a_1949_,
    );
    crate::leanh::lean_dec(v_l_1947_);
    return v_res_1950_;
}
pub unsafe fn l_List_erasePTR___redArg(
    mut v_p_1951_: *mut crate::leanh::LeanObject,
    mut v_l_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1952_);
    v___x_1954_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1951_,
        v_l_1952_,
        v_l_1952_,
        v___x_1953_,
    );
    crate::leanh::lean_dec(v_l_1952_);
    return v___x_1954_;
}
pub unsafe fn l_List_erasePTR(
    mut v_00_u03b1_1955_: *mut crate::leanh::LeanObject,
    mut v_p_1956_: *mut crate::leanh::LeanObject,
    mut v_l_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1957_);
    v___x_1959_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1956_,
        v_l_1957_,
        v_l_1957_,
        v___x_1958_,
    );
    crate::leanh::lean_dec(v_l_1957_);
    return v___x_1959_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
    mut v_l_1960_: *mut crate::leanh::LeanObject,
    mut v_a_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1967_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1961_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1963_);
                    crate::leanh::lean_dec(v_a_1962_);
                    crate::leanh::lean_inc(v_l_1960_);
                    return v_l_1960_;
                } else {
                    v_head_1964_ = crate::leanh::lean_ctor_get(v_a_1961_, 0);
                    crate::leanh::lean_inc(v_head_1964_);
                    v_tail_1965_ = crate::leanh::lean_ctor_get(v_a_1961_, 1);
                    crate::leanh::lean_inc(v_tail_1965_);
                    crate::leanh::lean_dec_ref_known(v_a_1961_, 2);
                    v_zero_1966_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_1967_ = lean_nat_dec_eq(v_a_1962_, v_zero_1966_);
                    if v_isZero_1967_ == 1 {
                        crate::leanh::lean_dec(v_head_1964_);
                        crate::leanh::lean_dec(v_a_1962_);
                        v___x_1968_ = lean_array_get_size(v_a_1963_);
                        v___x_1969_ = lean_nat_dec_lt(v_zero_1966_, v___x_1968_);
                        if v___x_1969_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1963_);
                            return v_tail_1965_;
                        } else {
                            v___x_1970_ = lean_usize_of_nat(v___x_1968_);
                            v___x_1971_ = 0usize;
                            v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1963_, v___x_1970_, v___x_1971_, v_tail_1965_);
                            crate::leanh::lean_dec_ref(v_a_1963_);
                            return v___x_1972_;
                        }
                    } else {
                        v_one_1973_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1974_ = lean_nat_sub(v_a_1962_, v_one_1973_);
                        crate::leanh::lean_dec(v_a_1962_);
                        v___x_1975_ = lean_array_push(v_a_1963_, v_head_1964_);
                        v_a_1961_ = v_tail_1965_;
                        v_a_1962_ = v_n_1974_;
                        v_a_1963_ = v___x_1975_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(
    mut v_l_1977_: *mut crate::leanh::LeanObject,
    mut v_a_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1977_, v_a_1978_, v_a_1979_, v_a_1980_,
    );
    crate::leanh::lean_dec(v_l_1977_);
    return v_res_1981_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
    mut v_00_u03b1_1982_: *mut crate::leanh::LeanObject,
    mut v_l_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1983_, v_a_1984_, v_a_1985_, v_a_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(
    mut v_00_u03b1_1988_: *mut crate::leanh::LeanObject,
    mut v_l_1989_: *mut crate::leanh::LeanObject,
    mut v_a_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1993_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
        v_00_u03b1_1988_,
        v_l_1989_,
        v_a_1990_,
        v_a_1991_,
        v_a_1992_,
    );
    crate::leanh::lean_dec(v_l_1989_);
    return v_res_1993_;
}
pub unsafe fn l_List_eraseIdxTR___redArg(
    mut v_l_1994_: *mut crate::leanh::LeanObject,
    mut v_n_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1994_);
    v___x_1997_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1994_,
        v_l_1994_,
        v_n_1995_,
        v___x_1996_,
    );
    crate::leanh::lean_dec(v_l_1994_);
    return v___x_1997_;
}
pub unsafe fn l_List_eraseIdxTR(
    mut v_00_u03b1_1998_: *mut crate::leanh::LeanObject,
    mut v_l_1999_: *mut crate::leanh::LeanObject,
    mut v_n_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_List_setTR___redArg___closed__0;
    crate::leanh::lean_inc(v_l_1999_);
    v___x_2002_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1999_,
        v_l_1999_,
        v_n_2000_,
        v___x_2001_,
    );
    crate::leanh::lean_dec(v_l_1999_);
    return v___x_2002_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(
    mut v_x_2003_: *mut crate::leanh::LeanObject,
    mut v_x_2004_: *mut crate::leanh::LeanObject,
    mut v_h__1_2005_: *mut crate::leanh::LeanObject,
    mut v_h__2_2006_: *mut crate::leanh::LeanObject,
    mut v_h__3_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2003_) == 0 {
        let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2007_);
        crate::leanh::lean_dec(v_h__2_2006_);
        v___x_2008_ = crate::leanh::lean_apply_1(v_h__1_2005_, v_x_2004_);
        return v___x_2008_;
    } else {
        let mut v_head_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_2012_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_2005_);
        v_head_2009_ = crate::leanh::lean_ctor_get(v_x_2003_, 0);
        crate::leanh::lean_inc(v_head_2009_);
        v_tail_2010_ = crate::leanh::lean_ctor_get(v_x_2003_, 1);
        crate::leanh::lean_inc(v_tail_2010_);
        crate::leanh::lean_dec_ref_known(v_x_2003_, 2);
        v_zero_2011_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_2012_ = lean_nat_dec_eq(v_x_2004_, v_zero_2011_);
        if v_isZero_2012_ == 1 {
            let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2007_);
            crate::leanh::lean_dec(v_x_2004_);
            v___x_2013_ = crate::leanh::lean_apply_2(v_h__2_2006_, v_head_2009_, v_tail_2010_);
            return v___x_2013_;
        } else {
            let mut v_one_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2006_);
            v_one_2014_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_2015_ = lean_nat_sub(v_x_2004_, v_one_2014_);
            crate::leanh::lean_dec(v_x_2004_);
            v___x_2016_ =
                crate::leanh::lean_apply_3(v_h__3_2007_, v_head_2009_, v_tail_2010_, v_n_2015_);
            return v___x_2016_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(
    mut v_00_u03b1_2017_: *mut crate::leanh::LeanObject,
    mut v_motive_2018_: *mut crate::leanh::LeanObject,
    mut v_x_2019_: *mut crate::leanh::LeanObject,
    mut v_x_2020_: *mut crate::leanh::LeanObject,
    mut v_h__1_2021_: *mut crate::leanh::LeanObject,
    mut v_h__2_2022_: *mut crate::leanh::LeanObject,
    mut v_h__3_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2019_) == 0 {
        let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2023_);
        crate::leanh::lean_dec(v_h__2_2022_);
        v___x_2024_ = crate::leanh::lean_apply_1(v_h__1_2021_, v_x_2020_);
        return v___x_2024_;
    } else {
        let mut v_head_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_2028_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_2021_);
        v_head_2025_ = crate::leanh::lean_ctor_get(v_x_2019_, 0);
        crate::leanh::lean_inc(v_head_2025_);
        v_tail_2026_ = crate::leanh::lean_ctor_get(v_x_2019_, 1);
        crate::leanh::lean_inc(v_tail_2026_);
        crate::leanh::lean_dec_ref_known(v_x_2019_, 2);
        v_zero_2027_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_2028_ = lean_nat_dec_eq(v_x_2020_, v_zero_2027_);
        if v_isZero_2028_ == 1 {
            let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2023_);
            crate::leanh::lean_dec(v_x_2020_);
            v___x_2029_ = crate::leanh::lean_apply_2(v_h__2_2022_, v_head_2025_, v_tail_2026_);
            return v___x_2029_;
        } else {
            let mut v_one_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2022_);
            v_one_2030_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_2031_ = lean_nat_sub(v_x_2020_, v_one_2030_);
            crate::leanh::lean_dec(v_x_2020_);
            v___x_2032_ =
                crate::leanh::lean_apply_3(v_h__3_2023_, v_head_2025_, v_tail_2026_, v_n_2031_);
            return v___x_2032_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
    mut v_f_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_a_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2034_) == 1 {
                    if crate::leanh::lean_obj_tag(v_a_2035_) == 1 {
                        v_head_2037_ = crate::leanh::lean_ctor_get(v_a_2034_, 0);
                        crate::leanh::lean_inc(v_head_2037_);
                        v_tail_2038_ = crate::leanh::lean_ctor_get(v_a_2034_, 1);
                        crate::leanh::lean_inc(v_tail_2038_);
                        crate::leanh::lean_dec_ref_known(v_a_2034_, 2);
                        v_head_2039_ = crate::leanh::lean_ctor_get(v_a_2035_, 0);
                        crate::leanh::lean_inc(v_head_2039_);
                        v_tail_2040_ = crate::leanh::lean_ctor_get(v_a_2035_, 1);
                        crate::leanh::lean_inc(v_tail_2040_);
                        crate::leanh::lean_dec_ref_known(v_a_2035_, 2);
                        crate::leanh::lean_inc(v_f_2033_);
                        v___x_2041_ =
                            crate::leanh::lean_apply_2(v_f_2033_, v_head_2037_, v_head_2039_);
                        v___x_2042_ = lean_array_push(v_a_2036_, v___x_2041_);
                        v_a_2034_ = v_tail_2038_;
                        v_a_2035_ = v_tail_2040_;
                        v_a_2036_ = v___x_2042_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_2034_, 2);
                        crate::leanh::lean_dec(v_a_2035_);
                        crate::leanh::lean_dec(v_f_2033_);
                        v___x_2044_ = lean_array_to_list(v_a_2036_);
                        return v___x_2044_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2035_);
                    crate::leanh::lean_dec(v_a_2034_);
                    crate::leanh::lean_dec(v_f_2033_);
                    v___x_2045_ = lean_array_to_list(v_a_2036_);
                    return v___x_2045_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
    mut v_00_u03b1_2046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2047_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2048_: *mut crate::leanh::LeanObject,
    mut v_f_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
    mut v_a_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
        v_f_2049_, v_a_2050_, v_a_2051_, v_a_2052_,
    );
    return v___x_2053_;
}
pub unsafe fn l_List_zipWithTR___redArg(
    mut v_f_2054_: *mut crate::leanh::LeanObject,
    mut v_as_2055_: *mut crate::leanh::LeanObject,
    mut v_bs_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_List_setTR___redArg___closed__0;
    v___x_2058_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
        v_f_2054_,
        v_as_2055_,
        v_bs_2056_,
        v___x_2057_,
    );
    return v___x_2058_;
}
pub unsafe fn l_List_zipWithTR(
    mut v_00_u03b1_2059_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2060_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2061_: *mut crate::leanh::LeanObject,
    mut v_f_2062_: *mut crate::leanh::LeanObject,
    mut v_as_2063_: *mut crate::leanh::LeanObject,
    mut v_bs_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_List_setTR___redArg___closed__0;
    v___x_2066_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
        v_f_2062_,
        v_as_2063_,
        v_bs_2064_,
        v___x_2065_,
    );
    return v___x_2066_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(
    mut v_x_2067_: *mut crate::leanh::LeanObject,
    mut v_x_2068_: *mut crate::leanh::LeanObject,
    mut v_x_2069_: *mut crate::leanh::LeanObject,
    mut v_h__1_2070_: *mut crate::leanh::LeanObject,
    mut v_h__2_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2067_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_2068_) == 1 {
            let mut v_head_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2071_);
            v_head_2072_ = crate::leanh::lean_ctor_get(v_x_2067_, 0);
            crate::leanh::lean_inc(v_head_2072_);
            v_tail_2073_ = crate::leanh::lean_ctor_get(v_x_2067_, 1);
            crate::leanh::lean_inc(v_tail_2073_);
            crate::leanh::lean_dec_ref_known(v_x_2067_, 2);
            v_head_2074_ = crate::leanh::lean_ctor_get(v_x_2068_, 0);
            crate::leanh::lean_inc(v_head_2074_);
            v_tail_2075_ = crate::leanh::lean_ctor_get(v_x_2068_, 1);
            crate::leanh::lean_inc(v_tail_2075_);
            crate::leanh::lean_dec_ref_known(v_x_2068_, 2);
            v___x_2076_ = crate::leanh::lean_apply_5(
                v_h__1_2070_,
                v_head_2072_,
                v_tail_2073_,
                v_head_2074_,
                v_tail_2075_,
                v_x_2069_,
            );
            return v___x_2076_;
        } else {
            let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2070_);
            v___x_2077_ = crate::leanh::lean_apply_4(
                v_h__2_2071_,
                v_x_2067_,
                v_x_2068_,
                v_x_2069_,
                crate::leanh::lean_box(0),
            );
            return v___x_2077_;
        }
    } else {
        let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2070_);
        v___x_2078_ = crate::leanh::lean_apply_4(
            v_h__2_2071_,
            v_x_2067_,
            v_x_2068_,
            v_x_2069_,
            crate::leanh::lean_box(0),
        );
        return v___x_2078_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(
    mut v_00_u03b1_2079_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2080_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_2081_: *mut crate::leanh::LeanObject,
    mut v_motive_2082_: *mut crate::leanh::LeanObject,
    mut v_x_2083_: *mut crate::leanh::LeanObject,
    mut v_x_2084_: *mut crate::leanh::LeanObject,
    mut v_x_2085_: *mut crate::leanh::LeanObject,
    mut v_h__1_2086_: *mut crate::leanh::LeanObject,
    mut v_h__2_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2083_) == 1 {
        if crate::leanh::lean_obj_tag(v_x_2084_) == 1 {
            let mut v_head_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_2087_);
            v_head_2088_ = crate::leanh::lean_ctor_get(v_x_2083_, 0);
            crate::leanh::lean_inc(v_head_2088_);
            v_tail_2089_ = crate::leanh::lean_ctor_get(v_x_2083_, 1);
            crate::leanh::lean_inc(v_tail_2089_);
            crate::leanh::lean_dec_ref_known(v_x_2083_, 2);
            v_head_2090_ = crate::leanh::lean_ctor_get(v_x_2084_, 0);
            crate::leanh::lean_inc(v_head_2090_);
            v_tail_2091_ = crate::leanh::lean_ctor_get(v_x_2084_, 1);
            crate::leanh::lean_inc(v_tail_2091_);
            crate::leanh::lean_dec_ref_known(v_x_2084_, 2);
            v___x_2092_ = crate::leanh::lean_apply_5(
                v_h__1_2086_,
                v_head_2088_,
                v_tail_2089_,
                v_head_2090_,
                v_tail_2091_,
                v_x_2085_,
            );
            return v___x_2092_;
        } else {
            let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_2086_);
            v___x_2093_ = crate::leanh::lean_apply_4(
                v_h__2_2087_,
                v_x_2083_,
                v_x_2084_,
                v_x_2085_,
                crate::leanh::lean_box(0),
            );
            return v___x_2093_;
        }
    } else {
        let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2086_);
        v___x_2094_ = crate::leanh::lean_apply_4(
            v_h__2_2087_,
            v_x_2083_,
            v_x_2084_,
            v_x_2085_,
            crate::leanh::lean_box(0),
        );
        return v___x_2094_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(
    mut v_as_2095_: *mut crate::leanh::LeanObject,
    mut v_i_2096_: usize,
    mut v_stop_2097_: usize,
    mut v_b_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2099_: u8 = 0;
    let mut v_fst_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2099_ = lean_usize_dec_eq(v_i_2096_, v_stop_2097_);
                if v___x_2099_ == 0 {
                    v_fst_2100_ = crate::leanh::lean_ctor_get(v_b_2098_, 0);
                    v_snd_2101_ = crate::leanh::lean_ctor_get(v_b_2098_, 1);
                    v_isSharedCheck_2116_ = (!crate::leanh::lean_is_exclusive(v_b_2098_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2103_ = v_b_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2101_);
                        crate::leanh::lean_inc(v_fst_2100_);
                        crate::leanh::lean_dec(v_b_2098_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2098_;
                }
            }
            1 => {
                v___x_2105_ = 1usize;
                v___x_2106_ = lean_usize_sub(v_i_2096_, v___x_2105_);
                v___x_2107_ = lean_array_uget_borrowed(v_as_2095_, v___x_2106_);
                v___x_2108_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_sub(v_fst_2100_, v___x_2108_);
                crate::leanh::lean_dec(v_fst_2100_);
                crate::leanh::lean_inc(v___x_2109_);
                crate::leanh::lean_inc(v___x_2107_);
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2103_, 1, v___x_2109_);
                    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2107_);
                    v___x_2111_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2112_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2112_, 0, v___x_2111_);
                crate::leanh::lean_ctor_set(v___x_2112_, 1, v_snd_2101_);
                v___x_2113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2109_);
                crate::leanh::lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                v_i_2096_ = v___x_2106_;
                v_b_2098_ = v___x_2113_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(
    mut v_as_2117_: *mut crate::leanh::LeanObject,
    mut v_i_2118_: *mut crate::leanh::LeanObject,
    mut v_stop_2119_: *mut crate::leanh::LeanObject,
    mut v_b_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2121_: usize = 0;
    let mut v_stop_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2121_ = crate::leanh::lean_unbox_usize(v_i_2118_);
    crate::leanh::lean_dec(v_i_2118_);
    v_stop_boxed_2122_ = crate::leanh::lean_unbox_usize(v_stop_2119_);
    crate::leanh::lean_dec(v_stop_2119_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2117_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2120_);
    crate::leanh::lean_dec_ref(v_as_2117_);
    return v_res_2123_;
}
pub unsafe fn l_List_zipIdxTR___redArg(
    mut v_l_2124_: *mut crate::leanh::LeanObject,
    mut v_n_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_as_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    v_as_2126_ = lean_array_mk(v_l_2124_);
    v___x_2127_ = lean_array_get_size(v_as_2126_);
    v___x_2128_ = crate::leanh::lean_box(0);
    v___x_2129_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2130_ = lean_nat_dec_lt(v___x_2129_, v___x_2127_);
    if v___x_2130_ == 0 {
        crate::leanh::lean_dec_ref(v_as_2126_);
        return v___x_2128_;
    } else {
        let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: usize = 0;
        let mut v___x_2134_: usize = 0;
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2131_ = lean_nat_add(v_n_2125_, v___x_2127_);
        v___x_2132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
        crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2128_);
        v___x_2133_ = lean_usize_of_nat(v___x_2127_);
        v___x_2134_ = 0usize;
        v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2126_, v___x_2133_, v___x_2134_, v___x_2132_);
        crate::leanh::lean_dec_ref(v_as_2126_);
        v_snd_2136_ = crate::leanh::lean_ctor_get(v___x_2135_, 1);
        crate::leanh::lean_inc(v_snd_2136_);
        crate::leanh::lean_dec_ref(v___x_2135_);
        return v_snd_2136_;
    }
}
pub unsafe fn l_List_zipIdxTR___redArg___boxed(
    mut v_l_2137_: *mut crate::leanh::LeanObject,
    mut v_n_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_List_zipIdxTR___redArg(v_l_2137_, v_n_2138_);
    crate::leanh::lean_dec(v_n_2138_);
    return v_res_2139_;
}
pub unsafe fn l_List_zipIdxTR(
    mut v_00_u03b1_2140_: *mut crate::leanh::LeanObject,
    mut v_l_2141_: *mut crate::leanh::LeanObject,
    mut v_n_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_List_zipIdxTR___redArg(v_l_2141_, v_n_2142_);
    return v___x_2143_;
}
pub unsafe fn l_List_zipIdxTR___boxed(
    mut v_00_u03b1_2144_: *mut crate::leanh::LeanObject,
    mut v_l_2145_: *mut crate::leanh::LeanObject,
    mut v_n_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_List_zipIdxTR(v_00_u03b1_2144_, v_l_2145_, v_n_2146_);
    crate::leanh::lean_dec(v_n_2146_);
    return v_res_2147_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
    mut v_00_u03b1_2148_: *mut crate::leanh::LeanObject,
    mut v_as_2149_: *mut crate::leanh::LeanObject,
    mut v_i_2150_: usize,
    mut v_stop_2151_: usize,
    mut v_b_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2149_, v_i_2150_, v_stop_2151_, v_b_2152_);
    return v___x_2153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(
    mut v_00_u03b1_2154_: *mut crate::leanh::LeanObject,
    mut v_as_2155_: *mut crate::leanh::LeanObject,
    mut v_i_2156_: *mut crate::leanh::LeanObject,
    mut v_stop_2157_: *mut crate::leanh::LeanObject,
    mut v_b_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2159_: usize = 0;
    let mut v_stop_boxed_2160_: usize = 0;
    let mut v_res_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2159_ = crate::leanh::lean_unbox_usize(v_i_2156_);
    crate::leanh::lean_dec(v_i_2156_);
    v_stop_boxed_2160_ = crate::leanh::lean_unbox_usize(v_stop_2157_);
    crate::leanh::lean_dec(v_stop_2157_);
    v_res_2161_ =
        l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
            v_00_u03b1_2154_,
            v_as_2155_,
            v_i_boxed_2159_,
            v_stop_boxed_2160_,
            v_b_2158_,
        );
    crate::leanh::lean_dec_ref(v_as_2155_);
    return v_res_2161_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_2162_: *mut crate::leanh::LeanObject,
    mut v_x_2163_: *mut crate::leanh::LeanObject,
    mut v_h__1_2164_: *mut crate::leanh::LeanObject,
    mut v_h__2_2165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2162_) == 0 {
        let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2165_);
        v___x_2166_ = crate::leanh::lean_apply_1(v_h__1_2164_, v_x_2163_);
        return v___x_2166_;
    } else {
        let mut v_head_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2164_);
        v_head_2167_ = crate::leanh::lean_ctor_get(v_x_2162_, 0);
        crate::leanh::lean_inc(v_head_2167_);
        v_tail_2168_ = crate::leanh::lean_ctor_get(v_x_2162_, 1);
        crate::leanh::lean_inc(v_tail_2168_);
        crate::leanh::lean_dec_ref_known(v_x_2162_, 2);
        v___x_2169_ =
            crate::leanh::lean_apply_3(v_h__2_2165_, v_head_2167_, v_tail_2168_, v_x_2163_);
        return v___x_2169_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_2170_: *mut crate::leanh::LeanObject,
    mut v_motive_2171_: *mut crate::leanh::LeanObject,
    mut v_x_2172_: *mut crate::leanh::LeanObject,
    mut v_x_2173_: *mut crate::leanh::LeanObject,
    mut v_h__1_2174_: *mut crate::leanh::LeanObject,
    mut v_h__2_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2172_) == 0 {
        let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2175_);
        v___x_2176_ = crate::leanh::lean_apply_1(v_h__1_2174_, v_x_2173_);
        return v___x_2176_;
    } else {
        let mut v_head_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2174_);
        v_head_2177_ = crate::leanh::lean_ctor_get(v_x_2172_, 0);
        crate::leanh::lean_inc(v_head_2177_);
        v_tail_2178_ = crate::leanh::lean_ctor_get(v_x_2172_, 1);
        crate::leanh::lean_inc(v_tail_2178_);
        crate::leanh::lean_dec_ref_known(v_x_2172_, 2);
        v___x_2179_ =
            crate::leanh::lean_apply_3(v_h__2_2175_, v_head_2177_, v_tail_2178_, v_x_2173_);
        return v___x_2179_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
    mut v_sep_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2182_) == 0 {
                    v___x_2184_ = lean_array_get_size(v_a_2183_);
                    v___x_2185_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v___x_2184_);
                    if v___x_2186_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_2183_);
                        return v_a_2181_;
                    } else {
                        v___x_2187_ = lean_usize_of_nat(v___x_2184_);
                        v___x_2188_ = 0usize;
                        v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_2183_, v___x_2187_, v___x_2188_, v_a_2181_);
                        crate::leanh::lean_dec_ref(v_a_2183_);
                        return v___x_2189_;
                    }
                } else {
                    v_head_2190_ = crate::leanh::lean_ctor_get(v_a_2182_, 0);
                    crate::leanh::lean_inc(v_head_2190_);
                    v_tail_2191_ = crate::leanh::lean_ctor_get(v_a_2182_, 1);
                    crate::leanh::lean_inc(v_tail_2191_);
                    crate::leanh::lean_dec_ref_known(v_a_2182_, 2);
                    v___x_2192_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_2183_, v_a_2181_,
                    );
                    v___x_2193_ = l_Array_append___redArg(v___x_2192_, v_sep_2180_);
                    v_a_2181_ = v_head_2190_;
                    v_a_2182_ = v_tail_2191_;
                    v_a_2183_ = v___x_2193_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(
    mut v_sep_2195_: *mut crate::leanh::LeanObject,
    mut v_a_2196_: *mut crate::leanh::LeanObject,
    mut v_a_2197_: *mut crate::leanh::LeanObject,
    mut v_a_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2195_,
        v_a_2196_,
        v_a_2197_,
        v_a_2198_,
    );
    crate::leanh::lean_dec_ref(v_sep_2195_);
    return v_res_2199_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
    mut v_00_u03b1_2200_: *mut crate::leanh::LeanObject,
    mut v_sep_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
    );
    return v___x_2205_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(
    mut v_00_u03b1_2206_: *mut crate::leanh::LeanObject,
    mut v_sep_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
    mut v_a_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2211_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
        v_00_u03b1_2206_,
        v_sep_2207_,
        v_a_2208_,
        v_a_2209_,
        v_a_2210_,
    );
    crate::leanh::lean_dec_ref(v_sep_2207_);
    return v_res_2211_;
}
pub unsafe fn l_List_intercalateTR___redArg(
    mut v_sep_2212_: *mut crate::leanh::LeanObject,
    mut v_x_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2213_) == 0 {
        let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_sep_2212_);
        v___x_2214_ = crate::leanh::lean_box(0);
        return v___x_2214_;
    } else {
        let mut v_tail_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2215_ = crate::leanh::lean_ctor_get(v_x_2213_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2215_) == 0 {
            let mut v_head_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_sep_2212_);
            v_head_2216_ = crate::leanh::lean_ctor_get(v_x_2213_, 0);
            crate::leanh::lean_inc(v_head_2216_);
            crate::leanh::lean_dec_ref_known(v_x_2213_, 2);
            return v_head_2216_;
        } else {
            let mut v_head_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2215_);
            v_head_2217_ = crate::leanh::lean_ctor_get(v_x_2213_, 0);
            crate::leanh::lean_inc(v_head_2217_);
            crate::leanh::lean_dec_ref_known(v_x_2213_, 2);
            v___x_2218_ = lean_array_mk(v_sep_2212_);
            v___x_2219_ = l_List_setTR___redArg___closed__0;
            v___x_2220_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
                v___x_2218_,
                v_head_2217_,
                v_tail_2215_,
                v___x_2219_,
            );
            crate::leanh::lean_dec_ref(v___x_2218_);
            return v___x_2220_;
        }
    }
}
pub unsafe fn l_List_intercalateTR(
    mut v_00_u03b1_2221_: *mut crate::leanh::LeanObject,
    mut v_sep_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_List_intercalateTR___redArg(v_sep_2222_, v_x_2223_);
    return v___x_2224_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(
    mut v_x_2225_: *mut crate::leanh::LeanObject,
    mut v_h__1_2226_: *mut crate::leanh::LeanObject,
    mut v_h__2_2227_: *mut crate::leanh::LeanObject,
    mut v_h__3_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2225_) == 0 {
        let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2228_);
        crate::leanh::lean_dec(v_h__2_2227_);
        v___x_2229_ = crate::leanh::lean_box(0);
        v___x_2230_ = crate::leanh::lean_apply_1(v_h__1_2226_, v___x_2229_);
        return v___x_2230_;
    } else {
        let mut v_tail_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2226_);
        v_tail_2231_ = crate::leanh::lean_ctor_get(v_x_2225_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2231_) == 0 {
            let mut v_head_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2228_);
            v_head_2232_ = crate::leanh::lean_ctor_get(v_x_2225_, 0);
            crate::leanh::lean_inc(v_head_2232_);
            crate::leanh::lean_dec_ref_known(v_x_2225_, 2);
            v___x_2233_ = crate::leanh::lean_apply_1(v_h__2_2227_, v_head_2232_);
            return v___x_2233_;
        } else {
            let mut v_head_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2231_);
            crate::leanh::lean_dec(v_h__2_2227_);
            v_head_2234_ = crate::leanh::lean_ctor_get(v_x_2225_, 0);
            crate::leanh::lean_inc(v_head_2234_);
            crate::leanh::lean_dec_ref_known(v_x_2225_, 2);
            v___x_2235_ = crate::leanh::lean_apply_3(
                v_h__3_2228_,
                v_head_2234_,
                v_tail_2231_,
                crate::leanh::lean_box(0),
            );
            return v___x_2235_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(
    mut v_00_u03b1_2236_: *mut crate::leanh::LeanObject,
    mut v_motive_2237_: *mut crate::leanh::LeanObject,
    mut v_x_2238_: *mut crate::leanh::LeanObject,
    mut v_h__1_2239_: *mut crate::leanh::LeanObject,
    mut v_h__2_2240_: *mut crate::leanh::LeanObject,
    mut v_h__3_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2238_) == 0 {
        let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_2241_);
        crate::leanh::lean_dec(v_h__2_2240_);
        v___x_2242_ = crate::leanh::lean_box(0);
        v___x_2243_ = crate::leanh::lean_apply_1(v_h__1_2239_, v___x_2242_);
        return v___x_2243_;
    } else {
        let mut v_tail_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2239_);
        v_tail_2244_ = crate::leanh::lean_ctor_get(v_x_2238_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2244_) == 0 {
            let mut v_head_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_2241_);
            v_head_2245_ = crate::leanh::lean_ctor_get(v_x_2238_, 0);
            crate::leanh::lean_inc(v_head_2245_);
            crate::leanh::lean_dec_ref_known(v_x_2238_, 2);
            v___x_2246_ = crate::leanh::lean_apply_1(v_h__2_2240_, v_head_2245_);
            return v___x_2246_;
        } else {
            let mut v_head_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2244_);
            crate::leanh::lean_dec(v_h__2_2240_);
            v_head_2247_ = crate::leanh::lean_ctor_get(v_x_2238_, 0);
            crate::leanh::lean_inc(v_head_2247_);
            crate::leanh::lean_dec_ref_known(v_x_2238_, 2);
            v___x_2248_ = crate::leanh::lean_apply_3(
                v_h__3_2241_,
                v_head_2247_,
                v_tail_2244_,
                crate::leanh::lean_box(0),
            );
            return v___x_2248_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(
    mut v_x_2249_: *mut crate::leanh::LeanObject,
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: *mut crate::leanh::LeanObject,
    mut v_h__1_2252_: *mut crate::leanh::LeanObject,
    mut v_h__2_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2250_) == 0 {
        let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2253_);
        v___x_2254_ = crate::leanh::lean_apply_2(v_h__1_2252_, v_x_2249_, v_x_2251_);
        return v___x_2254_;
    } else {
        let mut v_head_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2252_);
        v_head_2255_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
        crate::leanh::lean_inc(v_head_2255_);
        v_tail_2256_ = crate::leanh::lean_ctor_get(v_x_2250_, 1);
        crate::leanh::lean_inc(v_tail_2256_);
        crate::leanh::lean_dec_ref_known(v_x_2250_, 2);
        v___x_2257_ = crate::leanh::lean_apply_4(
            v_h__2_2253_,
            v_x_2249_,
            v_head_2255_,
            v_tail_2256_,
            v_x_2251_,
        );
        return v___x_2257_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(
    mut v_00_u03b1_2258_: *mut crate::leanh::LeanObject,
    mut v_motive_2259_: *mut crate::leanh::LeanObject,
    mut v_x_2260_: *mut crate::leanh::LeanObject,
    mut v_x_2261_: *mut crate::leanh::LeanObject,
    mut v_x_2262_: *mut crate::leanh::LeanObject,
    mut v_h__1_2263_: *mut crate::leanh::LeanObject,
    mut v_h__2_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2261_) == 0 {
        let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2264_);
        v___x_2265_ = crate::leanh::lean_apply_2(v_h__1_2263_, v_x_2260_, v_x_2262_);
        return v___x_2265_;
    } else {
        let mut v_head_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2263_);
        v_head_2266_ = crate::leanh::lean_ctor_get(v_x_2261_, 0);
        crate::leanh::lean_inc(v_head_2266_);
        v_tail_2267_ = crate::leanh::lean_ctor_get(v_x_2261_, 1);
        crate::leanh::lean_inc(v_tail_2267_);
        crate::leanh::lean_dec_ref_known(v_x_2261_, 2);
        v___x_2268_ = crate::leanh::lean_apply_4(
            v_h__2_2264_,
            v_x_2260_,
            v_head_2266_,
            v_tail_2267_,
            v_x_2262_,
        );
        return v___x_2268_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Impl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Impl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Impl(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Impl(builtin);
}
