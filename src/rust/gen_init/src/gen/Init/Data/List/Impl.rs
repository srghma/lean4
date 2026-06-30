// Lean compiler output
// Module: Init.Data.List.Impl
// Imports: Init.Ext Init.Data.Array.Bootstrap Init.Data.Bool Init.Data.List.Lemmas Init.Data.Option.Lemmas
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_pop, lean_array_push, lean_array_to_list,
    lean_array_uget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_usize_dec_eq, lean_usize_of_nat, lean_usize_sub,
};
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
pub static l_List_setTR___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_List_setTR___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_setTR___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_reduceOption___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_List_reduceOption___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_reduceOption___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
static mut l_List_foldrTR___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__8_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_List_foldrTR___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_foldrTR___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_List_flattenTR___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_List_flattenTR___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_flattenTR___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value:
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
    m_fun: l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(
    mut v_as_1135_: *mut leanh::LeanObject,
    mut v_i_1136_: usize,
    mut v_stop_1137_: usize,
    mut v_b_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
                if v___x_1139_ == 0 {
                    v___x_1140_ = 1usize;
                    v___x_1141_ = lean_usize_sub(v_i_1136_, v___x_1140_);
                    v___x_1142_ = lean_array_uget_borrowed(v_as_1135_, v___x_1141_);
                    leanh::lean_inc(v___x_1142_);
                    v___x_1143_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    leanh::lean_ctor_set(v___x_1143_, 1, v_b_1138_);
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
    mut v_as_1145_: *mut leanh::LeanObject,
    mut v_i_1146_: *mut leanh::LeanObject,
    mut v_stop_1147_: *mut leanh::LeanObject,
    mut v_b_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1149_: usize = 0;
    let mut v_stop_boxed_1150_: usize = 0;
    let mut v_res_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1149_ = leanh::lean_unbox_usize(v_i_1146_);
    leanh::lean_dec(v_i_1146_);
    v_stop_boxed_1150_ = leanh::lean_unbox_usize(v_stop_1147_);
    leanh::lean_dec(v_stop_1147_);
    v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1145_, v_i_boxed_1149_, v_stop_boxed_1150_, v_b_1148_);
    leanh::lean_dec_ref(v_as_1145_);
    return v_res_1151_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
    mut v_l_1152_: *mut leanh::LeanObject,
    mut v_a_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_zero_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1163_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1154_) == 0 {
                    leanh::lean_dec_ref(v_a_1156_);
                    leanh::lean_dec(v_a_1155_);
                    leanh::lean_dec(v_a_1153_);
                    leanh::lean_inc(v_l_1152_);
                    return v_l_1152_;
                } else {
                    v_head_1157_ = leanh::lean_ctor_get(v_a_1154_, 0);
                    v_tail_1158_ = leanh::lean_ctor_get(v_a_1154_, 1);
                    v_isSharedCheck_1176_ = (!leanh::lean_is_exclusive(v_a_1154_)) as u8;
                    if v_isSharedCheck_1176_ == 0 {
                        v___x_1160_ = v_a_1154_;
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1158_);
                        leanh::lean_inc(v_head_1157_);
                        leanh::lean_dec(v_a_1154_);
                        v___x_1160_ = leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1162_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1163_ = lean_nat_dec_eq(v_a_1155_, v_zero_1162_);
                if v_isZero_1163_ == 1 {
                    leanh::lean_dec(v_head_1157_);
                    leanh::lean_dec(v_a_1155_);
                    if v_isShared_1161_ == 0 {
                        leanh::lean_ctor_set(v___x_1160_, 0, v_a_1153_);
                        v___x_1165_ = v___x_1160_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1171_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1153_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_tail_1158_);
                        v___x_1165_ = v_reuseFailAlloc_1171_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1160_);
                    v_one_1172_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1173_ = lean_nat_sub(v_a_1155_, v_one_1172_);
                    leanh::lean_dec(v_a_1155_);
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
                    leanh::lean_dec_ref(v_a_1156_);
                    return v___x_1165_;
                } else {
                    v___x_1168_ = lean_usize_of_nat(v___x_1166_);
                    v___x_1169_ = 0usize;
                    v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1156_, v___x_1168_, v___x_1169_, v___x_1165_);
                    leanh::lean_dec_ref(v_a_1156_);
                    return v___x_1170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(
    mut v_l_1177_: *mut leanh::LeanObject,
    mut v_a_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v_a_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_,
    );
    leanh::lean_dec(v_l_1177_);
    return v_res_1182_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go(
    mut v_00_u03b1_1183_: *mut leanh::LeanObject,
    mut v_l_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_a_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_,
    );
    return v___x_1189_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(
    mut v_00_u03b1_1190_: *mut leanh::LeanObject,
    mut v_l_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Init_Data_List_Impl_0__List_setTR_go(
        v_00_u03b1_1190_,
        v_l_1191_,
        v_a_1192_,
        v_a_1193_,
        v_a_1194_,
        v_a_1195_,
    );
    leanh::lean_dec(v_l_1191_);
    return v_res_1196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(
    mut v_00_u03b1_1197_: *mut leanh::LeanObject,
    mut v_as_1198_: *mut leanh::LeanObject,
    mut v_i_1199_: usize,
    mut v_stop_1200_: usize,
    mut v_b_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1198_, v_i_1199_, v_stop_1200_, v_b_1201_);
    return v___x_1202_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(
    mut v_00_u03b1_1203_: *mut leanh::LeanObject,
    mut v_as_1204_: *mut leanh::LeanObject,
    mut v_i_1205_: *mut leanh::LeanObject,
    mut v_stop_1206_: *mut leanh::LeanObject,
    mut v_b_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1208_: usize = 0;
    let mut v_stop_boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1208_ = leanh::lean_unbox_usize(v_i_1205_);
    leanh::lean_dec(v_i_1205_);
    v_stop_boxed_1209_ = leanh::lean_unbox_usize(v_stop_1206_);
    leanh::lean_dec(v_stop_1206_);
    v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(v_00_u03b1_1203_, v_as_1204_, v_i_boxed_1208_, v_stop_boxed_1209_, v_b_1207_);
    leanh::lean_dec_ref(v_as_1204_);
    return v_res_1210_;
}
pub unsafe fn l_List_setTR___redArg(
    mut v_l_1213_: *mut leanh::LeanObject,
    mut v_n_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1213_);
    v___x_1217_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1213_,
        v_a_1215_,
        v_l_1213_,
        v_n_1214_,
        v___x_1216_,
    );
    leanh::lean_dec(v_l_1213_);
    return v___x_1217_;
}
pub unsafe fn l_List_setTR(
    mut v_00_u03b1_1218_: *mut leanh::LeanObject,
    mut v_l_1219_: *mut leanh::LeanObject,
    mut v_n_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1219_);
    v___x_1223_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1219_,
        v_a_1221_,
        v_l_1219_,
        v_n_1220_,
        v___x_1222_,
    );
    leanh::lean_dec(v_l_1219_);
    return v___x_1223_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(
    mut v_x_1224_: *mut leanh::LeanObject,
    mut v_x_1225_: *mut leanh::LeanObject,
    mut v_x_1226_: *mut leanh::LeanObject,
    mut v_h__1_1227_: *mut leanh::LeanObject,
    mut v_h__2_1228_: *mut leanh::LeanObject,
    mut v_h__3_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1224_) == 0 {
        let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1229_);
        leanh::lean_dec(v_h__2_1228_);
        v___x_1230_ = leanh::lean_apply_2(v_h__1_1227_, v_x_1225_, v_x_1226_);
        return v___x_1230_;
    } else {
        let mut v_head_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1234_: u8 = 0;
        leanh::lean_dec(v_h__1_1227_);
        v_head_1231_ = leanh::lean_ctor_get(v_x_1224_, 0);
        leanh::lean_inc(v_head_1231_);
        v_tail_1232_ = leanh::lean_ctor_get(v_x_1224_, 1);
        leanh::lean_inc(v_tail_1232_);
        leanh::lean_dec_ref_known(v_x_1224_, 2);
        v_zero_1233_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_1234_ = lean_nat_dec_eq(v_x_1225_, v_zero_1233_);
        if v_isZero_1234_ == 1 {
            let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1229_);
            leanh::lean_dec(v_x_1225_);
            v___x_1235_ =
                leanh::lean_apply_3(v_h__2_1228_, v_head_1231_, v_tail_1232_, v_x_1226_);
            return v___x_1235_;
        } else {
            let mut v_one_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1228_);
            v_one_1236_ = leanh::lean_unsigned_to_nat(1);
            v_n_1237_ = lean_nat_sub(v_x_1225_, v_one_1236_);
            leanh::lean_dec(v_x_1225_);
            v___x_1238_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_1239_: *mut leanh::LeanObject,
    mut v_motive_1240_: *mut leanh::LeanObject,
    mut v_x_1241_: *mut leanh::LeanObject,
    mut v_x_1242_: *mut leanh::LeanObject,
    mut v_x_1243_: *mut leanh::LeanObject,
    mut v_h__1_1244_: *mut leanh::LeanObject,
    mut v_h__2_1245_: *mut leanh::LeanObject,
    mut v_h__3_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1241_) == 0 {
        let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1246_);
        leanh::lean_dec(v_h__2_1245_);
        v___x_1247_ = leanh::lean_apply_2(v_h__1_1244_, v_x_1242_, v_x_1243_);
        return v___x_1247_;
    } else {
        let mut v_head_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1251_: u8 = 0;
        leanh::lean_dec(v_h__1_1244_);
        v_head_1248_ = leanh::lean_ctor_get(v_x_1241_, 0);
        leanh::lean_inc(v_head_1248_);
        v_tail_1249_ = leanh::lean_ctor_get(v_x_1241_, 1);
        leanh::lean_inc(v_tail_1249_);
        leanh::lean_dec_ref_known(v_x_1241_, 2);
        v_zero_1250_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_1251_ = lean_nat_dec_eq(v_x_1242_, v_zero_1250_);
        if v_isZero_1251_ == 1 {
            let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1246_);
            leanh::lean_dec(v_x_1242_);
            v___x_1252_ =
                leanh::lean_apply_3(v_h__2_1245_, v_head_1248_, v_tail_1249_, v_x_1243_);
            return v___x_1252_;
        } else {
            let mut v_one_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1245_);
            v_one_1253_ = leanh::lean_unsigned_to_nat(1);
            v_n_1254_ = lean_nat_sub(v_x_1242_, v_one_1253_);
            leanh::lean_dec(v_x_1242_);
            v___x_1255_ = leanh::lean_apply_4(
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
    mut v_f_1256_: *mut leanh::LeanObject,
    mut v_a_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1257_) == 0 {
                    leanh::lean_dec_ref(v_f_1256_);
                    v___x_1259_ = lean_array_to_list(v_a_1258_);
                    return v___x_1259_;
                } else {
                    v_head_1260_ = leanh::lean_ctor_get(v_a_1257_, 0);
                    leanh::lean_inc(v_head_1260_);
                    v_tail_1261_ = leanh::lean_ctor_get(v_a_1257_, 1);
                    leanh::lean_inc(v_tail_1261_);
                    leanh::lean_dec_ref_known(v_a_1257_, 2);
                    leanh::lean_inc_ref(v_f_1256_);
                    v___x_1262_ = leanh::lean_apply_1(v_f_1256_, v_head_1260_);
                    if leanh::lean_obj_tag(v___x_1262_) == 0 {
                        v_a_1257_ = v_tail_1261_;
                        state = 0;
                        continue;
                    } else {
                        v_val_1264_ = leanh::lean_ctor_get(v___x_1262_, 0);
                        leanh::lean_inc(v_val_1264_);
                        leanh::lean_dec_ref_known(v___x_1262_, 1);
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
    mut v_00_u03b1_1267_: *mut leanh::LeanObject,
    mut v_00_u03b2_1268_: *mut leanh::LeanObject,
    mut v_f_1269_: *mut leanh::LeanObject,
    mut v_a_1270_: *mut leanh::LeanObject,
    mut v_a_1271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_List_filterMapTR_go___redArg(v_f_1269_, v_a_1270_, v_a_1271_);
    return v___x_1272_;
}
pub unsafe fn l_List_filterMapTR___redArg(
    mut v_f_1273_: *mut leanh::LeanObject,
    mut v_l_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_List_setTR___redArg___closed__0;
    v___x_1276_ = l_List_filterMapTR_go___redArg(v_f_1273_, v_l_1274_, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_List_filterMapTR(
    mut v_00_u03b1_1277_: *mut leanh::LeanObject,
    mut v_00_u03b2_1278_: *mut leanh::LeanObject,
    mut v_f_1279_: *mut leanh::LeanObject,
    mut v_l_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_List_setTR___redArg___closed__0;
    v___x_1282_ = l_List_filterMapTR_go___redArg(v_f_1279_, v_l_1280_, v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(
    mut v_x_1283_: *mut leanh::LeanObject,
    mut v_x_1284_: *mut leanh::LeanObject,
    mut v_h__1_1285_: *mut leanh::LeanObject,
    mut v_h__2_1286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1283_) == 0 {
        let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1286_);
        v___x_1287_ = leanh::lean_apply_1(v_h__1_1285_, v_x_1284_);
        return v___x_1287_;
    } else {
        let mut v_head_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1285_);
        v_head_1288_ = leanh::lean_ctor_get(v_x_1283_, 0);
        leanh::lean_inc(v_head_1288_);
        v_tail_1289_ = leanh::lean_ctor_get(v_x_1283_, 1);
        leanh::lean_inc(v_tail_1289_);
        leanh::lean_dec_ref_known(v_x_1283_, 2);
        v___x_1290_ =
            leanh::lean_apply_3(v_h__2_1286_, v_head_1288_, v_tail_1289_, v_x_1284_);
        return v___x_1290_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(
    mut v_00_u03b1_1291_: *mut leanh::LeanObject,
    mut v_00_u03b2_1292_: *mut leanh::LeanObject,
    mut v_motive_1293_: *mut leanh::LeanObject,
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_x_1295_: *mut leanh::LeanObject,
    mut v_h__1_1296_: *mut leanh::LeanObject,
    mut v_h__2_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1294_) == 0 {
        let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1297_);
        v___x_1298_ = leanh::lean_apply_1(v_h__1_1296_, v_x_1295_);
        return v___x_1298_;
    } else {
        let mut v_head_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1296_);
        v_head_1299_ = leanh::lean_ctor_get(v_x_1294_, 0);
        leanh::lean_inc(v_head_1299_);
        v_tail_1300_ = leanh::lean_ctor_get(v_x_1294_, 1);
        leanh::lean_inc(v_tail_1300_);
        leanh::lean_dec_ref_known(v_x_1294_, 2);
        v___x_1301_ =
            leanh::lean_apply_3(v_h__2_1297_, v_head_1299_, v_tail_1300_, v_x_1295_);
        return v___x_1301_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(
    mut v_x_1302_: *mut leanh::LeanObject,
    mut v_h__1_1303_: *mut leanh::LeanObject,
    mut v_h__2_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1302_) == 0 {
        let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1304_);
        v___x_1305_ = leanh::lean_box(0);
        v___x_1306_ = leanh::lean_apply_1(v_h__1_1303_, v___x_1305_);
        return v___x_1306_;
    } else {
        let mut v_val_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1303_);
        v_val_1307_ = leanh::lean_ctor_get(v_x_1302_, 0);
        leanh::lean_inc(v_val_1307_);
        leanh::lean_dec_ref_known(v_x_1302_, 1);
        v___x_1308_ = leanh::lean_apply_1(v_h__2_1304_, v_val_1307_);
        return v___x_1308_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(
    mut v_00_u03b2_1309_: *mut leanh::LeanObject,
    mut v_motive_1310_: *mut leanh::LeanObject,
    mut v_x_1311_: *mut leanh::LeanObject,
    mut v_h__1_1312_: *mut leanh::LeanObject,
    mut v_h__2_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1311_) == 0 {
        let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1313_);
        v___x_1314_ = leanh::lean_box(0);
        v___x_1315_ = leanh::lean_apply_1(v_h__1_1312_, v___x_1314_);
        return v___x_1315_;
    } else {
        let mut v_val_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1312_);
        v_val_1316_ = leanh::lean_ctor_get(v_x_1311_, 0);
        leanh::lean_inc(v_val_1316_);
        leanh::lean_dec_ref_known(v_x_1311_, 1);
        v___x_1317_ = leanh::lean_apply_1(v_h__2_1313_, v_val_1316_);
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_1318_: *mut leanh::LeanObject,
    mut v_h__1_1319_: *mut leanh::LeanObject,
    mut v_h__2_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1318_) == 0 {
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1320_);
        v___x_1321_ = leanh::lean_box(0);
        v___x_1322_ = leanh::lean_apply_1(v_h__1_1319_, v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v_val_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1319_);
        v_val_1323_ = leanh::lean_ctor_get(v_x_1318_, 0);
        leanh::lean_inc(v_val_1323_);
        leanh::lean_dec_ref_known(v_x_1318_, 1);
        v___x_1324_ = leanh::lean_apply_1(v_h__2_1320_, v_val_1323_);
        return v___x_1324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_1325_: *mut leanh::LeanObject,
    mut v_motive_1326_: *mut leanh::LeanObject,
    mut v_x_1327_: *mut leanh::LeanObject,
    mut v_h__1_1328_: *mut leanh::LeanObject,
    mut v_h__2_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1327_) == 0 {
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1329_);
        v___x_1330_ = leanh::lean_box(0);
        v___x_1331_ = leanh::lean_apply_1(v_h__1_1328_, v___x_1330_);
        return v___x_1331_;
    } else {
        let mut v_val_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1328_);
        v_val_1332_ = leanh::lean_ctor_get(v_x_1327_, 0);
        leanh::lean_inc(v_val_1332_);
        leanh::lean_dec_ref_known(v_x_1327_, 1);
        v___x_1333_ = leanh::lean_apply_1(v_h__2_1329_, v_val_1332_);
        return v___x_1333_;
    }
}
pub unsafe fn l_List_reduceOption___redArg(
    mut v_a_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_List_reduceOption___redArg___closed__0;
    v___x_1337_ = l_List_setTR___redArg___closed__0;
    v___x_1338_ = l_List_filterMapTR_go___redArg(v___x_1336_, v_a_1335_, v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_List_reduceOption(
    mut v_00_u03b1_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = l_List_reduceOption___redArg___closed__0;
    v___x_1342_ = l_List_setTR___redArg___closed__0;
    v___x_1343_ = l_List_filterMapTR_go___redArg(v___x_1341_, v_a_1340_, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_List_foldrTR___redArg___lam__0(
    mut v_f_1344_: *mut leanh::LeanObject,
    mut v_x1_1345_: *mut leanh::LeanObject,
    mut v_x2_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = leanh::lean_apply_2(v_f_1344_, v_x1_1345_, v_x2_1346_);
    return v___x_1347_;
}
pub unsafe fn l_List_foldrTR___redArg(
    mut v_f_1367_: *mut leanh::LeanObject,
    mut v_init_1368_: *mut leanh::LeanObject,
    mut v_l_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    v___x_1370_ = lean_array_mk(v_l_1369_);
    v___x_1371_ = lean_array_get_size(v___x_1370_);
    v___x_1372_ = leanh::lean_unsigned_to_nat(0);
    v___x_1373_ = l_List_foldrTR___redArg___closed__9;
    v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1371_);
    if v___x_1374_ == 0 {
        leanh::lean_dec_ref(v___x_1370_);
        leanh::lean_dec(v_f_1367_);
        return v_init_1368_;
    } else {
        let mut v___f_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: usize = 0;
        let mut v___x_1377_: usize = 0;
        let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1375_ = leanh::lean_alloc_closure(
            l_List_foldrTR___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1375_, 0, v_f_1367_);
        v___x_1376_ = lean_usize_of_nat(v___x_1371_);
        v___x_1377_ = 0usize;
        v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
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
    mut v_00_u03b1_1379_: *mut leanh::LeanObject,
    mut v_00_u03b2_1380_: *mut leanh::LeanObject,
    mut v_f_1381_: *mut leanh::LeanObject,
    mut v_init_1382_: *mut leanh::LeanObject,
    mut v_l_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_List_foldrTR___redArg(v_f_1381_, v_init_1382_, v_l_1383_);
    return v___x_1384_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
    mut v_f_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
    mut v_a_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1386_) == 0 {
                    leanh::lean_dec_ref(v_f_1385_);
                    v___x_1388_ = lean_array_to_list(v_a_1387_);
                    return v___x_1388_;
                } else {
                    v_head_1389_ = leanh::lean_ctor_get(v_a_1386_, 0);
                    leanh::lean_inc(v_head_1389_);
                    v_tail_1390_ = leanh::lean_ctor_get(v_a_1386_, 1);
                    leanh::lean_inc(v_tail_1390_);
                    leanh::lean_dec_ref_known(v_a_1386_, 2);
                    leanh::lean_inc_ref(v_f_1385_);
                    v___x_1391_ = leanh::lean_apply_1(v_f_1385_, v_head_1389_);
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
    mut v_00_u03b1_1394_: *mut leanh::LeanObject,
    mut v_00_u03b2_1395_: *mut leanh::LeanObject,
    mut v_f_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1396_, v_a_1397_, v_a_1398_,
    );
    return v___x_1399_;
}
pub unsafe fn l_List_flatMapTR___redArg(
    mut v_f_1400_: *mut leanh::LeanObject,
    mut v_as_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_List_setTR___redArg___closed__0;
    v___x_1403_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1400_,
        v_as_1401_,
        v___x_1402_,
    );
    return v___x_1403_;
}
pub unsafe fn l_List_flatMapTR(
    mut v_00_u03b1_1404_: *mut leanh::LeanObject,
    mut v_00_u03b2_1405_: *mut leanh::LeanObject,
    mut v_f_1406_: *mut leanh::LeanObject,
    mut v_as_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = l_List_setTR___redArg___closed__0;
    v___x_1409_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1406_,
        v_as_1407_,
        v___x_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_List_flattenTR___redArg(
    mut v_l_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1415_: *mut leanh::LeanObject,
    mut v_l_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_l_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1427_: u8 = 0;
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1421_) == 0 {
                    leanh::lean_dec_ref(v_a_1423_);
                    leanh::lean_dec(v_a_1422_);
                    leanh::lean_inc(v_l_1420_);
                    return v_l_1420_;
                } else {
                    v_head_1424_ = leanh::lean_ctor_get(v_a_1421_, 0);
                    leanh::lean_inc(v_head_1424_);
                    v_tail_1425_ = leanh::lean_ctor_get(v_a_1421_, 1);
                    leanh::lean_inc(v_tail_1425_);
                    leanh::lean_dec_ref_known(v_a_1421_, 2);
                    v_zero_1426_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_1427_ = lean_nat_dec_eq(v_a_1422_, v_zero_1426_);
                    if v_isZero_1427_ == 1 {
                        leanh::lean_dec(v_tail_1425_);
                        leanh::lean_dec(v_head_1424_);
                        leanh::lean_dec(v_a_1422_);
                        v___x_1428_ = lean_array_to_list(v_a_1423_);
                        return v___x_1428_;
                    } else {
                        v_one_1429_ = leanh::lean_unsigned_to_nat(1);
                        v_n_1430_ = lean_nat_sub(v_a_1422_, v_one_1429_);
                        leanh::lean_dec(v_a_1422_);
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
    mut v_l_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
    mut v_a_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1433_, v_a_1434_, v_a_1435_, v_a_1436_,
    );
    leanh::lean_dec(v_l_1433_);
    return v_res_1437_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go(
    mut v_00_u03b1_1438_: *mut leanh::LeanObject,
    mut v_l_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
    mut v_a_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1439_, v_a_1440_, v_a_1441_, v_a_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(
    mut v_00_u03b1_1444_: *mut leanh::LeanObject,
    mut v_l_1445_: *mut leanh::LeanObject,
    mut v_a_1446_: *mut leanh::LeanObject,
    mut v_a_1447_: *mut leanh::LeanObject,
    mut v_a_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        v_00_u03b1_1444_,
        v_l_1445_,
        v_a_1446_,
        v_a_1447_,
        v_a_1448_,
    );
    leanh::lean_dec(v_l_1445_);
    return v_res_1449_;
}
pub unsafe fn l_List_takeTR___redArg(
    mut v_n_1450_: *mut leanh::LeanObject,
    mut v_l_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1451_);
    v___x_1453_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1451_,
        v_l_1451_,
        v_n_1450_,
        v___x_1452_,
    );
    leanh::lean_dec(v_l_1451_);
    return v___x_1453_;
}
pub unsafe fn l_List_takeTR(
    mut v_00_u03b1_1454_: *mut leanh::LeanObject,
    mut v_n_1455_: *mut leanh::LeanObject,
    mut v_l_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1456_);
    v___x_1458_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1456_,
        v_l_1456_,
        v_n_1455_,
        v___x_1457_,
    );
    leanh::lean_dec(v_l_1456_);
    return v___x_1458_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
    mut v_x_1459_: *mut leanh::LeanObject,
    mut v_x_1460_: *mut leanh::LeanObject,
    mut v_h__1_1461_: *mut leanh::LeanObject,
    mut v_h__2_1462_: *mut leanh::LeanObject,
    mut v_h__3_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1465_: u8 = 0;
    v_zero_1464_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1465_ = lean_nat_dec_eq(v_x_1459_, v_zero_1464_);
    if v_isZero_1465_ == 1 {
        let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1463_);
        leanh::lean_dec(v_h__2_1462_);
        v___x_1466_ = leanh::lean_apply_1(v_h__1_1461_, v_x_1460_);
        return v___x_1466_;
    } else {
        let mut v_one_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1461_);
        v_one_1467_ = leanh::lean_unsigned_to_nat(1);
        v_n_1468_ = lean_nat_sub(v_x_1459_, v_one_1467_);
        if leanh::lean_obj_tag(v_x_1460_) == 0 {
            let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1463_);
            v___x_1469_ = leanh::lean_apply_1(v_h__2_1462_, v_n_1468_);
            return v___x_1469_;
        } else {
            let mut v_head_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1462_);
            v_head_1470_ = leanh::lean_ctor_get(v_x_1460_, 0);
            leanh::lean_inc(v_head_1470_);
            v_tail_1471_ = leanh::lean_ctor_get(v_x_1460_, 1);
            leanh::lean_inc(v_tail_1471_);
            leanh::lean_dec_ref_known(v_x_1460_, 2);
            v___x_1472_ =
                leanh::lean_apply_3(v_h__3_1463_, v_n_1468_, v_head_1470_, v_tail_1471_);
            return v___x_1472_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_1473_: *mut leanh::LeanObject,
    mut v_x_1474_: *mut leanh::LeanObject,
    mut v_h__1_1475_: *mut leanh::LeanObject,
    mut v_h__2_1476_: *mut leanh::LeanObject,
    mut v_h__3_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
        v_x_1473_,
        v_x_1474_,
        v_h__1_1475_,
        v_h__2_1476_,
        v_h__3_1477_,
    );
    leanh::lean_dec(v_x_1473_);
    return v_res_1478_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
    mut v_00_u03b1_1479_: *mut leanh::LeanObject,
    mut v_motive_1480_: *mut leanh::LeanObject,
    mut v_x_1481_: *mut leanh::LeanObject,
    mut v_x_1482_: *mut leanh::LeanObject,
    mut v_h__1_1483_: *mut leanh::LeanObject,
    mut v_h__2_1484_: *mut leanh::LeanObject,
    mut v_h__3_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1487_: u8 = 0;
    v_zero_1486_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1487_ = lean_nat_dec_eq(v_x_1481_, v_zero_1486_);
    if v_isZero_1487_ == 1 {
        let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1485_);
        leanh::lean_dec(v_h__2_1484_);
        v___x_1488_ = leanh::lean_apply_1(v_h__1_1483_, v_x_1482_);
        return v___x_1488_;
    } else {
        let mut v_one_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1483_);
        v_one_1489_ = leanh::lean_unsigned_to_nat(1);
        v_n_1490_ = lean_nat_sub(v_x_1481_, v_one_1489_);
        if leanh::lean_obj_tag(v_x_1482_) == 0 {
            let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1485_);
            v___x_1491_ = leanh::lean_apply_1(v_h__2_1484_, v_n_1490_);
            return v___x_1491_;
        } else {
            let mut v_head_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1484_);
            v_head_1492_ = leanh::lean_ctor_get(v_x_1482_, 0);
            leanh::lean_inc(v_head_1492_);
            v_tail_1493_ = leanh::lean_ctor_get(v_x_1482_, 1);
            leanh::lean_inc(v_tail_1493_);
            leanh::lean_dec_ref_known(v_x_1482_, 2);
            v___x_1494_ =
                leanh::lean_apply_3(v_h__3_1485_, v_n_1490_, v_head_1492_, v_tail_1493_);
            return v___x_1494_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_1495_: *mut leanh::LeanObject,
    mut v_motive_1496_: *mut leanh::LeanObject,
    mut v_x_1497_: *mut leanh::LeanObject,
    mut v_x_1498_: *mut leanh::LeanObject,
    mut v_h__1_1499_: *mut leanh::LeanObject,
    mut v_h__2_1500_: *mut leanh::LeanObject,
    mut v_h__3_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
        v_00_u03b1_1495_,
        v_motive_1496_,
        v_x_1497_,
        v_x_1498_,
        v_h__1_1499_,
        v_h__2_1500_,
        v_h__3_1501_,
    );
    leanh::lean_dec(v_x_1497_);
    return v_res_1502_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
    mut v_p_1503_: *mut leanh::LeanObject,
    mut v_l_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1505_) == 0 {
                    leanh::lean_dec_ref(v_a_1506_);
                    leanh::lean_dec_ref(v_p_1503_);
                    leanh::lean_inc(v_l_1504_);
                    return v_l_1504_;
                } else {
                    v_head_1507_ = leanh::lean_ctor_get(v_a_1505_, 0);
                    leanh::lean_inc_n(v_head_1507_, 2);
                    v_tail_1508_ = leanh::lean_ctor_get(v_a_1505_, 1);
                    leanh::lean_inc(v_tail_1508_);
                    leanh::lean_dec_ref_known(v_a_1505_, 2);
                    leanh::lean_inc_ref(v_p_1503_);
                    v___x_1509_ = leanh::lean_apply_1(v_p_1503_, v_head_1507_);
                    v___x_1510_ = (leanh::lean_unbox(v___x_1509_) as u8);
                    if v___x_1510_ == 0 {
                        leanh::lean_dec(v_tail_1508_);
                        leanh::lean_dec(v_head_1507_);
                        leanh::lean_dec_ref(v_p_1503_);
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
    mut v_p_1514_: *mut leanh::LeanObject,
    mut v_l_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1514_, v_l_1515_, v_a_1516_, v_a_1517_,
    );
    leanh::lean_dec(v_l_1515_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
    mut v_00_u03b1_1519_: *mut leanh::LeanObject,
    mut v_p_1520_: *mut leanh::LeanObject,
    mut v_l_1521_: *mut leanh::LeanObject,
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1520_, v_l_1521_, v_a_1522_, v_a_1523_,
    );
    return v___x_1524_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(
    mut v_00_u03b1_1525_: *mut leanh::LeanObject,
    mut v_p_1526_: *mut leanh::LeanObject,
    mut v_l_1527_: *mut leanh::LeanObject,
    mut v_a_1528_: *mut leanh::LeanObject,
    mut v_a_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
        v_00_u03b1_1525_,
        v_p_1526_,
        v_l_1527_,
        v_a_1528_,
        v_a_1529_,
    );
    leanh::lean_dec(v_l_1527_);
    return v_res_1530_;
}
pub unsafe fn l_List_takeWhileTR___redArg(
    mut v_p_1531_: *mut leanh::LeanObject,
    mut v_l_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1532_);
    v___x_1534_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1531_,
        v_l_1532_,
        v_l_1532_,
        v___x_1533_,
    );
    leanh::lean_dec(v_l_1532_);
    return v___x_1534_;
}
pub unsafe fn l_List_takeWhileTR(
    mut v_00_u03b1_1535_: *mut leanh::LeanObject,
    mut v_p_1536_: *mut leanh::LeanObject,
    mut v_l_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1537_);
    v___x_1539_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1536_,
        v_l_1537_,
        v_l_1537_,
        v___x_1538_,
    );
    leanh::lean_dec(v_l_1537_);
    return v___x_1539_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v_h__1_1541_: *mut leanh::LeanObject,
    mut v_h__2_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1540_) == 0 {
        let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1542_);
        v___x_1543_ = leanh::lean_box(0);
        v___x_1544_ = leanh::lean_apply_1(v_h__1_1541_, v___x_1543_);
        return v___x_1544_;
    } else {
        let mut v_head_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1541_);
        v_head_1545_ = leanh::lean_ctor_get(v_x_1540_, 0);
        leanh::lean_inc(v_head_1545_);
        v_tail_1546_ = leanh::lean_ctor_get(v_x_1540_, 1);
        leanh::lean_inc(v_tail_1546_);
        leanh::lean_dec_ref_known(v_x_1540_, 2);
        v___x_1547_ = leanh::lean_apply_2(v_h__2_1542_, v_head_1545_, v_tail_1546_);
        return v___x_1547_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_1548_: *mut leanh::LeanObject,
    mut v_motive_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v_h__1_1551_: *mut leanh::LeanObject,
    mut v_h__2_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1550_) == 0 {
        let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1552_);
        v___x_1553_ = leanh::lean_box(0);
        v___x_1554_ = leanh::lean_apply_1(v_h__1_1551_, v___x_1553_);
        return v___x_1554_;
    } else {
        let mut v_head_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1551_);
        v_head_1555_ = leanh::lean_ctor_get(v_x_1550_, 0);
        leanh::lean_inc(v_head_1555_);
        v_tail_1556_ = leanh::lean_ctor_get(v_x_1550_, 1);
        leanh::lean_inc(v_tail_1556_);
        leanh::lean_dec_ref_known(v_x_1550_, 2);
        v___x_1557_ = leanh::lean_apply_2(v_h__2_1552_, v_head_1555_, v_tail_1556_);
        return v___x_1557_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
    mut v_x_1558_: u8,
    mut v_h__1_1559_: *mut leanh::LeanObject,
    mut v_h__2_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1558_ == 0 {
        let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1559_);
        v___x_1561_ = leanh::lean_box(0);
        v___x_1562_ = leanh::lean_apply_1(v_h__2_1560_, v___x_1561_);
        return v___x_1562_;
    } else {
        let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1560_);
        v___x_1563_ = leanh::lean_box(0);
        v___x_1564_ = leanh::lean_apply_1(v_h__1_1559_, v___x_1563_);
        return v___x_1564_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1565_: *mut leanh::LeanObject,
    mut v_h__1_1566_: *mut leanh::LeanObject,
    mut v_h__2_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_1568_: u8 = 0;
    let mut v_res_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1568_ = (leanh::lean_unbox(v_x_1565_) as u8);
    v_res_1569_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_1568_,
        v_h__1_1566_,
        v_h__2_1567_,
    );
    return v_res_1569_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
    mut v_motive_1570_: *mut leanh::LeanObject,
    mut v_x_1571_: u8,
    mut v_h__1_1572_: *mut leanh::LeanObject,
    mut v_h__2_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1571_ == 0 {
        let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1572_);
        v___x_1574_ = leanh::lean_box(0);
        v___x_1575_ = leanh::lean_apply_1(v_h__2_1573_, v___x_1574_);
        return v___x_1575_;
    } else {
        let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1573_);
        v___x_1576_ = leanh::lean_box(0);
        v___x_1577_ = leanh::lean_apply_1(v_h__1_1572_, v___x_1576_);
        return v___x_1577_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1578_: *mut leanh::LeanObject,
    mut v_x_1579_: *mut leanh::LeanObject,
    mut v_h__1_1580_: *mut leanh::LeanObject,
    mut v_h__2_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1582_ = (leanh::lean_unbox(v_x_1579_) as u8);
    v_res_1583_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
        v_motive_1578_,
        v_x_37__boxed_1582_,
        v_h__1_1580_,
        v_h__2_1581_,
    );
    return v_res_1583_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(
    mut v_x_1584_: *mut leanh::LeanObject,
    mut v_x_1585_: *mut leanh::LeanObject,
    mut v_h__1_1586_: *mut leanh::LeanObject,
    mut v_h__2_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1584_) == 0 {
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1587_);
        v___x_1588_ = leanh::lean_apply_1(v_h__1_1586_, v_x_1585_);
        return v___x_1588_;
    } else {
        let mut v_head_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1586_);
        v_head_1589_ = leanh::lean_ctor_get(v_x_1584_, 0);
        leanh::lean_inc(v_head_1589_);
        v_tail_1590_ = leanh::lean_ctor_get(v_x_1584_, 1);
        leanh::lean_inc(v_tail_1590_);
        leanh::lean_dec_ref_known(v_x_1584_, 2);
        v___x_1591_ =
            leanh::lean_apply_3(v_h__2_1587_, v_head_1589_, v_tail_1590_, v_x_1585_);
        return v___x_1591_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(
    mut v_00_u03b1_1592_: *mut leanh::LeanObject,
    mut v_motive_1593_: *mut leanh::LeanObject,
    mut v_x_1594_: *mut leanh::LeanObject,
    mut v_x_1595_: *mut leanh::LeanObject,
    mut v_h__1_1596_: *mut leanh::LeanObject,
    mut v_h__2_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1594_) == 0 {
        let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1597_);
        v___x_1598_ = leanh::lean_apply_1(v_h__1_1596_, v_x_1595_);
        return v___x_1598_;
    } else {
        let mut v_head_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1596_);
        v_head_1599_ = leanh::lean_ctor_get(v_x_1594_, 0);
        leanh::lean_inc(v_head_1599_);
        v_tail_1600_ = leanh::lean_ctor_get(v_x_1594_, 1);
        leanh::lean_inc(v_tail_1600_);
        leanh::lean_dec_ref_known(v_x_1594_, 2);
        v___x_1601_ =
            leanh::lean_apply_3(v_h__2_1597_, v_head_1599_, v_tail_1600_, v_x_1595_);
        return v___x_1601_;
    }
}
pub unsafe fn l_List_dropLastTR___redArg(
    mut v_l_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_array_mk(v_l_1602_);
    v___x_1604_ = lean_array_pop(v___x_1603_);
    v___x_1605_ = lean_array_to_list(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn l_List_dropLastTR(
    mut v_00_u03b1_1606_: *mut leanh::LeanObject,
    mut v_l_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_array_mk(v_l_1607_);
    v___x_1609_ = lean_array_pop(v___x_1608_);
    v___x_1610_ = lean_array_to_list(v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(
    mut v_p_1611_: *mut leanh::LeanObject,
    mut v_x_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1612_) == 0 {
                    leanh::lean_dec_ref(v_p_1611_);
                    v___x_1613_ = leanh::lean_box(0);
                    return v___x_1613_;
                } else {
                    v_head_1614_ = leanh::lean_ctor_get(v_x_1612_, 0);
                    leanh::lean_inc_n(v_head_1614_, 2);
                    v_tail_1615_ = leanh::lean_ctor_get(v_x_1612_, 1);
                    leanh::lean_inc(v_tail_1615_);
                    leanh::lean_dec_ref_known(v_x_1612_, 2);
                    leanh::lean_inc_ref(v_p_1611_);
                    v___x_1616_ = leanh::lean_apply_1(v_p_1611_, v_head_1614_);
                    v___x_1617_ = (leanh::lean_unbox(v___x_1616_) as u8);
                    if v___x_1617_ == 0 {
                        leanh::lean_dec(v_head_1614_);
                        v_x_1612_ = v_tail_1615_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1615_);
                        leanh::lean_dec_ref(v_p_1611_);
                        v___x_1619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1619_, 0, v_head_1614_);
                        return v___x_1619_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findRev_x3fTR___redArg(
    mut v_p_1620_: *mut leanh::LeanObject,
    mut v_l_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_List_reverse___redArg(v_l_1621_);
    v___x_1623_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1620_, v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_List_findRev_x3fTR(
    mut v_00_u03b1_1624_: *mut leanh::LeanObject,
    mut v_p_1625_: *mut leanh::LeanObject,
    mut v_l_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_List_findRev_x3fTR___redArg(v_p_1625_, v_l_1626_);
    return v___x_1627_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(
    mut v_00_u03b1_1628_: *mut leanh::LeanObject,
    mut v_p_1629_: *mut leanh::LeanObject,
    mut v_x_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1629_, v_x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_1632_: *mut leanh::LeanObject,
    mut v_h__1_1633_: *mut leanh::LeanObject,
    mut v_h__2_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1632_) == 0 {
        let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1633_);
        v___x_1635_ = leanh::lean_box(0);
        v___x_1636_ = leanh::lean_apply_1(v_h__2_1634_, v___x_1635_);
        return v___x_1636_;
    } else {
        let mut v_val_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1634_);
        v_val_1637_ = leanh::lean_ctor_get(v_x_1632_, 0);
        leanh::lean_inc(v_val_1637_);
        leanh::lean_dec_ref_known(v_x_1632_, 1);
        v___x_1638_ = leanh::lean_apply_1(v_h__1_1633_, v_val_1637_);
        return v___x_1638_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_1639_: *mut leanh::LeanObject,
    mut v_motive_1640_: *mut leanh::LeanObject,
    mut v_x_1641_: *mut leanh::LeanObject,
    mut v_h__1_1642_: *mut leanh::LeanObject,
    mut v_h__2_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1641_) == 0 {
        let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1642_);
        v___x_1644_ = leanh::lean_box(0);
        v___x_1645_ = leanh::lean_apply_1(v_h__2_1643_, v___x_1644_);
        return v___x_1645_;
    } else {
        let mut v_val_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1643_);
        v_val_1646_ = leanh::lean_ctor_get(v_x_1641_, 0);
        leanh::lean_inc(v_val_1646_);
        leanh::lean_dec_ref_known(v_x_1641_, 1);
        v___x_1647_ = leanh::lean_apply_1(v_h__1_1642_, v_val_1646_);
        return v___x_1647_;
    }
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
    mut v_f_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1649_) == 0 {
                    leanh::lean_dec_ref(v_f_1648_);
                    v___x_1650_ = leanh::lean_box(0);
                    return v___x_1650_;
                } else {
                    v_head_1651_ = leanh::lean_ctor_get(v_x_1649_, 0);
                    leanh::lean_inc(v_head_1651_);
                    v_tail_1652_ = leanh::lean_ctor_get(v_x_1649_, 1);
                    leanh::lean_inc(v_tail_1652_);
                    leanh::lean_dec_ref_known(v_x_1649_, 2);
                    leanh::lean_inc_ref(v_f_1648_);
                    v___x_1653_ = leanh::lean_apply_1(v_f_1648_, v_head_1651_);
                    if leanh::lean_obj_tag(v___x_1653_) == 0 {
                        v_x_1649_ = v_tail_1652_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_1652_);
                        leanh::lean_dec_ref(v_f_1648_);
                        return v___x_1653_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findSomeRev_x3fTR___redArg(
    mut v_f_1655_: *mut leanh::LeanObject,
    mut v_l_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = l_List_reverse___redArg(v_l_1656_);
    v___x_1658_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
        v_f_1655_,
        v___x_1657_,
    );
    return v___x_1658_;
}
pub unsafe fn l_List_findSomeRev_x3fTR(
    mut v_00_u03b1_1659_: *mut leanh::LeanObject,
    mut v_00_u03b2_1660_: *mut leanh::LeanObject,
    mut v_f_1661_: *mut leanh::LeanObject,
    mut v_l_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_List_findSomeRev_x3fTR___redArg(v_f_1661_, v_l_1662_);
    return v___x_1663_;
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(
    mut v_00_u03b1_1664_: *mut leanh::LeanObject,
    mut v_00_u03b2_1665_: *mut leanh::LeanObject,
    mut v_f_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ =
        l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_1666_, v_x_1667_);
    return v___x_1668_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(
    mut v_x1_1669_: *mut leanh::LeanObject,
    mut v_x2_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1671_, 0, v_x1_1669_);
    leanh::lean_ctor_set(v___x_1671_, 1, v_x2_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
    mut v_inst_1673_: *mut leanh::LeanObject,
    mut v_l_1674_: *mut leanh::LeanObject,
    mut v_b_1675_: *mut leanh::LeanObject,
    mut v_c_1676_: *mut leanh::LeanObject,
    mut v_a_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___f_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: usize = 0;
    let mut v___x_1696_: usize = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1677_) == 0 {
                    leanh::lean_dec_ref(v_a_1678_);
                    leanh::lean_dec(v_c_1676_);
                    leanh::lean_dec(v_b_1675_);
                    leanh::lean_dec_ref(v_inst_1673_);
                    leanh::lean_inc(v_l_1674_);
                    return v_l_1674_;
                } else {
                    v_head_1679_ = leanh::lean_ctor_get(v_a_1677_, 0);
                    v_tail_1680_ = leanh::lean_ctor_get(v_a_1677_, 1);
                    v_isSharedCheck_1699_ = (!leanh::lean_is_exclusive(v_a_1677_)) as u8;
                    if v_isSharedCheck_1699_ == 0 {
                        v___x_1682_ = v_a_1677_;
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1680_);
                        leanh::lean_inc(v_head_1679_);
                        leanh::lean_dec(v_a_1677_);
                        v___x_1682_ = leanh::lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1673_);
                leanh::lean_inc(v_head_1679_);
                leanh::lean_inc(v_b_1675_);
                v___x_1684_ = leanh::lean_apply_2(v_inst_1673_, v_b_1675_, v_head_1679_);
                v___x_1685_ = (leanh::lean_unbox(v___x_1684_) as u8);
                if v___x_1685_ == 0 {
                    leanh::lean_del_object(v___x_1682_);
                    v___x_1686_ = lean_array_push(v_a_1678_, v_head_1679_);
                    v_a_1677_ = v_tail_1680_;
                    v_a_1678_ = v___x_1686_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_head_1679_);
                    leanh::lean_dec(v_b_1675_);
                    leanh::lean_dec_ref(v_inst_1673_);
                    if v_isShared_1683_ == 0 {
                        leanh::lean_ctor_set(v___x_1682_, 0, v_c_1676_);
                        v___x_1689_ = v___x_1682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_c_1676_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_tail_1680_);
                        v___x_1689_ = v_reuseFailAlloc_1698_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1690_ = lean_array_get_size(v_a_1678_);
                v___x_1691_ = leanh::lean_unsigned_to_nat(0);
                v___x_1692_ = l_List_foldrTR___redArg___closed__9;
                v___x_1693_ = lean_nat_dec_lt(v___x_1691_, v___x_1690_);
                if v___x_1693_ == 0 {
                    leanh::lean_dec_ref(v_a_1678_);
                    return v___x_1689_;
                } else {
                    v___f_1694_ =
                        l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                    v___x_1695_ = lean_usize_of_nat(v___x_1690_);
                    v___x_1696_ = 0usize;
                    v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
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
    mut v_inst_1700_: *mut leanh::LeanObject,
    mut v_l_1701_: *mut leanh::LeanObject,
    mut v_b_1702_: *mut leanh::LeanObject,
    mut v_c_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
    mut v_a_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1706_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1700_,
        v_l_1701_,
        v_b_1702_,
        v_c_1703_,
        v_a_1704_,
        v_a_1705_,
    );
    leanh::lean_dec(v_l_1701_);
    return v_res_1706_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go(
    mut v_00_u03b1_1707_: *mut leanh::LeanObject,
    mut v_inst_1708_: *mut leanh::LeanObject,
    mut v_l_1709_: *mut leanh::LeanObject,
    mut v_b_1710_: *mut leanh::LeanObject,
    mut v_c_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1715_: *mut leanh::LeanObject,
    mut v_inst_1716_: *mut leanh::LeanObject,
    mut v_l_1717_: *mut leanh::LeanObject,
    mut v_b_1718_: *mut leanh::LeanObject,
    mut v_c_1719_: *mut leanh::LeanObject,
    mut v_a_1720_: *mut leanh::LeanObject,
    mut v_a_1721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1722_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(
        v_00_u03b1_1715_,
        v_inst_1716_,
        v_l_1717_,
        v_b_1718_,
        v_c_1719_,
        v_a_1720_,
        v_a_1721_,
    );
    leanh::lean_dec(v_l_1717_);
    return v_res_1722_;
}
pub unsafe fn l_List_replaceTR___redArg(
    mut v_inst_1723_: *mut leanh::LeanObject,
    mut v_l_1724_: *mut leanh::LeanObject,
    mut v_b_1725_: *mut leanh::LeanObject,
    mut v_c_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1724_);
    v___x_1728_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1723_,
        v_l_1724_,
        v_b_1725_,
        v_c_1726_,
        v_l_1724_,
        v___x_1727_,
    );
    leanh::lean_dec(v_l_1724_);
    return v___x_1728_;
}
pub unsafe fn l_List_replaceTR(
    mut v_00_u03b1_1729_: *mut leanh::LeanObject,
    mut v_inst_1730_: *mut leanh::LeanObject,
    mut v_l_1731_: *mut leanh::LeanObject,
    mut v_b_1732_: *mut leanh::LeanObject,
    mut v_c_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1731_);
    v___x_1735_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1730_,
        v_l_1731_,
        v_b_1732_,
        v_c_1733_,
        v_l_1731_,
        v___x_1734_,
    );
    leanh::lean_dec(v_l_1731_);
    return v___x_1735_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(
    mut v_x_1736_: *mut leanh::LeanObject,
    mut v_x_1737_: *mut leanh::LeanObject,
    mut v_x_1738_: *mut leanh::LeanObject,
    mut v_h__1_1739_: *mut leanh::LeanObject,
    mut v_h__2_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1736_) == 0 {
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1740_);
        v___x_1741_ = leanh::lean_apply_2(v_h__1_1739_, v_x_1737_, v_x_1738_);
        return v___x_1741_;
    } else {
        let mut v_head_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1739_);
        v_head_1742_ = leanh::lean_ctor_get(v_x_1736_, 0);
        leanh::lean_inc(v_head_1742_);
        v_tail_1743_ = leanh::lean_ctor_get(v_x_1736_, 1);
        leanh::lean_inc(v_tail_1743_);
        leanh::lean_dec_ref_known(v_x_1736_, 2);
        v___x_1744_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_1745_: *mut leanh::LeanObject,
    mut v_motive_1746_: *mut leanh::LeanObject,
    mut v_x_1747_: *mut leanh::LeanObject,
    mut v_x_1748_: *mut leanh::LeanObject,
    mut v_x_1749_: *mut leanh::LeanObject,
    mut v_h__1_1750_: *mut leanh::LeanObject,
    mut v_h__2_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1747_) == 0 {
        let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1751_);
        v___x_1752_ = leanh::lean_apply_2(v_h__1_1750_, v_x_1748_, v_x_1749_);
        return v___x_1752_;
    } else {
        let mut v_head_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1750_);
        v_head_1753_ = leanh::lean_ctor_get(v_x_1747_, 0);
        leanh::lean_inc(v_head_1753_);
        v_tail_1754_ = leanh::lean_ctor_get(v_x_1747_, 1);
        leanh::lean_inc(v_tail_1754_);
        leanh::lean_dec_ref_known(v_x_1747_, 2);
        v___x_1755_ = leanh::lean_apply_4(
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
    mut v_f_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
    mut v_a_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v_zero_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: usize = 0;
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1757_) == 0 {
                    leanh::lean_dec(v_a_1758_);
                    leanh::lean_dec(v_f_1756_);
                    v___x_1760_ = lean_array_to_list(v_a_1759_);
                    return v___x_1760_;
                } else {
                    v_head_1761_ = leanh::lean_ctor_get(v_a_1757_, 0);
                    v_tail_1762_ = leanh::lean_ctor_get(v_a_1757_, 1);
                    v_isSharedCheck_1781_ = (!leanh::lean_is_exclusive(v_a_1757_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v___x_1764_ = v_a_1757_;
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1762_);
                        leanh::lean_inc(v_head_1761_);
                        leanh::lean_dec(v_a_1757_);
                        v___x_1764_ = leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1766_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1767_ = lean_nat_dec_eq(v_a_1758_, v_zero_1766_);
                if v_isZero_1767_ == 1 {
                    leanh::lean_dec(v_a_1758_);
                    v___x_1768_ = leanh::lean_apply_1(v_f_1756_, v_head_1761_);
                    if v_isShared_1765_ == 0 {
                        leanh::lean_ctor_set(v___x_1764_, 0, v___x_1768_);
                        v___x_1770_ = v___x_1764_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1776_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_tail_1762_);
                        v___x_1770_ = v_reuseFailAlloc_1776_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1764_);
                    v_one_1777_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1778_ = lean_nat_sub(v_a_1758_, v_one_1777_);
                    leanh::lean_dec(v_a_1758_);
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
                    leanh::lean_dec_ref(v_a_1759_);
                    return v___x_1770_;
                } else {
                    v___x_1773_ = lean_usize_of_nat(v___x_1771_);
                    v___x_1774_ = 0usize;
                    v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1759_, v___x_1773_, v___x_1774_, v___x_1770_);
                    leanh::lean_dec_ref(v_a_1759_);
                    return v___x_1775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_modifyTR_go(
    mut v_00_u03b1_1782_: *mut leanh::LeanObject,
    mut v_f_1783_: *mut leanh::LeanObject,
    mut v_a_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(
        v_f_1783_, v_a_1784_, v_a_1785_, v_a_1786_,
    );
    return v___x_1787_;
}
pub unsafe fn l_List_modifyTR___redArg(
    mut v_l_1788_: *mut leanh::LeanObject,
    mut v_i_1789_: *mut leanh::LeanObject,
    mut v_f_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1793_: *mut leanh::LeanObject,
    mut v_l_1794_: *mut leanh::LeanObject,
    mut v_i_1795_: *mut leanh::LeanObject,
    mut v_f_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1797_ = l_List_modifyTR___redArg(v_l_1794_, v_i_1795_, v_f_1796_);
    return v___x_1797_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1802_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1803_ = lean_nat_dec_eq(v_a_1799_, v_zero_1802_);
                if v_isZero_1803_ == 1 {
                    leanh::lean_dec(v_a_1799_);
                    v___x_1804_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1804_, 0, v_a_1798_);
                    leanh::lean_ctor_set(v___x_1804_, 1, v_a_1800_);
                    v___x_1805_ = lean_array_get_size(v_a_1801_);
                    v___x_1806_ = lean_nat_dec_lt(v_zero_1802_, v___x_1805_);
                    if v___x_1806_ == 0 {
                        leanh::lean_dec_ref(v_a_1801_);
                        return v___x_1804_;
                    } else {
                        v___x_1807_ = lean_usize_of_nat(v___x_1805_);
                        v___x_1808_ = 0usize;
                        v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1801_, v___x_1807_, v___x_1808_, v___x_1804_);
                        leanh::lean_dec_ref(v_a_1801_);
                        return v___x_1809_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_a_1800_) == 0 {
                        leanh::lean_dec(v_a_1799_);
                        leanh::lean_dec(v_a_1798_);
                        v___x_1810_ = lean_array_to_list(v_a_1801_);
                        return v___x_1810_;
                    } else {
                        v_head_1811_ = leanh::lean_ctor_get(v_a_1800_, 0);
                        leanh::lean_inc(v_head_1811_);
                        v_tail_1812_ = leanh::lean_ctor_get(v_a_1800_, 1);
                        leanh::lean_inc(v_tail_1812_);
                        leanh::lean_dec_ref_known(v_a_1800_, 2);
                        v_one_1813_ = leanh::lean_unsigned_to_nat(1);
                        v_n_1814_ = lean_nat_sub(v_a_1799_, v_one_1813_);
                        leanh::lean_dec(v_a_1799_);
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
    mut v_00_u03b1_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
        v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_,
    );
    return v___x_1822_;
}
pub unsafe fn l_List_insertIdxTR___redArg(
    mut v_l_1823_: *mut leanh::LeanObject,
    mut v_n_1824_: *mut leanh::LeanObject,
    mut v_a_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1828_: *mut leanh::LeanObject,
    mut v_l_1829_: *mut leanh::LeanObject,
    mut v_n_1830_: *mut leanh::LeanObject,
    mut v_a_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_1834_: *mut leanh::LeanObject,
    mut v_x_1835_: *mut leanh::LeanObject,
    mut v_x_1836_: *mut leanh::LeanObject,
    mut v_h__1_1837_: *mut leanh::LeanObject,
    mut v_h__2_1838_: *mut leanh::LeanObject,
    mut v_h__3_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1841_: u8 = 0;
    v_zero_1840_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1841_ = lean_nat_dec_eq(v_x_1834_, v_zero_1840_);
    if v_isZero_1841_ == 1 {
        let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1839_);
        leanh::lean_dec(v_h__2_1838_);
        leanh::lean_dec(v_x_1834_);
        v___x_1842_ = leanh::lean_apply_2(v_h__1_1837_, v_x_1835_, v_x_1836_);
        return v___x_1842_;
    } else {
        leanh::lean_dec(v_h__1_1837_);
        if leanh::lean_obj_tag(v_x_1835_) == 0 {
            let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1839_);
            v___x_1843_ = leanh::lean_apply_3(
                v_h__2_1838_,
                v_x_1834_,
                v_x_1836_,
                leanh::lean_box(0),
            );
            return v___x_1843_;
        } else {
            let mut v_head_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1838_);
            v_head_1844_ = leanh::lean_ctor_get(v_x_1835_, 0);
            leanh::lean_inc(v_head_1844_);
            v_tail_1845_ = leanh::lean_ctor_get(v_x_1835_, 1);
            leanh::lean_inc(v_tail_1845_);
            leanh::lean_dec_ref_known(v_x_1835_, 2);
            v_one_1846_ = leanh::lean_unsigned_to_nat(1);
            v_n_1847_ = lean_nat_sub(v_x_1834_, v_one_1846_);
            leanh::lean_dec(v_x_1834_);
            v___x_1848_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_motive_1850_: *mut leanh::LeanObject,
    mut v_x_1851_: *mut leanh::LeanObject,
    mut v_x_1852_: *mut leanh::LeanObject,
    mut v_x_1853_: *mut leanh::LeanObject,
    mut v_h__1_1854_: *mut leanh::LeanObject,
    mut v_h__2_1855_: *mut leanh::LeanObject,
    mut v_h__3_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1858_: u8 = 0;
    v_zero_1857_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1858_ = lean_nat_dec_eq(v_x_1851_, v_zero_1857_);
    if v_isZero_1858_ == 1 {
        let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1856_);
        leanh::lean_dec(v_h__2_1855_);
        leanh::lean_dec(v_x_1851_);
        v___x_1859_ = leanh::lean_apply_2(v_h__1_1854_, v_x_1852_, v_x_1853_);
        return v___x_1859_;
    } else {
        leanh::lean_dec(v_h__1_1854_);
        if leanh::lean_obj_tag(v_x_1852_) == 0 {
            let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1856_);
            v___x_1860_ = leanh::lean_apply_3(
                v_h__2_1855_,
                v_x_1851_,
                v_x_1853_,
                leanh::lean_box(0),
            );
            return v___x_1860_;
        } else {
            let mut v_head_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1855_);
            v_head_1861_ = leanh::lean_ctor_get(v_x_1852_, 0);
            leanh::lean_inc(v_head_1861_);
            v_tail_1862_ = leanh::lean_ctor_get(v_x_1852_, 1);
            leanh::lean_inc(v_tail_1862_);
            leanh::lean_dec_ref_known(v_x_1852_, 2);
            v_one_1863_ = leanh::lean_unsigned_to_nat(1);
            v_n_1864_ = lean_nat_sub(v_x_1851_, v_one_1863_);
            leanh::lean_dec(v_x_1851_);
            v___x_1865_ = leanh::lean_apply_4(
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
    mut v_inst_1866_: *mut leanh::LeanObject,
    mut v_l_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___f_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1869_) == 0 {
                    leanh::lean_dec_ref(v_a_1870_);
                    leanh::lean_dec(v_a_1868_);
                    leanh::lean_dec_ref(v_inst_1866_);
                    leanh::lean_inc(v_l_1867_);
                    return v_l_1867_;
                } else {
                    v_head_1871_ = leanh::lean_ctor_get(v_a_1869_, 0);
                    leanh::lean_inc_n(v_head_1871_, 2);
                    v_tail_1872_ = leanh::lean_ctor_get(v_a_1869_, 1);
                    leanh::lean_inc(v_tail_1872_);
                    leanh::lean_dec_ref_known(v_a_1869_, 2);
                    leanh::lean_inc_ref(v_inst_1866_);
                    leanh::lean_inc(v_a_1868_);
                    v___x_1873_ = leanh::lean_apply_2(v_inst_1866_, v_head_1871_, v_a_1868_);
                    v___x_1874_ = (leanh::lean_unbox(v___x_1873_) as u8);
                    if v___x_1874_ == 0 {
                        v___x_1875_ = lean_array_push(v_a_1870_, v_head_1871_);
                        v_a_1869_ = v_tail_1872_;
                        v_a_1870_ = v___x_1875_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1871_);
                        leanh::lean_dec(v_a_1868_);
                        leanh::lean_dec_ref(v_inst_1866_);
                        v___x_1877_ = lean_array_get_size(v_a_1870_);
                        v___x_1878_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1879_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1880_ = lean_nat_dec_lt(v___x_1878_, v___x_1877_);
                        if v___x_1880_ == 0 {
                            leanh::lean_dec_ref(v_a_1870_);
                            return v_tail_1872_;
                        } else {
                            v___f_1881_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1882_ = lean_usize_of_nat(v___x_1877_);
                            v___x_1883_ = 0usize;
                            v___x_1884_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
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
    mut v_inst_1885_: *mut leanh::LeanObject,
    mut v_l_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1885_,
        v_l_1886_,
        v_a_1887_,
        v_a_1888_,
        v_a_1889_,
    );
    leanh::lean_dec(v_l_1886_);
    return v_res_1890_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go(
    mut v_00_u03b1_1891_: *mut leanh::LeanObject,
    mut v_inst_1892_: *mut leanh::LeanObject,
    mut v_l_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
    mut v_a_1895_: *mut leanh::LeanObject,
    mut v_a_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1898_: *mut leanh::LeanObject,
    mut v_inst_1899_: *mut leanh::LeanObject,
    mut v_l_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(
        v_00_u03b1_1898_,
        v_inst_1899_,
        v_l_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
    );
    leanh::lean_dec(v_l_1900_);
    return v_res_1904_;
}
pub unsafe fn l_List_eraseTR___redArg(
    mut v_inst_1905_: *mut leanh::LeanObject,
    mut v_l_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1906_);
    v___x_1909_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1905_,
        v_l_1906_,
        v_a_1907_,
        v_l_1906_,
        v___x_1908_,
    );
    leanh::lean_dec(v_l_1906_);
    return v___x_1909_;
}
pub unsafe fn l_List_eraseTR(
    mut v_00_u03b1_1910_: *mut leanh::LeanObject,
    mut v_inst_1911_: *mut leanh::LeanObject,
    mut v_l_1912_: *mut leanh::LeanObject,
    mut v_a_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1912_);
    v___x_1915_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1911_,
        v_l_1912_,
        v_a_1913_,
        v_l_1912_,
        v___x_1914_,
    );
    leanh::lean_dec(v_l_1912_);
    return v___x_1915_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
    mut v_p_1916_: *mut leanh::LeanObject,
    mut v_l_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___f_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: usize = 0;
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1918_) == 0 {
                    leanh::lean_dec_ref(v_a_1919_);
                    leanh::lean_dec_ref(v_p_1916_);
                    leanh::lean_inc(v_l_1917_);
                    return v_l_1917_;
                } else {
                    v_head_1920_ = leanh::lean_ctor_get(v_a_1918_, 0);
                    leanh::lean_inc_n(v_head_1920_, 2);
                    v_tail_1921_ = leanh::lean_ctor_get(v_a_1918_, 1);
                    leanh::lean_inc(v_tail_1921_);
                    leanh::lean_dec_ref_known(v_a_1918_, 2);
                    leanh::lean_inc_ref(v_p_1916_);
                    v___x_1922_ = leanh::lean_apply_1(v_p_1916_, v_head_1920_);
                    v___x_1923_ = (leanh::lean_unbox(v___x_1922_) as u8);
                    if v___x_1923_ == 0 {
                        v___x_1924_ = lean_array_push(v_a_1919_, v_head_1920_);
                        v_a_1918_ = v_tail_1921_;
                        v_a_1919_ = v___x_1924_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1920_);
                        leanh::lean_dec_ref(v_p_1916_);
                        v___x_1926_ = lean_array_get_size(v_a_1919_);
                        v___x_1927_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1928_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1929_ = lean_nat_dec_lt(v___x_1927_, v___x_1926_);
                        if v___x_1929_ == 0 {
                            leanh::lean_dec_ref(v_a_1919_);
                            return v_tail_1921_;
                        } else {
                            v___f_1930_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1931_ = lean_usize_of_nat(v___x_1926_);
                            v___x_1932_ = 0usize;
                            v___x_1933_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
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
    mut v_p_1934_: *mut leanh::LeanObject,
    mut v_l_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1934_, v_l_1935_, v_a_1936_, v_a_1937_,
    );
    leanh::lean_dec(v_l_1935_);
    return v_res_1938_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go(
    mut v_00_u03b1_1939_: *mut leanh::LeanObject,
    mut v_p_1940_: *mut leanh::LeanObject,
    mut v_l_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1940_, v_l_1941_, v_a_1942_, v_a_1943_,
    );
    return v___x_1944_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(
    mut v_00_u03b1_1945_: *mut leanh::LeanObject,
    mut v_p_1946_: *mut leanh::LeanObject,
    mut v_l_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(
        v_00_u03b1_1945_,
        v_p_1946_,
        v_l_1947_,
        v_a_1948_,
        v_a_1949_,
    );
    leanh::lean_dec(v_l_1947_);
    return v_res_1950_;
}
pub unsafe fn l_List_erasePTR___redArg(
    mut v_p_1951_: *mut leanh::LeanObject,
    mut v_l_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1952_);
    v___x_1954_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1951_,
        v_l_1952_,
        v_l_1952_,
        v___x_1953_,
    );
    leanh::lean_dec(v_l_1952_);
    return v___x_1954_;
}
pub unsafe fn l_List_erasePTR(
    mut v_00_u03b1_1955_: *mut leanh::LeanObject,
    mut v_p_1956_: *mut leanh::LeanObject,
    mut v_l_1957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1957_);
    v___x_1959_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1956_,
        v_l_1957_,
        v_l_1957_,
        v___x_1958_,
    );
    leanh::lean_dec(v_l_1957_);
    return v___x_1959_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
    mut v_l_1960_: *mut leanh::LeanObject,
    mut v_a_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1967_: u8 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1961_) == 0 {
                    leanh::lean_dec_ref(v_a_1963_);
                    leanh::lean_dec(v_a_1962_);
                    leanh::lean_inc(v_l_1960_);
                    return v_l_1960_;
                } else {
                    v_head_1964_ = leanh::lean_ctor_get(v_a_1961_, 0);
                    leanh::lean_inc(v_head_1964_);
                    v_tail_1965_ = leanh::lean_ctor_get(v_a_1961_, 1);
                    leanh::lean_inc(v_tail_1965_);
                    leanh::lean_dec_ref_known(v_a_1961_, 2);
                    v_zero_1966_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_1967_ = lean_nat_dec_eq(v_a_1962_, v_zero_1966_);
                    if v_isZero_1967_ == 1 {
                        leanh::lean_dec(v_head_1964_);
                        leanh::lean_dec(v_a_1962_);
                        v___x_1968_ = lean_array_get_size(v_a_1963_);
                        v___x_1969_ = lean_nat_dec_lt(v_zero_1966_, v___x_1968_);
                        if v___x_1969_ == 0 {
                            leanh::lean_dec_ref(v_a_1963_);
                            return v_tail_1965_;
                        } else {
                            v___x_1970_ = lean_usize_of_nat(v___x_1968_);
                            v___x_1971_ = 0usize;
                            v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1963_, v___x_1970_, v___x_1971_, v_tail_1965_);
                            leanh::lean_dec_ref(v_a_1963_);
                            return v___x_1972_;
                        }
                    } else {
                        v_one_1973_ = leanh::lean_unsigned_to_nat(1);
                        v_n_1974_ = lean_nat_sub(v_a_1962_, v_one_1973_);
                        leanh::lean_dec(v_a_1962_);
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
    mut v_l_1977_: *mut leanh::LeanObject,
    mut v_a_1978_: *mut leanh::LeanObject,
    mut v_a_1979_: *mut leanh::LeanObject,
    mut v_a_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1977_, v_a_1978_, v_a_1979_, v_a_1980_,
    );
    leanh::lean_dec(v_l_1977_);
    return v_res_1981_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
    mut v_00_u03b1_1982_: *mut leanh::LeanObject,
    mut v_l_1983_: *mut leanh::LeanObject,
    mut v_a_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
    mut v_a_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1983_, v_a_1984_, v_a_1985_, v_a_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(
    mut v_00_u03b1_1988_: *mut leanh::LeanObject,
    mut v_l_1989_: *mut leanh::LeanObject,
    mut v_a_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1993_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
        v_00_u03b1_1988_,
        v_l_1989_,
        v_a_1990_,
        v_a_1991_,
        v_a_1992_,
    );
    leanh::lean_dec(v_l_1989_);
    return v_res_1993_;
}
pub unsafe fn l_List_eraseIdxTR___redArg(
    mut v_l_1994_: *mut leanh::LeanObject,
    mut v_n_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1994_);
    v___x_1997_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1994_,
        v_l_1994_,
        v_n_1995_,
        v___x_1996_,
    );
    leanh::lean_dec(v_l_1994_);
    return v___x_1997_;
}
pub unsafe fn l_List_eraseIdxTR(
    mut v_00_u03b1_1998_: *mut leanh::LeanObject,
    mut v_l_1999_: *mut leanh::LeanObject,
    mut v_n_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_List_setTR___redArg___closed__0;
    leanh::lean_inc(v_l_1999_);
    v___x_2002_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1999_,
        v_l_1999_,
        v_n_2000_,
        v___x_2001_,
    );
    leanh::lean_dec(v_l_1999_);
    return v___x_2002_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(
    mut v_x_2003_: *mut leanh::LeanObject,
    mut v_x_2004_: *mut leanh::LeanObject,
    mut v_h__1_2005_: *mut leanh::LeanObject,
    mut v_h__2_2006_: *mut leanh::LeanObject,
    mut v_h__3_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2003_) == 0 {
        let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_2007_);
        leanh::lean_dec(v_h__2_2006_);
        v___x_2008_ = leanh::lean_apply_1(v_h__1_2005_, v_x_2004_);
        return v___x_2008_;
    } else {
        let mut v_head_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_2012_: u8 = 0;
        leanh::lean_dec(v_h__1_2005_);
        v_head_2009_ = leanh::lean_ctor_get(v_x_2003_, 0);
        leanh::lean_inc(v_head_2009_);
        v_tail_2010_ = leanh::lean_ctor_get(v_x_2003_, 1);
        leanh::lean_inc(v_tail_2010_);
        leanh::lean_dec_ref_known(v_x_2003_, 2);
        v_zero_2011_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_2012_ = lean_nat_dec_eq(v_x_2004_, v_zero_2011_);
        if v_isZero_2012_ == 1 {
            let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2007_);
            leanh::lean_dec(v_x_2004_);
            v___x_2013_ = leanh::lean_apply_2(v_h__2_2006_, v_head_2009_, v_tail_2010_);
            return v___x_2013_;
        } else {
            let mut v_one_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2006_);
            v_one_2014_ = leanh::lean_unsigned_to_nat(1);
            v_n_2015_ = lean_nat_sub(v_x_2004_, v_one_2014_);
            leanh::lean_dec(v_x_2004_);
            v___x_2016_ =
                leanh::lean_apply_3(v_h__3_2007_, v_head_2009_, v_tail_2010_, v_n_2015_);
            return v___x_2016_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(
    mut v_00_u03b1_2017_: *mut leanh::LeanObject,
    mut v_motive_2018_: *mut leanh::LeanObject,
    mut v_x_2019_: *mut leanh::LeanObject,
    mut v_x_2020_: *mut leanh::LeanObject,
    mut v_h__1_2021_: *mut leanh::LeanObject,
    mut v_h__2_2022_: *mut leanh::LeanObject,
    mut v_h__3_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2019_) == 0 {
        let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_2023_);
        leanh::lean_dec(v_h__2_2022_);
        v___x_2024_ = leanh::lean_apply_1(v_h__1_2021_, v_x_2020_);
        return v___x_2024_;
    } else {
        let mut v_head_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_2028_: u8 = 0;
        leanh::lean_dec(v_h__1_2021_);
        v_head_2025_ = leanh::lean_ctor_get(v_x_2019_, 0);
        leanh::lean_inc(v_head_2025_);
        v_tail_2026_ = leanh::lean_ctor_get(v_x_2019_, 1);
        leanh::lean_inc(v_tail_2026_);
        leanh::lean_dec_ref_known(v_x_2019_, 2);
        v_zero_2027_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_2028_ = lean_nat_dec_eq(v_x_2020_, v_zero_2027_);
        if v_isZero_2028_ == 1 {
            let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2023_);
            leanh::lean_dec(v_x_2020_);
            v___x_2029_ = leanh::lean_apply_2(v_h__2_2022_, v_head_2025_, v_tail_2026_);
            return v___x_2029_;
        } else {
            let mut v_one_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2022_);
            v_one_2030_ = leanh::lean_unsigned_to_nat(1);
            v_n_2031_ = lean_nat_sub(v_x_2020_, v_one_2030_);
            leanh::lean_dec(v_x_2020_);
            v___x_2032_ =
                leanh::lean_apply_3(v_h__3_2023_, v_head_2025_, v_tail_2026_, v_n_2031_);
            return v___x_2032_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
    mut v_f_2033_: *mut leanh::LeanObject,
    mut v_a_2034_: *mut leanh::LeanObject,
    mut v_a_2035_: *mut leanh::LeanObject,
    mut v_a_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2034_) == 1 {
                    if leanh::lean_obj_tag(v_a_2035_) == 1 {
                        v_head_2037_ = leanh::lean_ctor_get(v_a_2034_, 0);
                        leanh::lean_inc(v_head_2037_);
                        v_tail_2038_ = leanh::lean_ctor_get(v_a_2034_, 1);
                        leanh::lean_inc(v_tail_2038_);
                        leanh::lean_dec_ref_known(v_a_2034_, 2);
                        v_head_2039_ = leanh::lean_ctor_get(v_a_2035_, 0);
                        leanh::lean_inc(v_head_2039_);
                        v_tail_2040_ = leanh::lean_ctor_get(v_a_2035_, 1);
                        leanh::lean_inc(v_tail_2040_);
                        leanh::lean_dec_ref_known(v_a_2035_, 2);
                        leanh::lean_inc(v_f_2033_);
                        v___x_2041_ =
                            leanh::lean_apply_2(v_f_2033_, v_head_2037_, v_head_2039_);
                        v___x_2042_ = lean_array_push(v_a_2036_, v___x_2041_);
                        v_a_2034_ = v_tail_2038_;
                        v_a_2035_ = v_tail_2040_;
                        v_a_2036_ = v___x_2042_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_a_2034_, 2);
                        leanh::lean_dec(v_a_2035_);
                        leanh::lean_dec(v_f_2033_);
                        v___x_2044_ = lean_array_to_list(v_a_2036_);
                        return v___x_2044_;
                    }
                } else {
                    leanh::lean_dec(v_a_2035_);
                    leanh::lean_dec(v_a_2034_);
                    leanh::lean_dec(v_f_2033_);
                    v___x_2045_ = lean_array_to_list(v_a_2036_);
                    return v___x_2045_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
    mut v_00_u03b1_2046_: *mut leanh::LeanObject,
    mut v_00_u03b2_2047_: *mut leanh::LeanObject,
    mut v_00_u03b3_2048_: *mut leanh::LeanObject,
    mut v_f_2049_: *mut leanh::LeanObject,
    mut v_a_2050_: *mut leanh::LeanObject,
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
        v_f_2049_, v_a_2050_, v_a_2051_, v_a_2052_,
    );
    return v___x_2053_;
}
pub unsafe fn l_List_zipWithTR___redArg(
    mut v_f_2054_: *mut leanh::LeanObject,
    mut v_as_2055_: *mut leanh::LeanObject,
    mut v_bs_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2059_: *mut leanh::LeanObject,
    mut v_00_u03b2_2060_: *mut leanh::LeanObject,
    mut v_00_u03b3_2061_: *mut leanh::LeanObject,
    mut v_f_2062_: *mut leanh::LeanObject,
    mut v_as_2063_: *mut leanh::LeanObject,
    mut v_bs_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_x_2068_: *mut leanh::LeanObject,
    mut v_x_2069_: *mut leanh::LeanObject,
    mut v_h__1_2070_: *mut leanh::LeanObject,
    mut v_h__2_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2067_) == 1 {
        if leanh::lean_obj_tag(v_x_2068_) == 1 {
            let mut v_head_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2071_);
            v_head_2072_ = leanh::lean_ctor_get(v_x_2067_, 0);
            leanh::lean_inc(v_head_2072_);
            v_tail_2073_ = leanh::lean_ctor_get(v_x_2067_, 1);
            leanh::lean_inc(v_tail_2073_);
            leanh::lean_dec_ref_known(v_x_2067_, 2);
            v_head_2074_ = leanh::lean_ctor_get(v_x_2068_, 0);
            leanh::lean_inc(v_head_2074_);
            v_tail_2075_ = leanh::lean_ctor_get(v_x_2068_, 1);
            leanh::lean_inc(v_tail_2075_);
            leanh::lean_dec_ref_known(v_x_2068_, 2);
            v___x_2076_ = leanh::lean_apply_5(
                v_h__1_2070_,
                v_head_2072_,
                v_tail_2073_,
                v_head_2074_,
                v_tail_2075_,
                v_x_2069_,
            );
            return v___x_2076_;
        } else {
            let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_2070_);
            v___x_2077_ = leanh::lean_apply_4(
                v_h__2_2071_,
                v_x_2067_,
                v_x_2068_,
                v_x_2069_,
                leanh::lean_box(0),
            );
            return v___x_2077_;
        }
    } else {
        let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2070_);
        v___x_2078_ = leanh::lean_apply_4(
            v_h__2_2071_,
            v_x_2067_,
            v_x_2068_,
            v_x_2069_,
            leanh::lean_box(0),
        );
        return v___x_2078_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(
    mut v_00_u03b1_2079_: *mut leanh::LeanObject,
    mut v_00_u03b2_2080_: *mut leanh::LeanObject,
    mut v_00_u03b3_2081_: *mut leanh::LeanObject,
    mut v_motive_2082_: *mut leanh::LeanObject,
    mut v_x_2083_: *mut leanh::LeanObject,
    mut v_x_2084_: *mut leanh::LeanObject,
    mut v_x_2085_: *mut leanh::LeanObject,
    mut v_h__1_2086_: *mut leanh::LeanObject,
    mut v_h__2_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2083_) == 1 {
        if leanh::lean_obj_tag(v_x_2084_) == 1 {
            let mut v_head_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2087_);
            v_head_2088_ = leanh::lean_ctor_get(v_x_2083_, 0);
            leanh::lean_inc(v_head_2088_);
            v_tail_2089_ = leanh::lean_ctor_get(v_x_2083_, 1);
            leanh::lean_inc(v_tail_2089_);
            leanh::lean_dec_ref_known(v_x_2083_, 2);
            v_head_2090_ = leanh::lean_ctor_get(v_x_2084_, 0);
            leanh::lean_inc(v_head_2090_);
            v_tail_2091_ = leanh::lean_ctor_get(v_x_2084_, 1);
            leanh::lean_inc(v_tail_2091_);
            leanh::lean_dec_ref_known(v_x_2084_, 2);
            v___x_2092_ = leanh::lean_apply_5(
                v_h__1_2086_,
                v_head_2088_,
                v_tail_2089_,
                v_head_2090_,
                v_tail_2091_,
                v_x_2085_,
            );
            return v___x_2092_;
        } else {
            let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_2086_);
            v___x_2093_ = leanh::lean_apply_4(
                v_h__2_2087_,
                v_x_2083_,
                v_x_2084_,
                v_x_2085_,
                leanh::lean_box(0),
            );
            return v___x_2093_;
        }
    } else {
        let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2086_);
        v___x_2094_ = leanh::lean_apply_4(
            v_h__2_2087_,
            v_x_2083_,
            v_x_2084_,
            v_x_2085_,
            leanh::lean_box(0),
        );
        return v___x_2094_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(
    mut v_as_2095_: *mut leanh::LeanObject,
    mut v_i_2096_: usize,
    mut v_stop_2097_: usize,
    mut v_b_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2099_: u8 = 0;
    let mut v_fst_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2099_ = lean_usize_dec_eq(v_i_2096_, v_stop_2097_);
                if v___x_2099_ == 0 {
                    v_fst_2100_ = leanh::lean_ctor_get(v_b_2098_, 0);
                    v_snd_2101_ = leanh::lean_ctor_get(v_b_2098_, 1);
                    v_isSharedCheck_2116_ = (!leanh::lean_is_exclusive(v_b_2098_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2103_ = v_b_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2101_);
                        leanh::lean_inc(v_fst_2100_);
                        leanh::lean_dec(v_b_2098_);
                        v___x_2103_ = leanh::lean_box(0);
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
                v___x_2108_ = leanh::lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_sub(v_fst_2100_, v___x_2108_);
                leanh::lean_dec(v_fst_2100_);
                leanh::lean_inc(v___x_2109_);
                leanh::lean_inc(v___x_2107_);
                if v_isShared_2104_ == 0 {
                    leanh::lean_ctor_set(v___x_2103_, 1, v___x_2109_);
                    leanh::lean_ctor_set(v___x_2103_, 0, v___x_2107_);
                    v___x_2111_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2112_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2112_, 0, v___x_2111_);
                leanh::lean_ctor_set(v___x_2112_, 1, v_snd_2101_);
                v___x_2113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2113_, 0, v___x_2109_);
                leanh::lean_ctor_set(v___x_2113_, 1, v___x_2112_);
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
    mut v_as_2117_: *mut leanh::LeanObject,
    mut v_i_2118_: *mut leanh::LeanObject,
    mut v_stop_2119_: *mut leanh::LeanObject,
    mut v_b_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2121_: usize = 0;
    let mut v_stop_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2121_ = leanh::lean_unbox_usize(v_i_2118_);
    leanh::lean_dec(v_i_2118_);
    v_stop_boxed_2122_ = leanh::lean_unbox_usize(v_stop_2119_);
    leanh::lean_dec(v_stop_2119_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2117_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2120_);
    leanh::lean_dec_ref(v_as_2117_);
    return v_res_2123_;
}
pub unsafe fn l_List_zipIdxTR___redArg(
    mut v_l_2124_: *mut leanh::LeanObject,
    mut v_n_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_as_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    v_as_2126_ = lean_array_mk(v_l_2124_);
    v___x_2127_ = lean_array_get_size(v_as_2126_);
    v___x_2128_ = leanh::lean_box(0);
    v___x_2129_ = leanh::lean_unsigned_to_nat(0);
    v___x_2130_ = lean_nat_dec_lt(v___x_2129_, v___x_2127_);
    if v___x_2130_ == 0 {
        leanh::lean_dec_ref(v_as_2126_);
        return v___x_2128_;
    } else {
        let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: usize = 0;
        let mut v___x_2134_: usize = 0;
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2131_ = lean_nat_add(v_n_2125_, v___x_2127_);
        v___x_2132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
        leanh::lean_ctor_set(v___x_2132_, 1, v___x_2128_);
        v___x_2133_ = lean_usize_of_nat(v___x_2127_);
        v___x_2134_ = 0usize;
        v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2126_, v___x_2133_, v___x_2134_, v___x_2132_);
        leanh::lean_dec_ref(v_as_2126_);
        v_snd_2136_ = leanh::lean_ctor_get(v___x_2135_, 1);
        leanh::lean_inc(v_snd_2136_);
        leanh::lean_dec_ref(v___x_2135_);
        return v_snd_2136_;
    }
}
pub unsafe fn l_List_zipIdxTR___redArg___boxed(
    mut v_l_2137_: *mut leanh::LeanObject,
    mut v_n_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_List_zipIdxTR___redArg(v_l_2137_, v_n_2138_);
    leanh::lean_dec(v_n_2138_);
    return v_res_2139_;
}
pub unsafe fn l_List_zipIdxTR(
    mut v_00_u03b1_2140_: *mut leanh::LeanObject,
    mut v_l_2141_: *mut leanh::LeanObject,
    mut v_n_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_List_zipIdxTR___redArg(v_l_2141_, v_n_2142_);
    return v___x_2143_;
}
pub unsafe fn l_List_zipIdxTR___boxed(
    mut v_00_u03b1_2144_: *mut leanh::LeanObject,
    mut v_l_2145_: *mut leanh::LeanObject,
    mut v_n_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_List_zipIdxTR(v_00_u03b1_2144_, v_l_2145_, v_n_2146_);
    leanh::lean_dec(v_n_2146_);
    return v_res_2147_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
    mut v_00_u03b1_2148_: *mut leanh::LeanObject,
    mut v_as_2149_: *mut leanh::LeanObject,
    mut v_i_2150_: usize,
    mut v_stop_2151_: usize,
    mut v_b_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2149_, v_i_2150_, v_stop_2151_, v_b_2152_);
    return v___x_2153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(
    mut v_00_u03b1_2154_: *mut leanh::LeanObject,
    mut v_as_2155_: *mut leanh::LeanObject,
    mut v_i_2156_: *mut leanh::LeanObject,
    mut v_stop_2157_: *mut leanh::LeanObject,
    mut v_b_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2159_: usize = 0;
    let mut v_stop_boxed_2160_: usize = 0;
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2159_ = leanh::lean_unbox_usize(v_i_2156_);
    leanh::lean_dec(v_i_2156_);
    v_stop_boxed_2160_ = leanh::lean_unbox_usize(v_stop_2157_);
    leanh::lean_dec(v_stop_2157_);
    v_res_2161_ =
        l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
            v_00_u03b1_2154_,
            v_as_2155_,
            v_i_boxed_2159_,
            v_stop_boxed_2160_,
            v_b_2158_,
        );
    leanh::lean_dec_ref(v_as_2155_);
    return v_res_2161_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_2162_: *mut leanh::LeanObject,
    mut v_x_2163_: *mut leanh::LeanObject,
    mut v_h__1_2164_: *mut leanh::LeanObject,
    mut v_h__2_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2162_) == 0 {
        let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2165_);
        v___x_2166_ = leanh::lean_apply_1(v_h__1_2164_, v_x_2163_);
        return v___x_2166_;
    } else {
        let mut v_head_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2164_);
        v_head_2167_ = leanh::lean_ctor_get(v_x_2162_, 0);
        leanh::lean_inc(v_head_2167_);
        v_tail_2168_ = leanh::lean_ctor_get(v_x_2162_, 1);
        leanh::lean_inc(v_tail_2168_);
        leanh::lean_dec_ref_known(v_x_2162_, 2);
        v___x_2169_ =
            leanh::lean_apply_3(v_h__2_2165_, v_head_2167_, v_tail_2168_, v_x_2163_);
        return v___x_2169_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_2170_: *mut leanh::LeanObject,
    mut v_motive_2171_: *mut leanh::LeanObject,
    mut v_x_2172_: *mut leanh::LeanObject,
    mut v_x_2173_: *mut leanh::LeanObject,
    mut v_h__1_2174_: *mut leanh::LeanObject,
    mut v_h__2_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2172_) == 0 {
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2175_);
        v___x_2176_ = leanh::lean_apply_1(v_h__1_2174_, v_x_2173_);
        return v___x_2176_;
    } else {
        let mut v_head_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2174_);
        v_head_2177_ = leanh::lean_ctor_get(v_x_2172_, 0);
        leanh::lean_inc(v_head_2177_);
        v_tail_2178_ = leanh::lean_ctor_get(v_x_2172_, 1);
        leanh::lean_inc(v_tail_2178_);
        leanh::lean_dec_ref_known(v_x_2172_, 2);
        v___x_2179_ =
            leanh::lean_apply_3(v_h__2_2175_, v_head_2177_, v_tail_2178_, v_x_2173_);
        return v___x_2179_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
    mut v_sep_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2182_) == 0 {
                    v___x_2184_ = lean_array_get_size(v_a_2183_);
                    v___x_2185_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v___x_2184_);
                    if v___x_2186_ == 0 {
                        leanh::lean_dec_ref(v_a_2183_);
                        return v_a_2181_;
                    } else {
                        v___x_2187_ = lean_usize_of_nat(v___x_2184_);
                        v___x_2188_ = 0usize;
                        v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_2183_, v___x_2187_, v___x_2188_, v_a_2181_);
                        leanh::lean_dec_ref(v_a_2183_);
                        return v___x_2189_;
                    }
                } else {
                    v_head_2190_ = leanh::lean_ctor_get(v_a_2182_, 0);
                    leanh::lean_inc(v_head_2190_);
                    v_tail_2191_ = leanh::lean_ctor_get(v_a_2182_, 1);
                    leanh::lean_inc(v_tail_2191_);
                    leanh::lean_dec_ref_known(v_a_2182_, 2);
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
    mut v_sep_2195_: *mut leanh::LeanObject,
    mut v_a_2196_: *mut leanh::LeanObject,
    mut v_a_2197_: *mut leanh::LeanObject,
    mut v_a_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2195_,
        v_a_2196_,
        v_a_2197_,
        v_a_2198_,
    );
    leanh::lean_dec_ref(v_sep_2195_);
    return v_res_2199_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
    mut v_00_u03b1_2200_: *mut leanh::LeanObject,
    mut v_sep_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
    mut v_a_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
    );
    return v___x_2205_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(
    mut v_00_u03b1_2206_: *mut leanh::LeanObject,
    mut v_sep_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
    mut v_a_2209_: *mut leanh::LeanObject,
    mut v_a_2210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2211_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
        v_00_u03b1_2206_,
        v_sep_2207_,
        v_a_2208_,
        v_a_2209_,
        v_a_2210_,
    );
    leanh::lean_dec_ref(v_sep_2207_);
    return v_res_2211_;
}
pub unsafe fn l_List_intercalateTR___redArg(
    mut v_sep_2212_: *mut leanh::LeanObject,
    mut v_x_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2213_) == 0 {
        let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_sep_2212_);
        v___x_2214_ = leanh::lean_box(0);
        return v___x_2214_;
    } else {
        let mut v_tail_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2215_ = leanh::lean_ctor_get(v_x_2213_, 1);
        if leanh::lean_obj_tag(v_tail_2215_) == 0 {
            let mut v_head_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_sep_2212_);
            v_head_2216_ = leanh::lean_ctor_get(v_x_2213_, 0);
            leanh::lean_inc(v_head_2216_);
            leanh::lean_dec_ref_known(v_x_2213_, 2);
            return v_head_2216_;
        } else {
            let mut v_head_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2215_);
            v_head_2217_ = leanh::lean_ctor_get(v_x_2213_, 0);
            leanh::lean_inc(v_head_2217_);
            leanh::lean_dec_ref_known(v_x_2213_, 2);
            v___x_2218_ = lean_array_mk(v_sep_2212_);
            v___x_2219_ = l_List_setTR___redArg___closed__0;
            v___x_2220_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
                v___x_2218_,
                v_head_2217_,
                v_tail_2215_,
                v___x_2219_,
            );
            leanh::lean_dec_ref(v___x_2218_);
            return v___x_2220_;
        }
    }
}
pub unsafe fn l_List_intercalateTR(
    mut v_00_u03b1_2221_: *mut leanh::LeanObject,
    mut v_sep_2222_: *mut leanh::LeanObject,
    mut v_x_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_List_intercalateTR___redArg(v_sep_2222_, v_x_2223_);
    return v___x_2224_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(
    mut v_x_2225_: *mut leanh::LeanObject,
    mut v_h__1_2226_: *mut leanh::LeanObject,
    mut v_h__2_2227_: *mut leanh::LeanObject,
    mut v_h__3_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2225_) == 0 {
        let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_2228_);
        leanh::lean_dec(v_h__2_2227_);
        v___x_2229_ = leanh::lean_box(0);
        v___x_2230_ = leanh::lean_apply_1(v_h__1_2226_, v___x_2229_);
        return v___x_2230_;
    } else {
        let mut v_tail_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2226_);
        v_tail_2231_ = leanh::lean_ctor_get(v_x_2225_, 1);
        if leanh::lean_obj_tag(v_tail_2231_) == 0 {
            let mut v_head_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2228_);
            v_head_2232_ = leanh::lean_ctor_get(v_x_2225_, 0);
            leanh::lean_inc(v_head_2232_);
            leanh::lean_dec_ref_known(v_x_2225_, 2);
            v___x_2233_ = leanh::lean_apply_1(v_h__2_2227_, v_head_2232_);
            return v___x_2233_;
        } else {
            let mut v_head_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2231_);
            leanh::lean_dec(v_h__2_2227_);
            v_head_2234_ = leanh::lean_ctor_get(v_x_2225_, 0);
            leanh::lean_inc(v_head_2234_);
            leanh::lean_dec_ref_known(v_x_2225_, 2);
            v___x_2235_ = leanh::lean_apply_3(
                v_h__3_2228_,
                v_head_2234_,
                v_tail_2231_,
                leanh::lean_box(0),
            );
            return v___x_2235_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(
    mut v_00_u03b1_2236_: *mut leanh::LeanObject,
    mut v_motive_2237_: *mut leanh::LeanObject,
    mut v_x_2238_: *mut leanh::LeanObject,
    mut v_h__1_2239_: *mut leanh::LeanObject,
    mut v_h__2_2240_: *mut leanh::LeanObject,
    mut v_h__3_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2238_) == 0 {
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_2241_);
        leanh::lean_dec(v_h__2_2240_);
        v___x_2242_ = leanh::lean_box(0);
        v___x_2243_ = leanh::lean_apply_1(v_h__1_2239_, v___x_2242_);
        return v___x_2243_;
    } else {
        let mut v_tail_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2239_);
        v_tail_2244_ = leanh::lean_ctor_get(v_x_2238_, 1);
        if leanh::lean_obj_tag(v_tail_2244_) == 0 {
            let mut v_head_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2241_);
            v_head_2245_ = leanh::lean_ctor_get(v_x_2238_, 0);
            leanh::lean_inc(v_head_2245_);
            leanh::lean_dec_ref_known(v_x_2238_, 2);
            v___x_2246_ = leanh::lean_apply_1(v_h__2_2240_, v_head_2245_);
            return v___x_2246_;
        } else {
            let mut v_head_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2244_);
            leanh::lean_dec(v_h__2_2240_);
            v_head_2247_ = leanh::lean_ctor_get(v_x_2238_, 0);
            leanh::lean_inc(v_head_2247_);
            leanh::lean_dec_ref_known(v_x_2238_, 2);
            v___x_2248_ = leanh::lean_apply_3(
                v_h__3_2241_,
                v_head_2247_,
                v_tail_2244_,
                leanh::lean_box(0),
            );
            return v___x_2248_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(
    mut v_x_2249_: *mut leanh::LeanObject,
    mut v_x_2250_: *mut leanh::LeanObject,
    mut v_x_2251_: *mut leanh::LeanObject,
    mut v_h__1_2252_: *mut leanh::LeanObject,
    mut v_h__2_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2250_) == 0 {
        let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2253_);
        v___x_2254_ = leanh::lean_apply_2(v_h__1_2252_, v_x_2249_, v_x_2251_);
        return v___x_2254_;
    } else {
        let mut v_head_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2252_);
        v_head_2255_ = leanh::lean_ctor_get(v_x_2250_, 0);
        leanh::lean_inc(v_head_2255_);
        v_tail_2256_ = leanh::lean_ctor_get(v_x_2250_, 1);
        leanh::lean_inc(v_tail_2256_);
        leanh::lean_dec_ref_known(v_x_2250_, 2);
        v___x_2257_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_2258_: *mut leanh::LeanObject,
    mut v_motive_2259_: *mut leanh::LeanObject,
    mut v_x_2260_: *mut leanh::LeanObject,
    mut v_x_2261_: *mut leanh::LeanObject,
    mut v_x_2262_: *mut leanh::LeanObject,
    mut v_h__1_2263_: *mut leanh::LeanObject,
    mut v_h__2_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2261_) == 0 {
        let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2264_);
        v___x_2265_ = leanh::lean_apply_2(v_h__1_2263_, v_x_2260_, v_x_2262_);
        return v___x_2265_;
    } else {
        let mut v_head_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2263_);
        v_head_2266_ = leanh::lean_ctor_get(v_x_2261_, 0);
        leanh::lean_inc(v_head_2266_);
        v_tail_2267_ = leanh::lean_ctor_get(v_x_2261_, 1);
        leanh::lean_inc(v_tail_2267_);
        leanh::lean_dec_ref_known(v_x_2261_, 2);
        v___x_2268_ = leanh::lean_apply_4(
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
pub unsafe fn runtime_initialize_Init_Data_List_Impl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Impl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Impl(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Impl(builtin);
}