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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_List_setTR___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_List_setTR___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_setTR___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_reduceOption___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_List_reduceOption___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_reduceOption___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_List_foldrTR___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_List_foldrTR___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_List_foldrTR___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value) as *mut LeanObject;
pub static l_List_foldrTR___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_foldrTR___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_List_foldrTR___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_List_foldrTR___redArg___closed__9_value) as *mut LeanObject;
pub static l_List_flattenTR___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_List_flattenTR___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_flattenTR___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(
    mut v_as_1135_: *mut LeanObject,
    mut v_i_1136_: usize,
    mut v_stop_1137_: usize,
    mut v_b_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: usize = 0;
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
                if v___x_1139_ == 0 {
                    v___x_1140_ = 1usize;
                    v___x_1141_ = lean_usize_sub(v_i_1136_, v___x_1140_);
                    v___x_1142_ = lean_array_uget_borrowed(v_as_1135_, v___x_1141_);
                    lean_inc(v___x_1142_);
                    v___x_1143_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    lean_ctor_set(v___x_1143_, 1, v_b_1138_);
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
    mut v_as_1145_: *mut LeanObject,
    mut v_i_1146_: *mut LeanObject,
    mut v_stop_1147_: *mut LeanObject,
    mut v_b_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1149_: usize = 0;
    let mut v_stop_boxed_1150_: usize = 0;
    let mut v_res_1151_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1149_ = lean_unbox_usize(v_i_1146_);
    lean_dec(v_i_1146_);
    v_stop_boxed_1150_ = lean_unbox_usize(v_stop_1147_);
    lean_dec(v_stop_1147_);
    v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1145_, v_i_boxed_1149_, v_stop_boxed_1150_, v_b_1148_);
    lean_dec_ref(v_as_1145_);
    return v_res_1151_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
    mut v_l_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_a_1155_: *mut LeanObject,
    mut v_a_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_zero_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1163_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: usize = 0;
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1154_) == 0 {
                    lean_dec_ref(v_a_1156_);
                    lean_dec(v_a_1155_);
                    lean_dec(v_a_1153_);
                    lean_inc(v_l_1152_);
                    return v_l_1152_;
                } else {
                    v_head_1157_ = lean_ctor_get(v_a_1154_, 0);
                    v_tail_1158_ = lean_ctor_get(v_a_1154_, 1);
                    v_isSharedCheck_1176_ = (!lean_is_exclusive(v_a_1154_)) as u8;
                    if v_isSharedCheck_1176_ == 0 {
                        v___x_1160_ = v_a_1154_;
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1158_);
                        lean_inc(v_head_1157_);
                        lean_dec(v_a_1154_);
                        v___x_1160_ = lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1162_ = lean_unsigned_to_nat(0);
                v_isZero_1163_ = lean_nat_dec_eq(v_a_1155_, v_zero_1162_);
                if v_isZero_1163_ == 1 {
                    lean_dec(v_head_1157_);
                    lean_dec(v_a_1155_);
                    if v_isShared_1161_ == 0 {
                        lean_ctor_set(v___x_1160_, 0, v_a_1153_);
                        v___x_1165_ = v___x_1160_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1153_);
                        lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_tail_1158_);
                        v___x_1165_ = v_reuseFailAlloc_1171_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1160_);
                    v_one_1172_ = lean_unsigned_to_nat(1);
                    v_n_1173_ = lean_nat_sub(v_a_1155_, v_one_1172_);
                    lean_dec(v_a_1155_);
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
                    lean_dec_ref(v_a_1156_);
                    return v___x_1165_;
                } else {
                    v___x_1168_ = lean_usize_of_nat(v___x_1166_);
                    v___x_1169_ = 0usize;
                    v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1156_, v___x_1168_, v___x_1169_, v___x_1165_);
                    lean_dec_ref(v_a_1156_);
                    return v___x_1170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(
    mut v_l_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
    mut v_a_1179_: *mut LeanObject,
    mut v_a_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1182_: *mut LeanObject = core::ptr::null_mut();
    v_res_1182_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_,
    );
    lean_dec(v_l_1177_);
    return v_res_1182_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go(
    mut v_00_u03b1_1183_: *mut LeanObject,
    mut v_l_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    v___x_1189_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_,
    );
    return v___x_1189_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(
    mut v_00_u03b1_1190_: *mut LeanObject,
    mut v_l_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
    mut v_a_1193_: *mut LeanObject,
    mut v_a_1194_: *mut LeanObject,
    mut v_a_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1196_: *mut LeanObject = core::ptr::null_mut();
    v_res_1196_ = l___private_Init_Data_List_Impl_0__List_setTR_go(
        v_00_u03b1_1190_,
        v_l_1191_,
        v_a_1192_,
        v_a_1193_,
        v_a_1194_,
        v_a_1195_,
    );
    lean_dec(v_l_1191_);
    return v_res_1196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(
    mut v_00_u03b1_1197_: *mut LeanObject,
    mut v_as_1198_: *mut LeanObject,
    mut v_i_1199_: usize,
    mut v_stop_1200_: usize,
    mut v_b_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1198_, v_i_1199_, v_stop_1200_, v_b_1201_);
    return v___x_1202_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(
    mut v_00_u03b1_1203_: *mut LeanObject,
    mut v_as_1204_: *mut LeanObject,
    mut v_i_1205_: *mut LeanObject,
    mut v_stop_1206_: *mut LeanObject,
    mut v_b_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1208_: usize = 0;
    let mut v_stop_boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1208_ = lean_unbox_usize(v_i_1205_);
    lean_dec(v_i_1205_);
    v_stop_boxed_1209_ = lean_unbox_usize(v_stop_1206_);
    lean_dec(v_stop_1206_);
    v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(v_00_u03b1_1203_, v_as_1204_, v_i_boxed_1208_, v_stop_boxed_1209_, v_b_1207_);
    lean_dec_ref(v_as_1204_);
    return v_res_1210_;
}
pub unsafe fn l_List_setTR___redArg(
    mut v_l_1213_: *mut LeanObject,
    mut v_n_1214_: *mut LeanObject,
    mut v_a_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1213_);
    v___x_1217_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1213_,
        v_a_1215_,
        v_l_1213_,
        v_n_1214_,
        v___x_1216_,
    );
    lean_dec(v_l_1213_);
    return v___x_1217_;
}
pub unsafe fn l_List_setTR(
    mut v_00_u03b1_1218_: *mut LeanObject,
    mut v_l_1219_: *mut LeanObject,
    mut v_n_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1219_);
    v___x_1223_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(
        v_l_1219_,
        v_a_1221_,
        v_l_1219_,
        v_n_1220_,
        v___x_1222_,
    );
    lean_dec(v_l_1219_);
    return v___x_1223_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(
    mut v_x_1224_: *mut LeanObject,
    mut v_x_1225_: *mut LeanObject,
    mut v_x_1226_: *mut LeanObject,
    mut v_h__1_1227_: *mut LeanObject,
    mut v_h__2_1228_: *mut LeanObject,
    mut v_h__3_1229_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1224_) == 0 {
        let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1229_);
        lean_dec(v_h__2_1228_);
        v___x_1230_ = lean_apply_2(v_h__1_1227_, v_x_1225_, v_x_1226_);
        return v___x_1230_;
    } else {
        let mut v_head_1231_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1232_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_1233_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1234_: u8 = 0;
        lean_dec(v_h__1_1227_);
        v_head_1231_ = lean_ctor_get(v_x_1224_, 0);
        lean_inc(v_head_1231_);
        v_tail_1232_ = lean_ctor_get(v_x_1224_, 1);
        lean_inc(v_tail_1232_);
        lean_dec_ref_known(v_x_1224_, 2);
        v_zero_1233_ = lean_unsigned_to_nat(0);
        v_isZero_1234_ = lean_nat_dec_eq(v_x_1225_, v_zero_1233_);
        if v_isZero_1234_ == 1 {
            let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1229_);
            lean_dec(v_x_1225_);
            v___x_1235_ = lean_apply_3(v_h__2_1228_, v_head_1231_, v_tail_1232_, v_x_1226_);
            return v___x_1235_;
        } else {
            let mut v_one_1236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1228_);
            v_one_1236_ = lean_unsigned_to_nat(1);
            v_n_1237_ = lean_nat_sub(v_x_1225_, v_one_1236_);
            lean_dec(v_x_1225_);
            v___x_1238_ = lean_apply_4(
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
    mut v_00_u03b1_1239_: *mut LeanObject,
    mut v_motive_1240_: *mut LeanObject,
    mut v_x_1241_: *mut LeanObject,
    mut v_x_1242_: *mut LeanObject,
    mut v_x_1243_: *mut LeanObject,
    mut v_h__1_1244_: *mut LeanObject,
    mut v_h__2_1245_: *mut LeanObject,
    mut v_h__3_1246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1241_) == 0 {
        let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1246_);
        lean_dec(v_h__2_1245_);
        v___x_1247_ = lean_apply_2(v_h__1_1244_, v_x_1242_, v_x_1243_);
        return v___x_1247_;
    } else {
        let mut v_head_1248_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1249_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_1250_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1251_: u8 = 0;
        lean_dec(v_h__1_1244_);
        v_head_1248_ = lean_ctor_get(v_x_1241_, 0);
        lean_inc(v_head_1248_);
        v_tail_1249_ = lean_ctor_get(v_x_1241_, 1);
        lean_inc(v_tail_1249_);
        lean_dec_ref_known(v_x_1241_, 2);
        v_zero_1250_ = lean_unsigned_to_nat(0);
        v_isZero_1251_ = lean_nat_dec_eq(v_x_1242_, v_zero_1250_);
        if v_isZero_1251_ == 1 {
            let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1246_);
            lean_dec(v_x_1242_);
            v___x_1252_ = lean_apply_3(v_h__2_1245_, v_head_1248_, v_tail_1249_, v_x_1243_);
            return v___x_1252_;
        } else {
            let mut v_one_1253_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1245_);
            v_one_1253_ = lean_unsigned_to_nat(1);
            v_n_1254_ = lean_nat_sub(v_x_1242_, v_one_1253_);
            lean_dec(v_x_1242_);
            v___x_1255_ = lean_apply_4(
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
    mut v_f_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1257_) == 0 {
                    lean_dec_ref(v_f_1256_);
                    v___x_1259_ = lean_array_to_list(v_a_1258_);
                    return v___x_1259_;
                } else {
                    v_head_1260_ = lean_ctor_get(v_a_1257_, 0);
                    lean_inc(v_head_1260_);
                    v_tail_1261_ = lean_ctor_get(v_a_1257_, 1);
                    lean_inc(v_tail_1261_);
                    lean_dec_ref_known(v_a_1257_, 2);
                    lean_inc_ref(v_f_1256_);
                    v___x_1262_ = lean_apply_1(v_f_1256_, v_head_1260_);
                    if lean_obj_tag(v___x_1262_) == 0 {
                        v_a_1257_ = v_tail_1261_;
                        state = 0;
                        continue;
                    } else {
                        v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
                        lean_inc(v_val_1264_);
                        lean_dec_ref_known(v___x_1262_, 1);
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
    mut v_00_u03b1_1267_: *mut LeanObject,
    mut v_00_u03b2_1268_: *mut LeanObject,
    mut v_f_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_List_filterMapTR_go___redArg(v_f_1269_, v_a_1270_, v_a_1271_);
    return v___x_1272_;
}
pub unsafe fn l_List_filterMapTR___redArg(
    mut v_f_1273_: *mut LeanObject,
    mut v_l_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = l_List_setTR___redArg___closed__0;
    v___x_1276_ = l_List_filterMapTR_go___redArg(v_f_1273_, v_l_1274_, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn l_List_filterMapTR(
    mut v_00_u03b1_1277_: *mut LeanObject,
    mut v_00_u03b2_1278_: *mut LeanObject,
    mut v_f_1279_: *mut LeanObject,
    mut v_l_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_List_setTR___redArg___closed__0;
    v___x_1282_ = l_List_filterMapTR_go___redArg(v_f_1279_, v_l_1280_, v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(
    mut v_x_1283_: *mut LeanObject,
    mut v_x_1284_: *mut LeanObject,
    mut v_h__1_1285_: *mut LeanObject,
    mut v_h__2_1286_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1283_) == 0 {
        let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1286_);
        v___x_1287_ = lean_apply_1(v_h__1_1285_, v_x_1284_);
        return v___x_1287_;
    } else {
        let mut v_head_1288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1285_);
        v_head_1288_ = lean_ctor_get(v_x_1283_, 0);
        lean_inc(v_head_1288_);
        v_tail_1289_ = lean_ctor_get(v_x_1283_, 1);
        lean_inc(v_tail_1289_);
        lean_dec_ref_known(v_x_1283_, 2);
        v___x_1290_ = lean_apply_3(v_h__2_1286_, v_head_1288_, v_tail_1289_, v_x_1284_);
        return v___x_1290_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(
    mut v_00_u03b1_1291_: *mut LeanObject,
    mut v_00_u03b2_1292_: *mut LeanObject,
    mut v_motive_1293_: *mut LeanObject,
    mut v_x_1294_: *mut LeanObject,
    mut v_x_1295_: *mut LeanObject,
    mut v_h__1_1296_: *mut LeanObject,
    mut v_h__2_1297_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1294_) == 0 {
        let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1297_);
        v___x_1298_ = lean_apply_1(v_h__1_1296_, v_x_1295_);
        return v___x_1298_;
    } else {
        let mut v_head_1299_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1296_);
        v_head_1299_ = lean_ctor_get(v_x_1294_, 0);
        lean_inc(v_head_1299_);
        v_tail_1300_ = lean_ctor_get(v_x_1294_, 1);
        lean_inc(v_tail_1300_);
        lean_dec_ref_known(v_x_1294_, 2);
        v___x_1301_ = lean_apply_3(v_h__2_1297_, v_head_1299_, v_tail_1300_, v_x_1295_);
        return v___x_1301_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(
    mut v_x_1302_: *mut LeanObject,
    mut v_h__1_1303_: *mut LeanObject,
    mut v_h__2_1304_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1302_) == 0 {
        let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1304_);
        v___x_1305_ = lean_box(0);
        v___x_1306_ = lean_apply_1(v_h__1_1303_, v___x_1305_);
        return v___x_1306_;
    } else {
        let mut v_val_1307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1303_);
        v_val_1307_ = lean_ctor_get(v_x_1302_, 0);
        lean_inc(v_val_1307_);
        lean_dec_ref_known(v_x_1302_, 1);
        v___x_1308_ = lean_apply_1(v_h__2_1304_, v_val_1307_);
        return v___x_1308_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(
    mut v_00_u03b2_1309_: *mut LeanObject,
    mut v_motive_1310_: *mut LeanObject,
    mut v_x_1311_: *mut LeanObject,
    mut v_h__1_1312_: *mut LeanObject,
    mut v_h__2_1313_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1311_) == 0 {
        let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1313_);
        v___x_1314_ = lean_box(0);
        v___x_1315_ = lean_apply_1(v_h__1_1312_, v___x_1314_);
        return v___x_1315_;
    } else {
        let mut v_val_1316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1312_);
        v_val_1316_ = lean_ctor_get(v_x_1311_, 0);
        lean_inc(v_val_1316_);
        lean_dec_ref_known(v_x_1311_, 1);
        v___x_1317_ = lean_apply_1(v_h__2_1313_, v_val_1316_);
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_1318_: *mut LeanObject,
    mut v_h__1_1319_: *mut LeanObject,
    mut v_h__2_1320_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1318_) == 0 {
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1320_);
        v___x_1321_ = lean_box(0);
        v___x_1322_ = lean_apply_1(v_h__1_1319_, v___x_1321_);
        return v___x_1322_;
    } else {
        let mut v_val_1323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1319_);
        v_val_1323_ = lean_ctor_get(v_x_1318_, 0);
        lean_inc(v_val_1323_);
        lean_dec_ref_known(v_x_1318_, 1);
        v___x_1324_ = lean_apply_1(v_h__2_1320_, v_val_1323_);
        return v___x_1324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_1325_: *mut LeanObject,
    mut v_motive_1326_: *mut LeanObject,
    mut v_x_1327_: *mut LeanObject,
    mut v_h__1_1328_: *mut LeanObject,
    mut v_h__2_1329_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1327_) == 0 {
        let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1329_);
        v___x_1330_ = lean_box(0);
        v___x_1331_ = lean_apply_1(v_h__1_1328_, v___x_1330_);
        return v___x_1331_;
    } else {
        let mut v_val_1332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1328_);
        v_val_1332_ = lean_ctor_get(v_x_1327_, 0);
        lean_inc(v_val_1332_);
        lean_dec_ref_known(v_x_1327_, 1);
        v___x_1333_ = lean_apply_1(v_h__2_1329_, v_val_1332_);
        return v___x_1333_;
    }
}
pub unsafe fn l_List_reduceOption___redArg(mut v_a_1335_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_List_reduceOption___redArg___closed__0;
    v___x_1337_ = l_List_setTR___redArg___closed__0;
    v___x_1338_ = l_List_filterMapTR_go___redArg(v___x_1336_, v_a_1335_, v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_List_reduceOption(
    mut v_00_u03b1_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1341_ = l_List_reduceOption___redArg___closed__0;
    v___x_1342_ = l_List_setTR___redArg___closed__0;
    v___x_1343_ = l_List_filterMapTR_go___redArg(v___x_1341_, v_a_1340_, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_List_foldrTR___redArg___lam__0(
    mut v_f_1344_: *mut LeanObject,
    mut v_x1_1345_: *mut LeanObject,
    mut v_x2_1346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_apply_2(v_f_1344_, v_x1_1345_, v_x2_1346_);
    return v___x_1347_;
}
pub unsafe fn l_List_foldrTR___redArg(
    mut v_f_1367_: *mut LeanObject,
    mut v_init_1368_: *mut LeanObject,
    mut v_l_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    v___x_1370_ = lean_array_mk(v_l_1369_);
    v___x_1371_ = lean_array_get_size(v___x_1370_);
    v___x_1372_ = lean_unsigned_to_nat(0);
    v___x_1373_ = l_List_foldrTR___redArg___closed__9;
    v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1371_);
    if v___x_1374_ == 0 {
        lean_dec_ref(v___x_1370_);
        lean_dec(v_f_1367_);
        return v_init_1368_;
    } else {
        let mut v___f_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: usize = 0;
        let mut v___x_1377_: usize = 0;
        let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
        v___f_1375_ = lean_alloc_closure(
            l_List_foldrTR___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_1375_, 0, v_f_1367_);
        v___x_1376_ = lean_usize_of_nat(v___x_1371_);
        v___x_1377_ = 0usize;
        v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            lean_box(0),
            lean_box(0),
            lean_box(0),
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
    mut v_00_u03b1_1379_: *mut LeanObject,
    mut v_00_u03b2_1380_: *mut LeanObject,
    mut v_f_1381_: *mut LeanObject,
    mut v_init_1382_: *mut LeanObject,
    mut v_l_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_List_foldrTR___redArg(v_f_1381_, v_init_1382_, v_l_1383_);
    return v___x_1384_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
    mut v_f_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1386_) == 0 {
                    lean_dec_ref(v_f_1385_);
                    v___x_1388_ = lean_array_to_list(v_a_1387_);
                    return v___x_1388_;
                } else {
                    v_head_1389_ = lean_ctor_get(v_a_1386_, 0);
                    lean_inc(v_head_1389_);
                    v_tail_1390_ = lean_ctor_get(v_a_1386_, 1);
                    lean_inc(v_tail_1390_);
                    lean_dec_ref_known(v_a_1386_, 2);
                    lean_inc_ref(v_f_1385_);
                    v___x_1391_ = lean_apply_1(v_f_1385_, v_head_1389_);
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
    mut v_00_u03b1_1394_: *mut LeanObject,
    mut v_00_u03b2_1395_: *mut LeanObject,
    mut v_f_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1396_, v_a_1397_, v_a_1398_,
    );
    return v___x_1399_;
}
pub unsafe fn l_List_flatMapTR___redArg(
    mut v_f_1400_: *mut LeanObject,
    mut v_as_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_List_setTR___redArg___closed__0;
    v___x_1403_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1400_,
        v_as_1401_,
        v___x_1402_,
    );
    return v___x_1403_;
}
pub unsafe fn l_List_flatMapTR(
    mut v_00_u03b1_1404_: *mut LeanObject,
    mut v_00_u03b2_1405_: *mut LeanObject,
    mut v_f_1406_: *mut LeanObject,
    mut v_as_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1408_ = l_List_setTR___redArg___closed__0;
    v___x_1409_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(
        v_f_1406_,
        v_as_1407_,
        v___x_1408_,
    );
    return v___x_1409_;
}
pub unsafe fn l_List_flattenTR___redArg(mut v_l_1411_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1415_: *mut LeanObject,
    mut v_l_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_l_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
    mut v_a_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1427_: u8 = 0;
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1421_) == 0 {
                    lean_dec_ref(v_a_1423_);
                    lean_dec(v_a_1422_);
                    lean_inc(v_l_1420_);
                    return v_l_1420_;
                } else {
                    v_head_1424_ = lean_ctor_get(v_a_1421_, 0);
                    lean_inc(v_head_1424_);
                    v_tail_1425_ = lean_ctor_get(v_a_1421_, 1);
                    lean_inc(v_tail_1425_);
                    lean_dec_ref_known(v_a_1421_, 2);
                    v_zero_1426_ = lean_unsigned_to_nat(0);
                    v_isZero_1427_ = lean_nat_dec_eq(v_a_1422_, v_zero_1426_);
                    if v_isZero_1427_ == 1 {
                        lean_dec(v_tail_1425_);
                        lean_dec(v_head_1424_);
                        lean_dec(v_a_1422_);
                        v___x_1428_ = lean_array_to_list(v_a_1423_);
                        return v___x_1428_;
                    } else {
                        v_one_1429_ = lean_unsigned_to_nat(1);
                        v_n_1430_ = lean_nat_sub(v_a_1422_, v_one_1429_);
                        lean_dec(v_a_1422_);
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
    mut v_l_1433_: *mut LeanObject,
    mut v_a_1434_: *mut LeanObject,
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1433_, v_a_1434_, v_a_1435_, v_a_1436_,
    );
    lean_dec(v_l_1433_);
    return v_res_1437_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go(
    mut v_00_u03b1_1438_: *mut LeanObject,
    mut v_l_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
    mut v_a_1441_: *mut LeanObject,
    mut v_a_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1439_, v_a_1440_, v_a_1441_, v_a_1442_,
    );
    return v___x_1443_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(
    mut v_00_u03b1_1444_: *mut LeanObject,
    mut v_l_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
    mut v_a_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1449_: *mut LeanObject = core::ptr::null_mut();
    v_res_1449_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        v_00_u03b1_1444_,
        v_l_1445_,
        v_a_1446_,
        v_a_1447_,
        v_a_1448_,
    );
    lean_dec(v_l_1445_);
    return v_res_1449_;
}
pub unsafe fn l_List_takeTR___redArg(
    mut v_n_1450_: *mut LeanObject,
    mut v_l_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1451_);
    v___x_1453_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1451_,
        v_l_1451_,
        v_n_1450_,
        v___x_1452_,
    );
    lean_dec(v_l_1451_);
    return v___x_1453_;
}
pub unsafe fn l_List_takeTR(
    mut v_00_u03b1_1454_: *mut LeanObject,
    mut v_n_1455_: *mut LeanObject,
    mut v_l_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1456_);
    v___x_1458_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(
        v_l_1456_,
        v_l_1456_,
        v_n_1455_,
        v___x_1457_,
    );
    lean_dec(v_l_1456_);
    return v___x_1458_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
    mut v_x_1459_: *mut LeanObject,
    mut v_x_1460_: *mut LeanObject,
    mut v_h__1_1461_: *mut LeanObject,
    mut v_h__2_1462_: *mut LeanObject,
    mut v_h__3_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1465_: u8 = 0;
    v_zero_1464_ = lean_unsigned_to_nat(0);
    v_isZero_1465_ = lean_nat_dec_eq(v_x_1459_, v_zero_1464_);
    if v_isZero_1465_ == 1 {
        let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1463_);
        lean_dec(v_h__2_1462_);
        v___x_1466_ = lean_apply_1(v_h__1_1461_, v_x_1460_);
        return v___x_1466_;
    } else {
        let mut v_one_1467_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1468_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1461_);
        v_one_1467_ = lean_unsigned_to_nat(1);
        v_n_1468_ = lean_nat_sub(v_x_1459_, v_one_1467_);
        if lean_obj_tag(v_x_1460_) == 0 {
            let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1463_);
            v___x_1469_ = lean_apply_1(v_h__2_1462_, v_n_1468_);
            return v___x_1469_;
        } else {
            let mut v_head_1470_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1471_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1462_);
            v_head_1470_ = lean_ctor_get(v_x_1460_, 0);
            lean_inc(v_head_1470_);
            v_tail_1471_ = lean_ctor_get(v_x_1460_, 1);
            lean_inc(v_tail_1471_);
            lean_dec_ref_known(v_x_1460_, 2);
            v___x_1472_ = lean_apply_3(v_h__3_1463_, v_n_1468_, v_head_1470_, v_tail_1471_);
            return v___x_1472_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_1473_: *mut LeanObject,
    mut v_x_1474_: *mut LeanObject,
    mut v_h__1_1475_: *mut LeanObject,
    mut v_h__2_1476_: *mut LeanObject,
    mut v_h__3_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1478_: *mut LeanObject = core::ptr::null_mut();
    v_res_1478_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(
        v_x_1473_,
        v_x_1474_,
        v_h__1_1475_,
        v_h__2_1476_,
        v_h__3_1477_,
    );
    lean_dec(v_x_1473_);
    return v_res_1478_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
    mut v_00_u03b1_1479_: *mut LeanObject,
    mut v_motive_1480_: *mut LeanObject,
    mut v_x_1481_: *mut LeanObject,
    mut v_x_1482_: *mut LeanObject,
    mut v_h__1_1483_: *mut LeanObject,
    mut v_h__2_1484_: *mut LeanObject,
    mut v_h__3_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1487_: u8 = 0;
    v_zero_1486_ = lean_unsigned_to_nat(0);
    v_isZero_1487_ = lean_nat_dec_eq(v_x_1481_, v_zero_1486_);
    if v_isZero_1487_ == 1 {
        let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1485_);
        lean_dec(v_h__2_1484_);
        v___x_1488_ = lean_apply_1(v_h__1_1483_, v_x_1482_);
        return v___x_1488_;
    } else {
        let mut v_one_1489_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1490_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1483_);
        v_one_1489_ = lean_unsigned_to_nat(1);
        v_n_1490_ = lean_nat_sub(v_x_1481_, v_one_1489_);
        if lean_obj_tag(v_x_1482_) == 0 {
            let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1485_);
            v___x_1491_ = lean_apply_1(v_h__2_1484_, v_n_1490_);
            return v___x_1491_;
        } else {
            let mut v_head_1492_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1484_);
            v_head_1492_ = lean_ctor_get(v_x_1482_, 0);
            lean_inc(v_head_1492_);
            v_tail_1493_ = lean_ctor_get(v_x_1482_, 1);
            lean_inc(v_tail_1493_);
            lean_dec_ref_known(v_x_1482_, 2);
            v___x_1494_ = lean_apply_3(v_h__3_1485_, v_n_1490_, v_head_1492_, v_tail_1493_);
            return v___x_1494_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_1495_: *mut LeanObject,
    mut v_motive_1496_: *mut LeanObject,
    mut v_x_1497_: *mut LeanObject,
    mut v_x_1498_: *mut LeanObject,
    mut v_h__1_1499_: *mut LeanObject,
    mut v_h__2_1500_: *mut LeanObject,
    mut v_h__3_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(
        v_00_u03b1_1495_,
        v_motive_1496_,
        v_x_1497_,
        v_x_1498_,
        v_h__1_1499_,
        v_h__2_1500_,
        v_h__3_1501_,
    );
    lean_dec(v_x_1497_);
    return v_res_1502_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
    mut v_p_1503_: *mut LeanObject,
    mut v_l_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1505_) == 0 {
                    lean_dec_ref(v_a_1506_);
                    lean_dec_ref(v_p_1503_);
                    lean_inc(v_l_1504_);
                    return v_l_1504_;
                } else {
                    v_head_1507_ = lean_ctor_get(v_a_1505_, 0);
                    lean_inc_n(v_head_1507_, 2);
                    v_tail_1508_ = lean_ctor_get(v_a_1505_, 1);
                    lean_inc(v_tail_1508_);
                    lean_dec_ref_known(v_a_1505_, 2);
                    lean_inc_ref(v_p_1503_);
                    v___x_1509_ = lean_apply_1(v_p_1503_, v_head_1507_);
                    v___x_1510_ = (lean_unbox(v___x_1509_) as u8);
                    if v___x_1510_ == 0 {
                        lean_dec(v_tail_1508_);
                        lean_dec(v_head_1507_);
                        lean_dec_ref(v_p_1503_);
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
    mut v_p_1514_: *mut LeanObject,
    mut v_l_1515_: *mut LeanObject,
    mut v_a_1516_: *mut LeanObject,
    mut v_a_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1514_, v_l_1515_, v_a_1516_, v_a_1517_,
    );
    lean_dec(v_l_1515_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
    mut v_00_u03b1_1519_: *mut LeanObject,
    mut v_p_1520_: *mut LeanObject,
    mut v_l_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1524_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1520_, v_l_1521_, v_a_1522_, v_a_1523_,
    );
    return v___x_1524_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(
    mut v_00_u03b1_1525_: *mut LeanObject,
    mut v_p_1526_: *mut LeanObject,
    mut v_l_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(
        v_00_u03b1_1525_,
        v_p_1526_,
        v_l_1527_,
        v_a_1528_,
        v_a_1529_,
    );
    lean_dec(v_l_1527_);
    return v_res_1530_;
}
pub unsafe fn l_List_takeWhileTR___redArg(
    mut v_p_1531_: *mut LeanObject,
    mut v_l_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1532_);
    v___x_1534_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1531_,
        v_l_1532_,
        v_l_1532_,
        v___x_1533_,
    );
    lean_dec(v_l_1532_);
    return v___x_1534_;
}
pub unsafe fn l_List_takeWhileTR(
    mut v_00_u03b1_1535_: *mut LeanObject,
    mut v_p_1536_: *mut LeanObject,
    mut v_l_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1537_);
    v___x_1539_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(
        v_p_1536_,
        v_l_1537_,
        v_l_1537_,
        v___x_1538_,
    );
    lean_dec(v_l_1537_);
    return v___x_1539_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_1540_: *mut LeanObject,
    mut v_h__1_1541_: *mut LeanObject,
    mut v_h__2_1542_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1540_) == 0 {
        let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1542_);
        v___x_1543_ = lean_box(0);
        v___x_1544_ = lean_apply_1(v_h__1_1541_, v___x_1543_);
        return v___x_1544_;
    } else {
        let mut v_head_1545_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1541_);
        v_head_1545_ = lean_ctor_get(v_x_1540_, 0);
        lean_inc(v_head_1545_);
        v_tail_1546_ = lean_ctor_get(v_x_1540_, 1);
        lean_inc(v_tail_1546_);
        lean_dec_ref_known(v_x_1540_, 2);
        v___x_1547_ = lean_apply_2(v_h__2_1542_, v_head_1545_, v_tail_1546_);
        return v___x_1547_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_1548_: *mut LeanObject,
    mut v_motive_1549_: *mut LeanObject,
    mut v_x_1550_: *mut LeanObject,
    mut v_h__1_1551_: *mut LeanObject,
    mut v_h__2_1552_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1550_) == 0 {
        let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1552_);
        v___x_1553_ = lean_box(0);
        v___x_1554_ = lean_apply_1(v_h__1_1551_, v___x_1553_);
        return v___x_1554_;
    } else {
        let mut v_head_1555_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1556_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1551_);
        v_head_1555_ = lean_ctor_get(v_x_1550_, 0);
        lean_inc(v_head_1555_);
        v_tail_1556_ = lean_ctor_get(v_x_1550_, 1);
        lean_inc(v_tail_1556_);
        lean_dec_ref_known(v_x_1550_, 2);
        v___x_1557_ = lean_apply_2(v_h__2_1552_, v_head_1555_, v_tail_1556_);
        return v___x_1557_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
    mut v_x_1558_: u8,
    mut v_h__1_1559_: *mut LeanObject,
    mut v_h__2_1560_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1558_ == 0 {
        let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1559_);
        v___x_1561_ = lean_box(0);
        v___x_1562_ = lean_apply_1(v_h__2_1560_, v___x_1561_);
        return v___x_1562_;
    } else {
        let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1560_);
        v___x_1563_ = lean_box(0);
        v___x_1564_ = lean_apply_1(v_h__1_1559_, v___x_1563_);
        return v___x_1564_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_1565_: *mut LeanObject,
    mut v_h__1_1566_: *mut LeanObject,
    mut v_h__2_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1568_: u8 = 0;
    let mut v_res_1569_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1568_ = (lean_unbox(v_x_1565_) as u8);
    v_res_1569_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_1568_,
        v_h__1_1566_,
        v_h__2_1567_,
    );
    return v_res_1569_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
    mut v_motive_1570_: *mut LeanObject,
    mut v_x_1571_: u8,
    mut v_h__1_1572_: *mut LeanObject,
    mut v_h__2_1573_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1571_ == 0 {
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1572_);
        v___x_1574_ = lean_box(0);
        v___x_1575_ = lean_apply_1(v_h__2_1573_, v___x_1574_);
        return v___x_1575_;
    } else {
        let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1573_);
        v___x_1576_ = lean_box(0);
        v___x_1577_ = lean_apply_1(v_h__1_1572_, v___x_1576_);
        return v___x_1577_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(
    mut v_motive_1578_: *mut LeanObject,
    mut v_x_1579_: *mut LeanObject,
    mut v_h__1_1580_: *mut LeanObject,
    mut v_h__2_1581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1582_ = (lean_unbox(v_x_1579_) as u8);
    v_res_1583_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(
        v_motive_1578_,
        v_x_37__boxed_1582_,
        v_h__1_1580_,
        v_h__2_1581_,
    );
    return v_res_1583_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(
    mut v_x_1584_: *mut LeanObject,
    mut v_x_1585_: *mut LeanObject,
    mut v_h__1_1586_: *mut LeanObject,
    mut v_h__2_1587_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1584_) == 0 {
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1587_);
        v___x_1588_ = lean_apply_1(v_h__1_1586_, v_x_1585_);
        return v___x_1588_;
    } else {
        let mut v_head_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1586_);
        v_head_1589_ = lean_ctor_get(v_x_1584_, 0);
        lean_inc(v_head_1589_);
        v_tail_1590_ = lean_ctor_get(v_x_1584_, 1);
        lean_inc(v_tail_1590_);
        lean_dec_ref_known(v_x_1584_, 2);
        v___x_1591_ = lean_apply_3(v_h__2_1587_, v_head_1589_, v_tail_1590_, v_x_1585_);
        return v___x_1591_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(
    mut v_00_u03b1_1592_: *mut LeanObject,
    mut v_motive_1593_: *mut LeanObject,
    mut v_x_1594_: *mut LeanObject,
    mut v_x_1595_: *mut LeanObject,
    mut v_h__1_1596_: *mut LeanObject,
    mut v_h__2_1597_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1594_) == 0 {
        let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1597_);
        v___x_1598_ = lean_apply_1(v_h__1_1596_, v_x_1595_);
        return v___x_1598_;
    } else {
        let mut v_head_1599_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1596_);
        v_head_1599_ = lean_ctor_get(v_x_1594_, 0);
        lean_inc(v_head_1599_);
        v_tail_1600_ = lean_ctor_get(v_x_1594_, 1);
        lean_inc(v_tail_1600_);
        lean_dec_ref_known(v_x_1594_, 2);
        v___x_1601_ = lean_apply_3(v_h__2_1597_, v_head_1599_, v_tail_1600_, v_x_1595_);
        return v___x_1601_;
    }
}
pub unsafe fn l_List_dropLastTR___redArg(mut v_l_1602_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_array_mk(v_l_1602_);
    v___x_1604_ = lean_array_pop(v___x_1603_);
    v___x_1605_ = lean_array_to_list(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn l_List_dropLastTR(
    mut v_00_u03b1_1606_: *mut LeanObject,
    mut v_l_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_array_mk(v_l_1607_);
    v___x_1609_ = lean_array_pop(v___x_1608_);
    v___x_1610_ = lean_array_to_list(v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(
    mut v_p_1611_: *mut LeanObject,
    mut v_x_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1612_) == 0 {
                    lean_dec_ref(v_p_1611_);
                    v___x_1613_ = lean_box(0);
                    return v___x_1613_;
                } else {
                    v_head_1614_ = lean_ctor_get(v_x_1612_, 0);
                    lean_inc_n(v_head_1614_, 2);
                    v_tail_1615_ = lean_ctor_get(v_x_1612_, 1);
                    lean_inc(v_tail_1615_);
                    lean_dec_ref_known(v_x_1612_, 2);
                    lean_inc_ref(v_p_1611_);
                    v___x_1616_ = lean_apply_1(v_p_1611_, v_head_1614_);
                    v___x_1617_ = (lean_unbox(v___x_1616_) as u8);
                    if v___x_1617_ == 0 {
                        lean_dec(v_head_1614_);
                        v_x_1612_ = v_tail_1615_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1615_);
                        lean_dec_ref(v_p_1611_);
                        v___x_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1619_, 0, v_head_1614_);
                        return v___x_1619_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findRev_x3fTR___redArg(
    mut v_p_1620_: *mut LeanObject,
    mut v_l_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_List_reverse___redArg(v_l_1621_);
    v___x_1623_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1620_, v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_List_findRev_x3fTR(
    mut v_00_u03b1_1624_: *mut LeanObject,
    mut v_p_1625_: *mut LeanObject,
    mut v_l_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_List_findRev_x3fTR___redArg(v_p_1625_, v_l_1626_);
    return v___x_1627_;
}
pub unsafe fn l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(
    mut v_00_u03b1_1628_: *mut LeanObject,
    mut v_p_1629_: *mut LeanObject,
    mut v_x_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ =
        l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_1629_, v_x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_1632_: *mut LeanObject,
    mut v_h__1_1633_: *mut LeanObject,
    mut v_h__2_1634_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1632_) == 0 {
        let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1633_);
        v___x_1635_ = lean_box(0);
        v___x_1636_ = lean_apply_1(v_h__2_1634_, v___x_1635_);
        return v___x_1636_;
    } else {
        let mut v_val_1637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1634_);
        v_val_1637_ = lean_ctor_get(v_x_1632_, 0);
        lean_inc(v_val_1637_);
        lean_dec_ref_known(v_x_1632_, 1);
        v___x_1638_ = lean_apply_1(v_h__1_1633_, v_val_1637_);
        return v___x_1638_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_1639_: *mut LeanObject,
    mut v_motive_1640_: *mut LeanObject,
    mut v_x_1641_: *mut LeanObject,
    mut v_h__1_1642_: *mut LeanObject,
    mut v_h__2_1643_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1641_) == 0 {
        let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1642_);
        v___x_1644_ = lean_box(0);
        v___x_1645_ = lean_apply_1(v_h__2_1643_, v___x_1644_);
        return v___x_1645_;
    } else {
        let mut v_val_1646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1643_);
        v_val_1646_ = lean_ctor_get(v_x_1641_, 0);
        lean_inc(v_val_1646_);
        lean_dec_ref_known(v_x_1641_, 1);
        v___x_1647_ = lean_apply_1(v_h__1_1642_, v_val_1646_);
        return v___x_1647_;
    }
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
    mut v_f_1648_: *mut LeanObject,
    mut v_x_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1649_) == 0 {
                    lean_dec_ref(v_f_1648_);
                    v___x_1650_ = lean_box(0);
                    return v___x_1650_;
                } else {
                    v_head_1651_ = lean_ctor_get(v_x_1649_, 0);
                    lean_inc(v_head_1651_);
                    v_tail_1652_ = lean_ctor_get(v_x_1649_, 1);
                    lean_inc(v_tail_1652_);
                    lean_dec_ref_known(v_x_1649_, 2);
                    lean_inc_ref(v_f_1648_);
                    v___x_1653_ = lean_apply_1(v_f_1648_, v_head_1651_);
                    if lean_obj_tag(v___x_1653_) == 0 {
                        v_x_1649_ = v_tail_1652_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_1652_);
                        lean_dec_ref(v_f_1648_);
                        return v___x_1653_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findSomeRev_x3fTR___redArg(
    mut v_f_1655_: *mut LeanObject,
    mut v_l_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ = l_List_reverse___redArg(v_l_1656_);
    v___x_1658_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(
        v_f_1655_,
        v___x_1657_,
    );
    return v___x_1658_;
}
pub unsafe fn l_List_findSomeRev_x3fTR(
    mut v_00_u03b1_1659_: *mut LeanObject,
    mut v_00_u03b2_1660_: *mut LeanObject,
    mut v_f_1661_: *mut LeanObject,
    mut v_l_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_List_findSomeRev_x3fTR___redArg(v_f_1661_, v_l_1662_);
    return v___x_1663_;
}
pub unsafe fn l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(
    mut v_00_u03b1_1664_: *mut LeanObject,
    mut v_00_u03b2_1665_: *mut LeanObject,
    mut v_f_1666_: *mut LeanObject,
    mut v_x_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v___x_1668_ =
        l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_1666_, v_x_1667_);
    return v___x_1668_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(
    mut v_x1_1669_: *mut LeanObject,
    mut v_x2_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1671_, 0, v_x1_1669_);
    lean_ctor_set(v___x_1671_, 1, v_x2_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
    mut v_inst_1673_: *mut LeanObject,
    mut v_l_1674_: *mut LeanObject,
    mut v_b_1675_: *mut LeanObject,
    mut v_c_1676_: *mut LeanObject,
    mut v_a_1677_: *mut LeanObject,
    mut v_a_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___f_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: usize = 0;
    let mut v___x_1696_: usize = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1677_) == 0 {
                    lean_dec_ref(v_a_1678_);
                    lean_dec(v_c_1676_);
                    lean_dec(v_b_1675_);
                    lean_dec_ref(v_inst_1673_);
                    lean_inc(v_l_1674_);
                    return v_l_1674_;
                } else {
                    v_head_1679_ = lean_ctor_get(v_a_1677_, 0);
                    v_tail_1680_ = lean_ctor_get(v_a_1677_, 1);
                    v_isSharedCheck_1699_ = (!lean_is_exclusive(v_a_1677_)) as u8;
                    if v_isSharedCheck_1699_ == 0 {
                        v___x_1682_ = v_a_1677_;
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1680_);
                        lean_inc(v_head_1679_);
                        lean_dec(v_a_1677_);
                        v___x_1682_ = lean_box(0);
                        v_isShared_1683_ = v_isSharedCheck_1699_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_1673_);
                lean_inc(v_head_1679_);
                lean_inc(v_b_1675_);
                v___x_1684_ = lean_apply_2(v_inst_1673_, v_b_1675_, v_head_1679_);
                v___x_1685_ = (lean_unbox(v___x_1684_) as u8);
                if v___x_1685_ == 0 {
                    lean_del_object(v___x_1682_);
                    v___x_1686_ = lean_array_push(v_a_1678_, v_head_1679_);
                    v_a_1677_ = v_tail_1680_;
                    v_a_1678_ = v___x_1686_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_head_1679_);
                    lean_dec(v_b_1675_);
                    lean_dec_ref(v_inst_1673_);
                    if v_isShared_1683_ == 0 {
                        lean_ctor_set(v___x_1682_, 0, v_c_1676_);
                        v___x_1689_ = v___x_1682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_c_1676_);
                        lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_tail_1680_);
                        v___x_1689_ = v_reuseFailAlloc_1698_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1690_ = lean_array_get_size(v_a_1678_);
                v___x_1691_ = lean_unsigned_to_nat(0);
                v___x_1692_ = l_List_foldrTR___redArg___closed__9;
                v___x_1693_ = lean_nat_dec_lt(v___x_1691_, v___x_1690_);
                if v___x_1693_ == 0 {
                    lean_dec_ref(v_a_1678_);
                    return v___x_1689_;
                } else {
                    v___f_1694_ =
                        l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                    v___x_1695_ = lean_usize_of_nat(v___x_1690_);
                    v___x_1696_ = 0usize;
                    v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
    mut v_inst_1700_: *mut LeanObject,
    mut v_l_1701_: *mut LeanObject,
    mut v_b_1702_: *mut LeanObject,
    mut v_c_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
    mut v_a_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1706_: *mut LeanObject = core::ptr::null_mut();
    v_res_1706_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1700_,
        v_l_1701_,
        v_b_1702_,
        v_c_1703_,
        v_a_1704_,
        v_a_1705_,
    );
    lean_dec(v_l_1701_);
    return v_res_1706_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replaceTR_go(
    mut v_00_u03b1_1707_: *mut LeanObject,
    mut v_inst_1708_: *mut LeanObject,
    mut v_l_1709_: *mut LeanObject,
    mut v_b_1710_: *mut LeanObject,
    mut v_c_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1715_: *mut LeanObject,
    mut v_inst_1716_: *mut LeanObject,
    mut v_l_1717_: *mut LeanObject,
    mut v_b_1718_: *mut LeanObject,
    mut v_c_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_a_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1722_: *mut LeanObject = core::ptr::null_mut();
    v_res_1722_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(
        v_00_u03b1_1715_,
        v_inst_1716_,
        v_l_1717_,
        v_b_1718_,
        v_c_1719_,
        v_a_1720_,
        v_a_1721_,
    );
    lean_dec(v_l_1717_);
    return v_res_1722_;
}
pub unsafe fn l_List_replaceTR___redArg(
    mut v_inst_1723_: *mut LeanObject,
    mut v_l_1724_: *mut LeanObject,
    mut v_b_1725_: *mut LeanObject,
    mut v_c_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1724_);
    v___x_1728_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1723_,
        v_l_1724_,
        v_b_1725_,
        v_c_1726_,
        v_l_1724_,
        v___x_1727_,
    );
    lean_dec(v_l_1724_);
    return v___x_1728_;
}
pub unsafe fn l_List_replaceTR(
    mut v_00_u03b1_1729_: *mut LeanObject,
    mut v_inst_1730_: *mut LeanObject,
    mut v_l_1731_: *mut LeanObject,
    mut v_b_1732_: *mut LeanObject,
    mut v_c_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1731_);
    v___x_1735_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(
        v_inst_1730_,
        v_l_1731_,
        v_b_1732_,
        v_c_1733_,
        v_l_1731_,
        v___x_1734_,
    );
    lean_dec(v_l_1731_);
    return v___x_1735_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(
    mut v_x_1736_: *mut LeanObject,
    mut v_x_1737_: *mut LeanObject,
    mut v_x_1738_: *mut LeanObject,
    mut v_h__1_1739_: *mut LeanObject,
    mut v_h__2_1740_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1736_) == 0 {
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1740_);
        v___x_1741_ = lean_apply_2(v_h__1_1739_, v_x_1737_, v_x_1738_);
        return v___x_1741_;
    } else {
        let mut v_head_1742_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1739_);
        v_head_1742_ = lean_ctor_get(v_x_1736_, 0);
        lean_inc(v_head_1742_);
        v_tail_1743_ = lean_ctor_get(v_x_1736_, 1);
        lean_inc(v_tail_1743_);
        lean_dec_ref_known(v_x_1736_, 2);
        v___x_1744_ = lean_apply_4(
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
    mut v_00_u03b1_1745_: *mut LeanObject,
    mut v_motive_1746_: *mut LeanObject,
    mut v_x_1747_: *mut LeanObject,
    mut v_x_1748_: *mut LeanObject,
    mut v_x_1749_: *mut LeanObject,
    mut v_h__1_1750_: *mut LeanObject,
    mut v_h__2_1751_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1747_) == 0 {
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1751_);
        v___x_1752_ = lean_apply_2(v_h__1_1750_, v_x_1748_, v_x_1749_);
        return v___x_1752_;
    } else {
        let mut v_head_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1750_);
        v_head_1753_ = lean_ctor_get(v_x_1747_, 0);
        lean_inc(v_head_1753_);
        v_tail_1754_ = lean_ctor_get(v_x_1747_, 1);
        lean_inc(v_tail_1754_);
        lean_dec_ref_known(v_x_1747_, 2);
        v___x_1755_ = lean_apply_4(
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
    mut v_f_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
    mut v_a_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v_zero_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1767_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: usize = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1757_) == 0 {
                    lean_dec(v_a_1758_);
                    lean_dec(v_f_1756_);
                    v___x_1760_ = lean_array_to_list(v_a_1759_);
                    return v___x_1760_;
                } else {
                    v_head_1761_ = lean_ctor_get(v_a_1757_, 0);
                    v_tail_1762_ = lean_ctor_get(v_a_1757_, 1);
                    v_isSharedCheck_1781_ = (!lean_is_exclusive(v_a_1757_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v___x_1764_ = v_a_1757_;
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1762_);
                        lean_inc(v_head_1761_);
                        lean_dec(v_a_1757_);
                        v___x_1764_ = lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1781_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_1766_ = lean_unsigned_to_nat(0);
                v_isZero_1767_ = lean_nat_dec_eq(v_a_1758_, v_zero_1766_);
                if v_isZero_1767_ == 1 {
                    lean_dec(v_a_1758_);
                    v___x_1768_ = lean_apply_1(v_f_1756_, v_head_1761_);
                    if v_isShared_1765_ == 0 {
                        lean_ctor_set(v___x_1764_, 0, v___x_1768_);
                        v___x_1770_ = v___x_1764_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1768_);
                        lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_tail_1762_);
                        v___x_1770_ = v_reuseFailAlloc_1776_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1764_);
                    v_one_1777_ = lean_unsigned_to_nat(1);
                    v_n_1778_ = lean_nat_sub(v_a_1758_, v_one_1777_);
                    lean_dec(v_a_1758_);
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
                    lean_dec_ref(v_a_1759_);
                    return v___x_1770_;
                } else {
                    v___x_1773_ = lean_usize_of_nat(v___x_1771_);
                    v___x_1774_ = 0usize;
                    v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1759_, v___x_1773_, v___x_1774_, v___x_1770_);
                    lean_dec_ref(v_a_1759_);
                    return v___x_1775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_modifyTR_go(
    mut v_00_u03b1_1782_: *mut LeanObject,
    mut v_f_1783_: *mut LeanObject,
    mut v_a_1784_: *mut LeanObject,
    mut v_a_1785_: *mut LeanObject,
    mut v_a_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    v___x_1787_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(
        v_f_1783_, v_a_1784_, v_a_1785_, v_a_1786_,
    );
    return v___x_1787_;
}
pub unsafe fn l_List_modifyTR___redArg(
    mut v_l_1788_: *mut LeanObject,
    mut v_i_1789_: *mut LeanObject,
    mut v_f_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1793_: *mut LeanObject,
    mut v_l_1794_: *mut LeanObject,
    mut v_i_1795_: *mut LeanObject,
    mut v_f_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    v___x_1797_ = l_List_modifyTR___redArg(v_l_1794_, v_i_1795_, v_f_1796_);
    return v___x_1797_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: usize = 0;
    let mut v___x_1808_: usize = 0;
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1802_ = lean_unsigned_to_nat(0);
                v_isZero_1803_ = lean_nat_dec_eq(v_a_1799_, v_zero_1802_);
                if v_isZero_1803_ == 1 {
                    lean_dec(v_a_1799_);
                    v___x_1804_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1804_, 0, v_a_1798_);
                    lean_ctor_set(v___x_1804_, 1, v_a_1800_);
                    v___x_1805_ = lean_array_get_size(v_a_1801_);
                    v___x_1806_ = lean_nat_dec_lt(v_zero_1802_, v___x_1805_);
                    if v___x_1806_ == 0 {
                        lean_dec_ref(v_a_1801_);
                        return v___x_1804_;
                    } else {
                        v___x_1807_ = lean_usize_of_nat(v___x_1805_);
                        v___x_1808_ = 0usize;
                        v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1801_, v___x_1807_, v___x_1808_, v___x_1804_);
                        lean_dec_ref(v_a_1801_);
                        return v___x_1809_;
                    }
                } else {
                    if lean_obj_tag(v_a_1800_) == 0 {
                        lean_dec(v_a_1799_);
                        lean_dec(v_a_1798_);
                        v___x_1810_ = lean_array_to_list(v_a_1801_);
                        return v___x_1810_;
                    } else {
                        v_head_1811_ = lean_ctor_get(v_a_1800_, 0);
                        lean_inc(v_head_1811_);
                        v_tail_1812_ = lean_ctor_get(v_a_1800_, 1);
                        lean_inc(v_tail_1812_);
                        lean_dec_ref_known(v_a_1800_, 2);
                        v_one_1813_ = lean_unsigned_to_nat(1);
                        v_n_1814_ = lean_nat_sub(v_a_1799_, v_one_1813_);
                        lean_dec(v_a_1799_);
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
    mut v_00_u03b1_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(
        v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_,
    );
    return v___x_1822_;
}
pub unsafe fn l_List_insertIdxTR___redArg(
    mut v_l_1823_: *mut LeanObject,
    mut v_n_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1828_: *mut LeanObject,
    mut v_l_1829_: *mut LeanObject,
    mut v_n_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_1834_: *mut LeanObject,
    mut v_x_1835_: *mut LeanObject,
    mut v_x_1836_: *mut LeanObject,
    mut v_h__1_1837_: *mut LeanObject,
    mut v_h__2_1838_: *mut LeanObject,
    mut v_h__3_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1841_: u8 = 0;
    v_zero_1840_ = lean_unsigned_to_nat(0);
    v_isZero_1841_ = lean_nat_dec_eq(v_x_1834_, v_zero_1840_);
    if v_isZero_1841_ == 1 {
        let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1839_);
        lean_dec(v_h__2_1838_);
        lean_dec(v_x_1834_);
        v___x_1842_ = lean_apply_2(v_h__1_1837_, v_x_1835_, v_x_1836_);
        return v___x_1842_;
    } else {
        lean_dec(v_h__1_1837_);
        if lean_obj_tag(v_x_1835_) == 0 {
            let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1839_);
            v___x_1843_ = lean_apply_3(v_h__2_1838_, v_x_1834_, v_x_1836_, lean_box(0));
            return v___x_1843_;
        } else {
            let mut v_head_1844_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1845_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_1846_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1847_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1838_);
            v_head_1844_ = lean_ctor_get(v_x_1835_, 0);
            lean_inc(v_head_1844_);
            v_tail_1845_ = lean_ctor_get(v_x_1835_, 1);
            lean_inc(v_tail_1845_);
            lean_dec_ref_known(v_x_1835_, 2);
            v_one_1846_ = lean_unsigned_to_nat(1);
            v_n_1847_ = lean_nat_sub(v_x_1834_, v_one_1846_);
            lean_dec(v_x_1834_);
            v___x_1848_ = lean_apply_4(
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
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_motive_1850_: *mut LeanObject,
    mut v_x_1851_: *mut LeanObject,
    mut v_x_1852_: *mut LeanObject,
    mut v_x_1853_: *mut LeanObject,
    mut v_h__1_1854_: *mut LeanObject,
    mut v_h__2_1855_: *mut LeanObject,
    mut v_h__3_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1858_: u8 = 0;
    v_zero_1857_ = lean_unsigned_to_nat(0);
    v_isZero_1858_ = lean_nat_dec_eq(v_x_1851_, v_zero_1857_);
    if v_isZero_1858_ == 1 {
        let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1856_);
        lean_dec(v_h__2_1855_);
        lean_dec(v_x_1851_);
        v___x_1859_ = lean_apply_2(v_h__1_1854_, v_x_1852_, v_x_1853_);
        return v___x_1859_;
    } else {
        lean_dec(v_h__1_1854_);
        if lean_obj_tag(v_x_1852_) == 0 {
            let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1856_);
            v___x_1860_ = lean_apply_3(v_h__2_1855_, v_x_1851_, v_x_1853_, lean_box(0));
            return v___x_1860_;
        } else {
            let mut v_head_1861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1862_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_1863_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1855_);
            v_head_1861_ = lean_ctor_get(v_x_1852_, 0);
            lean_inc(v_head_1861_);
            v_tail_1862_ = lean_ctor_get(v_x_1852_, 1);
            lean_inc(v_tail_1862_);
            lean_dec_ref_known(v_x_1852_, 2);
            v_one_1863_ = lean_unsigned_to_nat(1);
            v_n_1864_ = lean_nat_sub(v_x_1851_, v_one_1863_);
            lean_dec(v_x_1851_);
            v___x_1865_ = lean_apply_4(
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
    mut v_inst_1866_: *mut LeanObject,
    mut v_l_1867_: *mut LeanObject,
    mut v_a_1868_: *mut LeanObject,
    mut v_a_1869_: *mut LeanObject,
    mut v_a_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___f_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: usize = 0;
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1869_) == 0 {
                    lean_dec_ref(v_a_1870_);
                    lean_dec(v_a_1868_);
                    lean_dec_ref(v_inst_1866_);
                    lean_inc(v_l_1867_);
                    return v_l_1867_;
                } else {
                    v_head_1871_ = lean_ctor_get(v_a_1869_, 0);
                    lean_inc_n(v_head_1871_, 2);
                    v_tail_1872_ = lean_ctor_get(v_a_1869_, 1);
                    lean_inc(v_tail_1872_);
                    lean_dec_ref_known(v_a_1869_, 2);
                    lean_inc_ref(v_inst_1866_);
                    lean_inc(v_a_1868_);
                    v___x_1873_ = lean_apply_2(v_inst_1866_, v_head_1871_, v_a_1868_);
                    v___x_1874_ = (lean_unbox(v___x_1873_) as u8);
                    if v___x_1874_ == 0 {
                        v___x_1875_ = lean_array_push(v_a_1870_, v_head_1871_);
                        v_a_1869_ = v_tail_1872_;
                        v_a_1870_ = v___x_1875_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_head_1871_);
                        lean_dec(v_a_1868_);
                        lean_dec_ref(v_inst_1866_);
                        v___x_1877_ = lean_array_get_size(v_a_1870_);
                        v___x_1878_ = lean_unsigned_to_nat(0);
                        v___x_1879_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1880_ = lean_nat_dec_lt(v___x_1878_, v___x_1877_);
                        if v___x_1880_ == 0 {
                            lean_dec_ref(v_a_1870_);
                            return v_tail_1872_;
                        } else {
                            v___f_1881_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1882_ = lean_usize_of_nat(v___x_1877_);
                            v___x_1883_ = 0usize;
                            v___x_1884_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
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
    mut v_inst_1885_: *mut LeanObject,
    mut v_l_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1890_: *mut LeanObject = core::ptr::null_mut();
    v_res_1890_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1885_,
        v_l_1886_,
        v_a_1887_,
        v_a_1888_,
        v_a_1889_,
    );
    lean_dec(v_l_1886_);
    return v_res_1890_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go(
    mut v_00_u03b1_1891_: *mut LeanObject,
    mut v_inst_1892_: *mut LeanObject,
    mut v_l_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1898_: *mut LeanObject,
    mut v_inst_1899_: *mut LeanObject,
    mut v_l_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1904_: *mut LeanObject = core::ptr::null_mut();
    v_res_1904_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(
        v_00_u03b1_1898_,
        v_inst_1899_,
        v_l_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
    );
    lean_dec(v_l_1900_);
    return v_res_1904_;
}
pub unsafe fn l_List_eraseTR___redArg(
    mut v_inst_1905_: *mut LeanObject,
    mut v_l_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1906_);
    v___x_1909_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1905_,
        v_l_1906_,
        v_a_1907_,
        v_l_1906_,
        v___x_1908_,
    );
    lean_dec(v_l_1906_);
    return v___x_1909_;
}
pub unsafe fn l_List_eraseTR(
    mut v_00_u03b1_1910_: *mut LeanObject,
    mut v_inst_1911_: *mut LeanObject,
    mut v_l_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1912_);
    v___x_1915_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(
        v_inst_1911_,
        v_l_1912_,
        v_a_1913_,
        v_l_1912_,
        v___x_1914_,
    );
    lean_dec(v_l_1912_);
    return v___x_1915_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
    mut v_p_1916_: *mut LeanObject,
    mut v_l_1917_: *mut LeanObject,
    mut v_a_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___f_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: usize = 0;
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1918_) == 0 {
                    lean_dec_ref(v_a_1919_);
                    lean_dec_ref(v_p_1916_);
                    lean_inc(v_l_1917_);
                    return v_l_1917_;
                } else {
                    v_head_1920_ = lean_ctor_get(v_a_1918_, 0);
                    lean_inc_n(v_head_1920_, 2);
                    v_tail_1921_ = lean_ctor_get(v_a_1918_, 1);
                    lean_inc(v_tail_1921_);
                    lean_dec_ref_known(v_a_1918_, 2);
                    lean_inc_ref(v_p_1916_);
                    v___x_1922_ = lean_apply_1(v_p_1916_, v_head_1920_);
                    v___x_1923_ = (lean_unbox(v___x_1922_) as u8);
                    if v___x_1923_ == 0 {
                        v___x_1924_ = lean_array_push(v_a_1919_, v_head_1920_);
                        v_a_1918_ = v_tail_1921_;
                        v_a_1919_ = v___x_1924_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_head_1920_);
                        lean_dec_ref(v_p_1916_);
                        v___x_1926_ = lean_array_get_size(v_a_1919_);
                        v___x_1927_ = lean_unsigned_to_nat(0);
                        v___x_1928_ = l_List_foldrTR___redArg___closed__9;
                        v___x_1929_ = lean_nat_dec_lt(v___x_1927_, v___x_1926_);
                        if v___x_1929_ == 0 {
                            lean_dec_ref(v_a_1919_);
                            return v_tail_1921_;
                        } else {
                            v___f_1930_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0;
                            v___x_1931_ = lean_usize_of_nat(v___x_1926_);
                            v___x_1932_ = 0usize;
                            v___x_1933_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
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
    mut v_p_1934_: *mut LeanObject,
    mut v_l_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1938_: *mut LeanObject = core::ptr::null_mut();
    v_res_1938_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1934_, v_l_1935_, v_a_1936_, v_a_1937_,
    );
    lean_dec(v_l_1935_);
    return v_res_1938_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go(
    mut v_00_u03b1_1939_: *mut LeanObject,
    mut v_p_1940_: *mut LeanObject,
    mut v_l_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    v___x_1944_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1940_, v_l_1941_, v_a_1942_, v_a_1943_,
    );
    return v___x_1944_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(
    mut v_00_u03b1_1945_: *mut LeanObject,
    mut v_p_1946_: *mut LeanObject,
    mut v_l_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1950_: *mut LeanObject = core::ptr::null_mut();
    v_res_1950_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(
        v_00_u03b1_1945_,
        v_p_1946_,
        v_l_1947_,
        v_a_1948_,
        v_a_1949_,
    );
    lean_dec(v_l_1947_);
    return v_res_1950_;
}
pub unsafe fn l_List_erasePTR___redArg(
    mut v_p_1951_: *mut LeanObject,
    mut v_l_1952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    v___x_1953_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1952_);
    v___x_1954_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1951_,
        v_l_1952_,
        v_l_1952_,
        v___x_1953_,
    );
    lean_dec(v_l_1952_);
    return v___x_1954_;
}
pub unsafe fn l_List_erasePTR(
    mut v_00_u03b1_1955_: *mut LeanObject,
    mut v_p_1956_: *mut LeanObject,
    mut v_l_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1957_);
    v___x_1959_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(
        v_p_1956_,
        v_l_1957_,
        v_l_1957_,
        v___x_1958_,
    );
    lean_dec(v_l_1957_);
    return v___x_1959_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
    mut v_l_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1967_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1961_) == 0 {
                    lean_dec_ref(v_a_1963_);
                    lean_dec(v_a_1962_);
                    lean_inc(v_l_1960_);
                    return v_l_1960_;
                } else {
                    v_head_1964_ = lean_ctor_get(v_a_1961_, 0);
                    lean_inc(v_head_1964_);
                    v_tail_1965_ = lean_ctor_get(v_a_1961_, 1);
                    lean_inc(v_tail_1965_);
                    lean_dec_ref_known(v_a_1961_, 2);
                    v_zero_1966_ = lean_unsigned_to_nat(0);
                    v_isZero_1967_ = lean_nat_dec_eq(v_a_1962_, v_zero_1966_);
                    if v_isZero_1967_ == 1 {
                        lean_dec(v_head_1964_);
                        lean_dec(v_a_1962_);
                        v___x_1968_ = lean_array_get_size(v_a_1963_);
                        v___x_1969_ = lean_nat_dec_lt(v_zero_1966_, v___x_1968_);
                        if v___x_1969_ == 0 {
                            lean_dec_ref(v_a_1963_);
                            return v_tail_1965_;
                        } else {
                            v___x_1970_ = lean_usize_of_nat(v___x_1968_);
                            v___x_1971_ = 0usize;
                            v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1963_, v___x_1970_, v___x_1971_, v_tail_1965_);
                            lean_dec_ref(v_a_1963_);
                            return v___x_1972_;
                        }
                    } else {
                        v_one_1973_ = lean_unsigned_to_nat(1);
                        v_n_1974_ = lean_nat_sub(v_a_1962_, v_one_1973_);
                        lean_dec(v_a_1962_);
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
    mut v_l_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1981_: *mut LeanObject = core::ptr::null_mut();
    v_res_1981_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1977_, v_a_1978_, v_a_1979_, v_a_1980_,
    );
    lean_dec(v_l_1977_);
    return v_res_1981_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
    mut v_00_u03b1_1982_: *mut LeanObject,
    mut v_l_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    v___x_1987_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1983_, v_a_1984_, v_a_1985_, v_a_1986_,
    );
    return v___x_1987_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(
    mut v_00_u03b1_1988_: *mut LeanObject,
    mut v_l_1989_: *mut LeanObject,
    mut v_a_1990_: *mut LeanObject,
    mut v_a_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(
        v_00_u03b1_1988_,
        v_l_1989_,
        v_a_1990_,
        v_a_1991_,
        v_a_1992_,
    );
    lean_dec(v_l_1989_);
    return v_res_1993_;
}
pub unsafe fn l_List_eraseIdxTR___redArg(
    mut v_l_1994_: *mut LeanObject,
    mut v_n_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1994_);
    v___x_1997_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1994_,
        v_l_1994_,
        v_n_1995_,
        v___x_1996_,
    );
    lean_dec(v_l_1994_);
    return v___x_1997_;
}
pub unsafe fn l_List_eraseIdxTR(
    mut v_00_u03b1_1998_: *mut LeanObject,
    mut v_l_1999_: *mut LeanObject,
    mut v_n_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_List_setTR___redArg___closed__0;
    lean_inc(v_l_1999_);
    v___x_2002_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(
        v_l_1999_,
        v_l_1999_,
        v_n_2000_,
        v___x_2001_,
    );
    lean_dec(v_l_1999_);
    return v___x_2002_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(
    mut v_x_2003_: *mut LeanObject,
    mut v_x_2004_: *mut LeanObject,
    mut v_h__1_2005_: *mut LeanObject,
    mut v_h__2_2006_: *mut LeanObject,
    mut v_h__3_2007_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2003_) == 0 {
        let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2007_);
        lean_dec(v_h__2_2006_);
        v___x_2008_ = lean_apply_1(v_h__1_2005_, v_x_2004_);
        return v___x_2008_;
    } else {
        let mut v_head_2009_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2010_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_2011_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_2012_: u8 = 0;
        lean_dec(v_h__1_2005_);
        v_head_2009_ = lean_ctor_get(v_x_2003_, 0);
        lean_inc(v_head_2009_);
        v_tail_2010_ = lean_ctor_get(v_x_2003_, 1);
        lean_inc(v_tail_2010_);
        lean_dec_ref_known(v_x_2003_, 2);
        v_zero_2011_ = lean_unsigned_to_nat(0);
        v_isZero_2012_ = lean_nat_dec_eq(v_x_2004_, v_zero_2011_);
        if v_isZero_2012_ == 1 {
            let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2007_);
            lean_dec(v_x_2004_);
            v___x_2013_ = lean_apply_2(v_h__2_2006_, v_head_2009_, v_tail_2010_);
            return v___x_2013_;
        } else {
            let mut v_one_2014_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_2015_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2006_);
            v_one_2014_ = lean_unsigned_to_nat(1);
            v_n_2015_ = lean_nat_sub(v_x_2004_, v_one_2014_);
            lean_dec(v_x_2004_);
            v___x_2016_ = lean_apply_3(v_h__3_2007_, v_head_2009_, v_tail_2010_, v_n_2015_);
            return v___x_2016_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(
    mut v_00_u03b1_2017_: *mut LeanObject,
    mut v_motive_2018_: *mut LeanObject,
    mut v_x_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
    mut v_h__1_2021_: *mut LeanObject,
    mut v_h__2_2022_: *mut LeanObject,
    mut v_h__3_2023_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2019_) == 0 {
        let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2023_);
        lean_dec(v_h__2_2022_);
        v___x_2024_ = lean_apply_1(v_h__1_2021_, v_x_2020_);
        return v___x_2024_;
    } else {
        let mut v_head_2025_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2026_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_2027_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_2028_: u8 = 0;
        lean_dec(v_h__1_2021_);
        v_head_2025_ = lean_ctor_get(v_x_2019_, 0);
        lean_inc(v_head_2025_);
        v_tail_2026_ = lean_ctor_get(v_x_2019_, 1);
        lean_inc(v_tail_2026_);
        lean_dec_ref_known(v_x_2019_, 2);
        v_zero_2027_ = lean_unsigned_to_nat(0);
        v_isZero_2028_ = lean_nat_dec_eq(v_x_2020_, v_zero_2027_);
        if v_isZero_2028_ == 1 {
            let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2023_);
            lean_dec(v_x_2020_);
            v___x_2029_ = lean_apply_2(v_h__2_2022_, v_head_2025_, v_tail_2026_);
            return v___x_2029_;
        } else {
            let mut v_one_2030_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_2031_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2022_);
            v_one_2030_ = lean_unsigned_to_nat(1);
            v_n_2031_ = lean_nat_sub(v_x_2020_, v_one_2030_);
            lean_dec(v_x_2020_);
            v___x_2032_ = lean_apply_3(v_h__3_2023_, v_head_2025_, v_tail_2026_, v_n_2031_);
            return v___x_2032_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
    mut v_f_2033_: *mut LeanObject,
    mut v_a_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2034_) == 1 {
                    if lean_obj_tag(v_a_2035_) == 1 {
                        v_head_2037_ = lean_ctor_get(v_a_2034_, 0);
                        lean_inc(v_head_2037_);
                        v_tail_2038_ = lean_ctor_get(v_a_2034_, 1);
                        lean_inc(v_tail_2038_);
                        lean_dec_ref_known(v_a_2034_, 2);
                        v_head_2039_ = lean_ctor_get(v_a_2035_, 0);
                        lean_inc(v_head_2039_);
                        v_tail_2040_ = lean_ctor_get(v_a_2035_, 1);
                        lean_inc(v_tail_2040_);
                        lean_dec_ref_known(v_a_2035_, 2);
                        lean_inc(v_f_2033_);
                        v___x_2041_ = lean_apply_2(v_f_2033_, v_head_2037_, v_head_2039_);
                        v___x_2042_ = lean_array_push(v_a_2036_, v___x_2041_);
                        v_a_2034_ = v_tail_2038_;
                        v_a_2035_ = v_tail_2040_;
                        v_a_2036_ = v___x_2042_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_2034_, 2);
                        lean_dec(v_a_2035_);
                        lean_dec(v_f_2033_);
                        v___x_2044_ = lean_array_to_list(v_a_2036_);
                        return v___x_2044_;
                    }
                } else {
                    lean_dec(v_a_2035_);
                    lean_dec(v_a_2034_);
                    lean_dec(v_f_2033_);
                    v___x_2045_ = lean_array_to_list(v_a_2036_);
                    return v___x_2045_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
    mut v_00_u03b1_2046_: *mut LeanObject,
    mut v_00_u03b2_2047_: *mut LeanObject,
    mut v_00_u03b3_2048_: *mut LeanObject,
    mut v_f_2049_: *mut LeanObject,
    mut v_a_2050_: *mut LeanObject,
    mut v_a_2051_: *mut LeanObject,
    mut v_a_2052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(
        v_f_2049_, v_a_2050_, v_a_2051_, v_a_2052_,
    );
    return v___x_2053_;
}
pub unsafe fn l_List_zipWithTR___redArg(
    mut v_f_2054_: *mut LeanObject,
    mut v_as_2055_: *mut LeanObject,
    mut v_bs_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2059_: *mut LeanObject,
    mut v_00_u03b2_2060_: *mut LeanObject,
    mut v_00_u03b3_2061_: *mut LeanObject,
    mut v_f_2062_: *mut LeanObject,
    mut v_as_2063_: *mut LeanObject,
    mut v_bs_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2067_: *mut LeanObject,
    mut v_x_2068_: *mut LeanObject,
    mut v_x_2069_: *mut LeanObject,
    mut v_h__1_2070_: *mut LeanObject,
    mut v_h__2_2071_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2067_) == 1 {
        if lean_obj_tag(v_x_2068_) == 1 {
            let mut v_head_2072_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_2073_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_2074_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_2075_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2071_);
            v_head_2072_ = lean_ctor_get(v_x_2067_, 0);
            lean_inc(v_head_2072_);
            v_tail_2073_ = lean_ctor_get(v_x_2067_, 1);
            lean_inc(v_tail_2073_);
            lean_dec_ref_known(v_x_2067_, 2);
            v_head_2074_ = lean_ctor_get(v_x_2068_, 0);
            lean_inc(v_head_2074_);
            v_tail_2075_ = lean_ctor_get(v_x_2068_, 1);
            lean_inc(v_tail_2075_);
            lean_dec_ref_known(v_x_2068_, 2);
            v___x_2076_ = lean_apply_5(
                v_h__1_2070_,
                v_head_2072_,
                v_tail_2073_,
                v_head_2074_,
                v_tail_2075_,
                v_x_2069_,
            );
            return v___x_2076_;
        } else {
            let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_2070_);
            v___x_2077_ = lean_apply_4(v_h__2_2071_, v_x_2067_, v_x_2068_, v_x_2069_, lean_box(0));
            return v___x_2077_;
        }
    } else {
        let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2070_);
        v___x_2078_ = lean_apply_4(v_h__2_2071_, v_x_2067_, v_x_2068_, v_x_2069_, lean_box(0));
        return v___x_2078_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(
    mut v_00_u03b1_2079_: *mut LeanObject,
    mut v_00_u03b2_2080_: *mut LeanObject,
    mut v_00_u03b3_2081_: *mut LeanObject,
    mut v_motive_2082_: *mut LeanObject,
    mut v_x_2083_: *mut LeanObject,
    mut v_x_2084_: *mut LeanObject,
    mut v_x_2085_: *mut LeanObject,
    mut v_h__1_2086_: *mut LeanObject,
    mut v_h__2_2087_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2083_) == 1 {
        if lean_obj_tag(v_x_2084_) == 1 {
            let mut v_head_2088_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_2089_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_2090_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_2091_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2087_);
            v_head_2088_ = lean_ctor_get(v_x_2083_, 0);
            lean_inc(v_head_2088_);
            v_tail_2089_ = lean_ctor_get(v_x_2083_, 1);
            lean_inc(v_tail_2089_);
            lean_dec_ref_known(v_x_2083_, 2);
            v_head_2090_ = lean_ctor_get(v_x_2084_, 0);
            lean_inc(v_head_2090_);
            v_tail_2091_ = lean_ctor_get(v_x_2084_, 1);
            lean_inc(v_tail_2091_);
            lean_dec_ref_known(v_x_2084_, 2);
            v___x_2092_ = lean_apply_5(
                v_h__1_2086_,
                v_head_2088_,
                v_tail_2089_,
                v_head_2090_,
                v_tail_2091_,
                v_x_2085_,
            );
            return v___x_2092_;
        } else {
            let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_2086_);
            v___x_2093_ = lean_apply_4(v_h__2_2087_, v_x_2083_, v_x_2084_, v_x_2085_, lean_box(0));
            return v___x_2093_;
        }
    } else {
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2086_);
        v___x_2094_ = lean_apply_4(v_h__2_2087_, v_x_2083_, v_x_2084_, v_x_2085_, lean_box(0));
        return v___x_2094_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(
    mut v_as_2095_: *mut LeanObject,
    mut v_i_2096_: usize,
    mut v_stop_2097_: usize,
    mut v_b_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2099_: u8 = 0;
    let mut v_fst_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2099_ = lean_usize_dec_eq(v_i_2096_, v_stop_2097_);
                if v___x_2099_ == 0 {
                    v_fst_2100_ = lean_ctor_get(v_b_2098_, 0);
                    v_snd_2101_ = lean_ctor_get(v_b_2098_, 1);
                    v_isSharedCheck_2116_ = (!lean_is_exclusive(v_b_2098_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2103_ = v_b_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2116_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2101_);
                        lean_inc(v_fst_2100_);
                        lean_dec(v_b_2098_);
                        v___x_2103_ = lean_box(0);
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
                v___x_2108_ = lean_unsigned_to_nat(1);
                v___x_2109_ = lean_nat_sub(v_fst_2100_, v___x_2108_);
                lean_dec(v_fst_2100_);
                lean_inc(v___x_2109_);
                lean_inc(v___x_2107_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set(v___x_2103_, 1, v___x_2109_);
                    lean_ctor_set(v___x_2103_, 0, v___x_2107_);
                    v___x_2111_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2112_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2112_, 0, v___x_2111_);
                lean_ctor_set(v___x_2112_, 1, v_snd_2101_);
                v___x_2113_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2113_, 0, v___x_2109_);
                lean_ctor_set(v___x_2113_, 1, v___x_2112_);
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
    mut v_as_2117_: *mut LeanObject,
    mut v_i_2118_: *mut LeanObject,
    mut v_stop_2119_: *mut LeanObject,
    mut v_b_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2121_: usize = 0;
    let mut v_stop_boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
    lean_dec(v_i_2118_);
    v_stop_boxed_2122_ = lean_unbox_usize(v_stop_2119_);
    lean_dec(v_stop_2119_);
    v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2117_, v_i_boxed_2121_, v_stop_boxed_2122_, v_b_2120_);
    lean_dec_ref(v_as_2117_);
    return v_res_2123_;
}
pub unsafe fn l_List_zipIdxTR___redArg(
    mut v_l_2124_: *mut LeanObject,
    mut v_n_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_as_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    v_as_2126_ = lean_array_mk(v_l_2124_);
    v___x_2127_ = lean_array_get_size(v_as_2126_);
    v___x_2128_ = lean_box(0);
    v___x_2129_ = lean_unsigned_to_nat(0);
    v___x_2130_ = lean_nat_dec_lt(v___x_2129_, v___x_2127_);
    if v___x_2130_ == 0 {
        lean_dec_ref(v_as_2126_);
        return v___x_2128_;
    } else {
        let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: usize = 0;
        let mut v___x_2134_: usize = 0;
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_2136_: *mut LeanObject = core::ptr::null_mut();
        v___x_2131_ = lean_nat_add(v_n_2125_, v___x_2127_);
        v___x_2132_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2132_, 0, v___x_2131_);
        lean_ctor_set(v___x_2132_, 1, v___x_2128_);
        v___x_2133_ = lean_usize_of_nat(v___x_2127_);
        v___x_2134_ = 0usize;
        v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2126_, v___x_2133_, v___x_2134_, v___x_2132_);
        lean_dec_ref(v_as_2126_);
        v_snd_2136_ = lean_ctor_get(v___x_2135_, 1);
        lean_inc(v_snd_2136_);
        lean_dec_ref(v___x_2135_);
        return v_snd_2136_;
    }
}
pub unsafe fn l_List_zipIdxTR___redArg___boxed(
    mut v_l_2137_: *mut LeanObject,
    mut v_n_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2139_: *mut LeanObject = core::ptr::null_mut();
    v_res_2139_ = l_List_zipIdxTR___redArg(v_l_2137_, v_n_2138_);
    lean_dec(v_n_2138_);
    return v_res_2139_;
}
pub unsafe fn l_List_zipIdxTR(
    mut v_00_u03b1_2140_: *mut LeanObject,
    mut v_l_2141_: *mut LeanObject,
    mut v_n_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_List_zipIdxTR___redArg(v_l_2141_, v_n_2142_);
    return v___x_2143_;
}
pub unsafe fn l_List_zipIdxTR___boxed(
    mut v_00_u03b1_2144_: *mut LeanObject,
    mut v_l_2145_: *mut LeanObject,
    mut v_n_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_List_zipIdxTR(v_00_u03b1_2144_, v_l_2145_, v_n_2146_);
    lean_dec(v_n_2146_);
    return v_res_2147_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
    mut v_00_u03b1_2148_: *mut LeanObject,
    mut v_as_2149_: *mut LeanObject,
    mut v_i_2150_: usize,
    mut v_stop_2151_: usize,
    mut v_b_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_2149_, v_i_2150_, v_stop_2151_, v_b_2152_);
    return v___x_2153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(
    mut v_00_u03b1_2154_: *mut LeanObject,
    mut v_as_2155_: *mut LeanObject,
    mut v_i_2156_: *mut LeanObject,
    mut v_stop_2157_: *mut LeanObject,
    mut v_b_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2159_: usize = 0;
    let mut v_stop_boxed_2160_: usize = 0;
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2159_ = lean_unbox_usize(v_i_2156_);
    lean_dec(v_i_2156_);
    v_stop_boxed_2160_ = lean_unbox_usize(v_stop_2157_);
    lean_dec(v_stop_2157_);
    v_res_2161_ =
        l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(
            v_00_u03b1_2154_,
            v_as_2155_,
            v_i_boxed_2159_,
            v_stop_boxed_2160_,
            v_b_2158_,
        );
    lean_dec_ref(v_as_2155_);
    return v_res_2161_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_2162_: *mut LeanObject,
    mut v_x_2163_: *mut LeanObject,
    mut v_h__1_2164_: *mut LeanObject,
    mut v_h__2_2165_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2162_) == 0 {
        let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2165_);
        v___x_2166_ = lean_apply_1(v_h__1_2164_, v_x_2163_);
        return v___x_2166_;
    } else {
        let mut v_head_2167_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2164_);
        v_head_2167_ = lean_ctor_get(v_x_2162_, 0);
        lean_inc(v_head_2167_);
        v_tail_2168_ = lean_ctor_get(v_x_2162_, 1);
        lean_inc(v_tail_2168_);
        lean_dec_ref_known(v_x_2162_, 2);
        v___x_2169_ = lean_apply_3(v_h__2_2165_, v_head_2167_, v_tail_2168_, v_x_2163_);
        return v___x_2169_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_2170_: *mut LeanObject,
    mut v_motive_2171_: *mut LeanObject,
    mut v_x_2172_: *mut LeanObject,
    mut v_x_2173_: *mut LeanObject,
    mut v_h__1_2174_: *mut LeanObject,
    mut v_h__2_2175_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2172_) == 0 {
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2175_);
        v___x_2176_ = lean_apply_1(v_h__1_2174_, v_x_2173_);
        return v___x_2176_;
    } else {
        let mut v_head_2177_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2174_);
        v_head_2177_ = lean_ctor_get(v_x_2172_, 0);
        lean_inc(v_head_2177_);
        v_tail_2178_ = lean_ctor_get(v_x_2172_, 1);
        lean_inc(v_tail_2178_);
        lean_dec_ref_known(v_x_2172_, 2);
        v___x_2179_ = lean_apply_3(v_h__2_2175_, v_head_2177_, v_tail_2178_, v_x_2173_);
        return v___x_2179_;
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
    mut v_sep_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2182_) == 0 {
                    v___x_2184_ = lean_array_get_size(v_a_2183_);
                    v___x_2185_ = lean_unsigned_to_nat(0);
                    v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v___x_2184_);
                    if v___x_2186_ == 0 {
                        lean_dec_ref(v_a_2183_);
                        return v_a_2181_;
                    } else {
                        v___x_2187_ = lean_usize_of_nat(v___x_2184_);
                        v___x_2188_ = 0usize;
                        v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_2183_, v___x_2187_, v___x_2188_, v_a_2181_);
                        lean_dec_ref(v_a_2183_);
                        return v___x_2189_;
                    }
                } else {
                    v_head_2190_ = lean_ctor_get(v_a_2182_, 0);
                    lean_inc(v_head_2190_);
                    v_tail_2191_ = lean_ctor_get(v_a_2182_, 1);
                    lean_inc(v_tail_2191_);
                    lean_dec_ref_known(v_a_2182_, 2);
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
    mut v_sep_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
    mut v_a_2197_: *mut LeanObject,
    mut v_a_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2199_: *mut LeanObject = core::ptr::null_mut();
    v_res_2199_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2195_,
        v_a_2196_,
        v_a_2197_,
        v_a_2198_,
    );
    lean_dec_ref(v_sep_2195_);
    return v_res_2199_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
    mut v_00_u03b1_2200_: *mut LeanObject,
    mut v_sep_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v___x_2205_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
        v_sep_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
    );
    return v___x_2205_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(
    mut v_00_u03b1_2206_: *mut LeanObject,
    mut v_sep_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
    mut v_a_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2211_: *mut LeanObject = core::ptr::null_mut();
    v_res_2211_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(
        v_00_u03b1_2206_,
        v_sep_2207_,
        v_a_2208_,
        v_a_2209_,
        v_a_2210_,
    );
    lean_dec_ref(v_sep_2207_);
    return v_res_2211_;
}
pub unsafe fn l_List_intercalateTR___redArg(
    mut v_sep_2212_: *mut LeanObject,
    mut v_x_2213_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2213_) == 0 {
        let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_sep_2212_);
        v___x_2214_ = lean_box(0);
        return v___x_2214_;
    } else {
        let mut v_tail_2215_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2215_ = lean_ctor_get(v_x_2213_, 1);
        if lean_obj_tag(v_tail_2215_) == 0 {
            let mut v_head_2216_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_sep_2212_);
            v_head_2216_ = lean_ctor_get(v_x_2213_, 0);
            lean_inc(v_head_2216_);
            lean_dec_ref_known(v_x_2213_, 2);
            return v_head_2216_;
        } else {
            let mut v_head_2217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2215_);
            v_head_2217_ = lean_ctor_get(v_x_2213_, 0);
            lean_inc(v_head_2217_);
            lean_dec_ref_known(v_x_2213_, 2);
            v___x_2218_ = lean_array_mk(v_sep_2212_);
            v___x_2219_ = l_List_setTR___redArg___closed__0;
            v___x_2220_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(
                v___x_2218_,
                v_head_2217_,
                v_tail_2215_,
                v___x_2219_,
            );
            lean_dec_ref(v___x_2218_);
            return v___x_2220_;
        }
    }
}
pub unsafe fn l_List_intercalateTR(
    mut v_00_u03b1_2221_: *mut LeanObject,
    mut v_sep_2222_: *mut LeanObject,
    mut v_x_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_List_intercalateTR___redArg(v_sep_2222_, v_x_2223_);
    return v___x_2224_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(
    mut v_x_2225_: *mut LeanObject,
    mut v_h__1_2226_: *mut LeanObject,
    mut v_h__2_2227_: *mut LeanObject,
    mut v_h__3_2228_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2225_) == 0 {
        let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2228_);
        lean_dec(v_h__2_2227_);
        v___x_2229_ = lean_box(0);
        v___x_2230_ = lean_apply_1(v_h__1_2226_, v___x_2229_);
        return v___x_2230_;
    } else {
        let mut v_tail_2231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2226_);
        v_tail_2231_ = lean_ctor_get(v_x_2225_, 1);
        if lean_obj_tag(v_tail_2231_) == 0 {
            let mut v_head_2232_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2228_);
            v_head_2232_ = lean_ctor_get(v_x_2225_, 0);
            lean_inc(v_head_2232_);
            lean_dec_ref_known(v_x_2225_, 2);
            v___x_2233_ = lean_apply_1(v_h__2_2227_, v_head_2232_);
            return v___x_2233_;
        } else {
            let mut v_head_2234_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2231_);
            lean_dec(v_h__2_2227_);
            v_head_2234_ = lean_ctor_get(v_x_2225_, 0);
            lean_inc(v_head_2234_);
            lean_dec_ref_known(v_x_2225_, 2);
            v___x_2235_ = lean_apply_3(v_h__3_2228_, v_head_2234_, v_tail_2231_, lean_box(0));
            return v___x_2235_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(
    mut v_00_u03b1_2236_: *mut LeanObject,
    mut v_motive_2237_: *mut LeanObject,
    mut v_x_2238_: *mut LeanObject,
    mut v_h__1_2239_: *mut LeanObject,
    mut v_h__2_2240_: *mut LeanObject,
    mut v_h__3_2241_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2238_) == 0 {
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_2241_);
        lean_dec(v_h__2_2240_);
        v___x_2242_ = lean_box(0);
        v___x_2243_ = lean_apply_1(v_h__1_2239_, v___x_2242_);
        return v___x_2243_;
    } else {
        let mut v_tail_2244_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2239_);
        v_tail_2244_ = lean_ctor_get(v_x_2238_, 1);
        if lean_obj_tag(v_tail_2244_) == 0 {
            let mut v_head_2245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2241_);
            v_head_2245_ = lean_ctor_get(v_x_2238_, 0);
            lean_inc(v_head_2245_);
            lean_dec_ref_known(v_x_2238_, 2);
            v___x_2246_ = lean_apply_1(v_h__2_2240_, v_head_2245_);
            return v___x_2246_;
        } else {
            let mut v_head_2247_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2244_);
            lean_dec(v_h__2_2240_);
            v_head_2247_ = lean_ctor_get(v_x_2238_, 0);
            lean_inc(v_head_2247_);
            lean_dec_ref_known(v_x_2238_, 2);
            v___x_2248_ = lean_apply_3(v_h__3_2241_, v_head_2247_, v_tail_2244_, lean_box(0));
            return v___x_2248_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(
    mut v_x_2249_: *mut LeanObject,
    mut v_x_2250_: *mut LeanObject,
    mut v_x_2251_: *mut LeanObject,
    mut v_h__1_2252_: *mut LeanObject,
    mut v_h__2_2253_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2250_) == 0 {
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2253_);
        v___x_2254_ = lean_apply_2(v_h__1_2252_, v_x_2249_, v_x_2251_);
        return v___x_2254_;
    } else {
        let mut v_head_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2252_);
        v_head_2255_ = lean_ctor_get(v_x_2250_, 0);
        lean_inc(v_head_2255_);
        v_tail_2256_ = lean_ctor_get(v_x_2250_, 1);
        lean_inc(v_tail_2256_);
        lean_dec_ref_known(v_x_2250_, 2);
        v___x_2257_ = lean_apply_4(
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
    mut v_00_u03b1_2258_: *mut LeanObject,
    mut v_motive_2259_: *mut LeanObject,
    mut v_x_2260_: *mut LeanObject,
    mut v_x_2261_: *mut LeanObject,
    mut v_x_2262_: *mut LeanObject,
    mut v_h__1_2263_: *mut LeanObject,
    mut v_h__2_2264_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2261_) == 0 {
        let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_2264_);
        v___x_2265_ = lean_apply_2(v_h__1_2263_, v_x_2260_, v_x_2262_);
        return v___x_2265_;
    } else {
        let mut v_head_2266_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_2263_);
        v_head_2266_ = lean_ctor_get(v_x_2261_, 0);
        lean_inc(v_head_2266_);
        v_tail_2267_ = lean_ctor_get(v_x_2261_, 1);
        lean_inc(v_tail_2267_);
        lean_dec_ref_known(v_x_2261_, 2);
        v___x_2268_ = lean_apply_4(
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
pub unsafe fn runtime_initialize_Init_Data_List_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Impl(builtin);
}
