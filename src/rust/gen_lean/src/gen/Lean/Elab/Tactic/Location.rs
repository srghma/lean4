// Lean compiler output
// Module: Lean.Elab.Tactic.Location
// Imports: Lean.Elab.Tactic.ElabTerm
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_append___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_InfoTree_substitute;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_saveState___redArg, l_Lean_Elab_Tactic_tryTactic___redArg,
    l_Lean_Elab_Tactic_withMainContext___boxed, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_getFVarId,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_getFVarIds, l_Lean_LocalDecl_isImplementationDetail,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 84, 121, 112, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut leanh::LeanObject,5573707264546329628 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            108, 111, 99, 97, 116, 105, 111, 110, 87, 105, 108, 100, 99, 97, 114, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_expandLocation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_expandLocation___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value)
                as *mut leanh::LeanObject,
            1262264483427375750 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_expandLocation___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__2_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_expandLocation___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx(
    mut v_x_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1144_) == 0 {
        let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1145_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1145_;
    } else {
        let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1146_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1146_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx___boxed(
    mut v_x_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Elab_Tactic_Location_ctorIdx(v_x_1147_);
    leanh::lean_dec(v_x_1147_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___redArg(
    mut v_t_1149_: *mut leanh::LeanObject,
    mut v_k_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1149_) == 0 {
        return v_k_1150_;
    } else {
        let mut v_hypotheses_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_1152_: u8 = 0;
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_hypotheses_1151_ = leanh::lean_ctor_get(v_t_1149_, 0);
        leanh::lean_inc_ref(v_hypotheses_1151_);
        v_type_1152_ = leanh::lean_ctor_get_uint8(
            v_t_1149_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        );
        leanh::lean_dec_ref_known(v_t_1149_, 1);
        v___x_1153_ = leanh::lean_box((v_type_1152_) as usize);
        v___x_1154_ = leanh::lean_apply_2(v_k_1150_, v_hypotheses_1151_, v___x_1153_);
        return v___x_1154_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim(
    mut v_motive_1155_: *mut leanh::LeanObject,
    mut v_ctorIdx_1156_: *mut leanh::LeanObject,
    mut v_t_1157_: *mut leanh::LeanObject,
    mut v_h_1158_: *mut leanh::LeanObject,
    mut v_k_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1157_, v_k_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___boxed(
    mut v_motive_1161_: *mut leanh::LeanObject,
    mut v_ctorIdx_1162_: *mut leanh::LeanObject,
    mut v_t_1163_: *mut leanh::LeanObject,
    mut v_h_1164_: *mut leanh::LeanObject,
    mut v_k_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_Elab_Tactic_Location_ctorElim(
        v_motive_1161_,
        v_ctorIdx_1162_,
        v_t_1163_,
        v_h_1164_,
        v_k_1165_,
    );
    leanh::lean_dec(v_ctorIdx_1162_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(
    mut v_t_1167_: *mut leanh::LeanObject,
    mut v_wildcard_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1167_, v_wildcard_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim(
    mut v_motive_1170_: *mut leanh::LeanObject,
    mut v_t_1171_: *mut leanh::LeanObject,
    mut v_h_1172_: *mut leanh::LeanObject,
    mut v_wildcard_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1171_, v_wildcard_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim___redArg(
    mut v_t_1175_: *mut leanh::LeanObject,
    mut v_targets_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1175_, v_targets_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim(
    mut v_motive_1178_: *mut leanh::LeanObject,
    mut v_t_1179_: *mut leanh::LeanObject,
    mut v_h_1180_: *mut leanh::LeanObject,
    mut v_targets_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1179_, v_targets_1181_);
    return v___x_1182_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(
    mut v_as_1192_: *mut leanh::LeanObject,
    mut v_i_1193_: usize,
    mut v_stop_1194_: usize,
    mut v_b_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1201_ = lean_usize_dec_eq(v_i_1193_, v_stop_1194_);
                if v___x_1201_ == 0 {
                    v___x_1202_ = lean_array_uget_borrowed(v_as_1192_, v_i_1193_);
                    leanh::lean_inc(v___x_1202_);
                    v___x_1203_ = l_Lean_Syntax_getKind(v___x_1202_);
                    v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4;
                    v___x_1205_ = lean_name_eq(v___x_1203_, v___x_1204_);
                    leanh::lean_dec(v___x_1203_);
                    if v___x_1205_ == 0 {
                        leanh::lean_inc(v___x_1202_);
                        v___x_1206_ = lean_array_push(v_b_1195_, v___x_1202_);
                        v___y_1197_ = v___x_1206_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1197_ = v_b_1195_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1195_;
                }
            }
            1 => {
                v___x_1198_ = 1usize;
                v___x_1199_ = lean_usize_add(v_i_1193_, v___x_1198_);
                v_i_1193_ = v___x_1199_;
                v_b_1195_ = v___y_1197_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___boxed(
    mut v_as_1207_: *mut leanh::LeanObject,
    mut v_i_1208_: *mut leanh::LeanObject,
    mut v_stop_1209_: *mut leanh::LeanObject,
    mut v_b_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1211_: usize = 0;
    let mut v_stop_boxed_1212_: usize = 0;
    let mut v_res_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1211_ = leanh::lean_unbox_usize(v_i_1208_);
    leanh::lean_dec(v_i_1208_);
    v_stop_boxed_1212_ = leanh::lean_unbox_usize(v_stop_1209_);
    leanh::lean_dec(v_stop_1209_);
    v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_as_1207_, v_i_boxed_1211_, v_stop_boxed_1212_, v_b_1210_);
    leanh::lean_dec_ref(v_as_1207_);
    return v_res_1213_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation(
    mut v_stx_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_locationHyps_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numTurnstiles_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___x_1240_: u8 = 0;
    let mut v___x_1241_: usize = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1223_ = leanh::lean_unsigned_to_nat(1);
                v_arg_1224_ = l_Lean_Syntax_getArg(v_stx_1222_, v___x_1223_);
                leanh::lean_inc(v_arg_1224_);
                v___x_1225_ = l_Lean_Syntax_getKind(v_arg_1224_);
                v___x_1226_ = l_Lean_Elab_Tactic_expandLocation___closed__1;
                v___x_1227_ = lean_name_eq(v___x_1225_, v___x_1226_);
                leanh::lean_dec(v___x_1225_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1229_ = l_Lean_Syntax_getArg(v_arg_1224_, v___x_1228_);
                    leanh::lean_dec(v_arg_1224_);
                    v_locationHyps_1230_ = l_Lean_Syntax_getArgs(v___x_1229_);
                    leanh::lean_dec(v___x_1229_);
                    v___x_1231_ = lean_array_get_size(v_locationHyps_1230_);
                    v___x_1238_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
                    v___x_1239_ = lean_nat_dec_lt(v___x_1228_, v___x_1231_);
                    if v___x_1239_ == 0 {
                        leanh::lean_dec_ref(v_locationHyps_1230_);
                        v___y_1233_ = v___x_1238_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1240_ = lean_nat_dec_le(v___x_1231_, v___x_1231_);
                        if v___x_1240_ == 0 {
                            if v___x_1239_ == 0 {
                                leanh::lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1238_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1241_ = 0usize;
                                v___x_1242_ = lean_usize_of_nat(v___x_1231_);
                                v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1241_, v___x_1242_, v___x_1238_);
                                leanh::lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1243_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1244_ = 0usize;
                            v___x_1245_ = lean_usize_of_nat(v___x_1231_);
                            v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1244_, v___x_1245_, v___x_1238_);
                            leanh::lean_dec_ref(v_locationHyps_1230_);
                            v___y_1233_ = v___x_1246_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_arg_1224_);
                    v___x_1247_ = leanh::lean_box(0);
                    return v___x_1247_;
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v___y_1233_);
                v_numTurnstiles_1235_ = lean_nat_sub(v___x_1231_, v___x_1234_);
                v___x_1236_ = lean_nat_dec_lt(v___x_1228_, v_numTurnstiles_1235_);
                leanh::lean_dec(v_numTurnstiles_1235_);
                v___x_1237_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1237_, 0, v___y_1233_);
                leanh::lean_ctor_set_uint8(
                    v___x_1237_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1236_,
                );
                return v___x_1237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation___boxed(
    mut v_stx_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_Tactic_expandLocation(v_stx_1248_);
    leanh::lean_dec(v_stx_1248_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation(
    mut v_stx_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: u8 = 0;
    v___x_1251_ = l_Lean_Syntax_isNone(v_stx_1250_);
    if v___x_1251_ == 0 {
        let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1252_ = leanh::lean_unsigned_to_nat(0);
        v___x_1253_ = l_Lean_Syntax_getArg(v_stx_1250_, v___x_1252_);
        v___x_1254_ = l_Lean_Elab_Tactic_expandLocation(v___x_1253_);
        leanh::lean_dec(v___x_1253_);
        return v___x_1254_;
    } else {
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1255_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
        v___x_1256_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1256_, 0, v___x_1255_);
        leanh::lean_ctor_set_uint8(
            v___x_1256_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1251_,
        );
        return v___x_1256_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation___boxed(
    mut v_stx_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_1257_);
    leanh::lean_dec(v_stx_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(
    mut v_x_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1263_);
    leanh::lean_inc_ref(v___y_1262_);
    leanh::lean_inc(v___y_1261_);
    leanh::lean_inc_ref(v___y_1260_);
    v___x_1269_ = leanh::lean_apply_9(
        v_x_1259_,
        v___y_1260_,
        v___y_1261_,
        v___y_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        leanh::lean_box(0),
    );
    return v___x_1269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(
    mut v_x_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(
            v_x_1270_,
            v___y_1271_,
            v___y_1272_,
            v___y_1273_,
            v___y_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
            v___y_1278_,
        );
    leanh::lean_dec(v___y_1274_);
    leanh::lean_dec_ref(v___y_1273_);
    leanh::lean_dec(v___y_1272_);
    leanh::lean_dec_ref(v___y_1271_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(
    mut v_mvarId_1281_: *mut leanh::LeanObject,
    mut v_x_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
    mut v___y_1288_: *mut leanh::LeanObject,
    mut v___y_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1286_);
                leanh::lean_inc_ref(v___y_1285_);
                leanh::lean_inc(v___y_1284_);
                leanh::lean_inc_ref(v___y_1283_);
                v___f_1292_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_1292_, 0, v_x_1282_);
                leanh::lean_closure_set(v___f_1292_, 1, v___y_1283_);
                leanh::lean_closure_set(v___f_1292_, 2, v___y_1284_);
                leanh::lean_closure_set(v___f_1292_, 3, v___y_1285_);
                leanh::lean_closure_set(v___f_1292_, 4, v___y_1286_);
                v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1281_,
                    v___f_1292_,
                    v___y_1287_,
                    v___y_1288_,
                    v___y_1289_,
                    v___y_1290_,
                );
                if leanh::lean_obj_tag(v___x_1293_) == 0 {
                    return v___x_1293_;
                } else {
                    v_a_1294_ = leanh::lean_ctor_get(v___x_1293_, 0);
                    v_isSharedCheck_1301_ = (!leanh::lean_is_exclusive(v___x_1293_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1296_ = v___x_1293_;
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1294_);
                        leanh::lean_dec(v___x_1293_);
                        v___x_1296_ = leanh::lean_box(0);
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1297_ == 0 {
                    v___x_1299_ = v___x_1296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
                    v___x_1299_ = v_reuseFailAlloc_1300_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___boxed(
    mut v_mvarId_1302_: *mut leanh::LeanObject,
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(
        v_mvarId_1302_,
        v_x_1303_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
        v___y_1308_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
    );
    leanh::lean_dec(v___y_1311_);
    leanh::lean_dec_ref(v___y_1310_);
    leanh::lean_dec(v___y_1309_);
    leanh::lean_dec_ref(v___y_1308_);
    leanh::lean_dec(v___y_1307_);
    leanh::lean_dec_ref(v___y_1306_);
    leanh::lean_dec(v___y_1305_);
    leanh::lean_dec_ref(v___y_1304_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(
    mut v_00_u03b1_1314_: *mut leanh::LeanObject,
    mut v_mvarId_1315_: *mut leanh::LeanObject,
    mut v_x_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(
        v_mvarId_1315_,
        v_x_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
    );
    return v___x_1326_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___boxed(
    mut v_00_u03b1_1327_: *mut leanh::LeanObject,
    mut v_mvarId_1328_: *mut leanh::LeanObject,
    mut v_x_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
    mut v___y_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(
        v_00_u03b1_1327_,
        v_mvarId_1328_,
        v_x_1329_,
        v___y_1330_,
        v___y_1331_,
        v___y_1332_,
        v___y_1333_,
        v___y_1334_,
        v___y_1335_,
        v___y_1336_,
        v___y_1337_,
    );
    leanh::lean_dec(v___y_1337_);
    leanh::lean_dec_ref(v___y_1336_);
    leanh::lean_dec(v___y_1335_);
    leanh::lean_dec_ref(v___y_1334_);
    leanh::lean_dec(v___y_1333_);
    leanh::lean_dec_ref(v___y_1332_);
    leanh::lean_dec(v___y_1331_);
    leanh::lean_dec_ref(v___y_1330_);
    return v_res_1339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(
    mut v___x_1340_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1341_: *mut leanh::LeanObject,
    mut v_sz_1342_: usize,
    mut v_i_1343_: usize,
    mut v_bs_1344_: *mut leanh::LeanObject,
    mut v___y_1345_: *mut leanh::LeanObject,
    mut v___y_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
    mut v___y_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
                if v___x_1354_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_1341_);
                    v___x_1355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1355_, 0, v_bs_1344_);
                    return v___x_1355_;
                } else {
                    v_assignment_1356_ = leanh::lean_ctor_get(v___x_1340_, 0);
                    leanh::lean_inc_ref(v_ctx_x3f_1341_);
                    leanh::lean_inc(v___y_1352_);
                    leanh::lean_inc_ref(v___y_1351_);
                    leanh::lean_inc(v___y_1350_);
                    leanh::lean_inc_ref(v___y_1349_);
                    leanh::lean_inc(v___y_1348_);
                    leanh::lean_inc_ref(v___y_1347_);
                    leanh::lean_inc(v___y_1346_);
                    leanh::lean_inc_ref(v___y_1345_);
                    v___x_1357_ = leanh::lean_apply_9(
                        v_ctx_x3f_1341_,
                        v___y_1345_,
                        v___y_1346_,
                        v___y_1347_,
                        v___y_1348_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                        v___y_1352_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1357_) == 0 {
                        v_a_1358_ = leanh::lean_ctor_get(v___x_1357_, 0);
                        leanh::lean_inc(v_a_1358_);
                        leanh::lean_dec_ref_known(v___x_1357_, 1);
                        v_v_1359_ = lean_array_uget(v_bs_1344_, v_i_1343_);
                        v___x_1360_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1361_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1360_);
                        v_tree_1368_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_1359_, v_assignment_1356_);
                        if leanh::lean_obj_tag(v_a_1358_) == 0 {
                            v_a_1363_ = v_tree_1368_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1369_ = leanh::lean_ctor_get(v_a_1358_, 0);
                            leanh::lean_inc(v_val_1369_);
                            leanh::lean_dec_ref_known(v_a_1358_, 1);
                            v___x_1370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1370_, 0, v_val_1369_);
                            leanh::lean_ctor_set(v___x_1370_, 1, v_tree_1368_);
                            v_a_1363_ = v___x_1370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_1344_);
                        leanh::lean_dec_ref(v_ctx_x3f_1341_);
                        v_a_1371_ = leanh::lean_ctor_get(v___x_1357_, 0);
                        v_isSharedCheck_1378_ =
                            (!leanh::lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1357_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1371_);
                            leanh::lean_dec(v___x_1357_);
                            v___x_1373_ = leanh::lean_box(0);
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1364_ = 1usize;
                v___x_1365_ = lean_usize_add(v_i_1343_, v___x_1364_);
                v___x_1366_ = lean_array_uset(v_bs_x27_1361_, v_i_1343_, v_a_1363_);
                v_i_1343_ = v___x_1365_;
                v_bs_1344_ = v___x_1366_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9___boxed(
    mut v___x_1379_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1380_: *mut leanh::LeanObject,
    mut v_sz_1381_: *mut leanh::LeanObject,
    mut v_i_1382_: *mut leanh::LeanObject,
    mut v_bs_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1393_: usize = 0;
    let mut v_i_boxed_1394_: usize = 0;
    let mut v_res_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1393_ = leanh::lean_unbox_usize(v_sz_1381_);
    leanh::lean_dec(v_sz_1381_);
    v_i_boxed_1394_ = leanh::lean_unbox_usize(v_i_1382_);
    leanh::lean_dec(v_i_1382_);
    v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1379_, v_ctx_x3f_1380_, v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
    leanh::lean_dec(v___y_1391_);
    leanh::lean_dec_ref(v___y_1390_);
    leanh::lean_dec(v___y_1389_);
    leanh::lean_dec_ref(v___y_1388_);
    leanh::lean_dec(v___y_1387_);
    leanh::lean_dec_ref(v___y_1386_);
    leanh::lean_dec(v___y_1385_);
    leanh::lean_dec_ref(v___y_1384_);
    leanh::lean_dec_ref(v___x_1379_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(
    mut v___x_1396_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1397_: *mut leanh::LeanObject,
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
    mut v___y_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_sz_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut v_a_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_vs_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v_sz_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1445_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1452_: u8 = 0;
    let mut v_a_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1398_) == 0 {
                    v_cs_1408_ = leanh::lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1434_ = (!leanh::lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1410_ = v_x_1398_;
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_1408_);
                        leanh::lean_dec(v_x_1398_);
                        v___x_1410_ = leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1435_ = leanh::lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1461_ = (!leanh::lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1437_ = v_x_1398_;
                        v_isShared_1438_ = v_isSharedCheck_1461_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1435_);
                        leanh::lean_dec(v_x_1398_);
                        v___x_1437_ = leanh::lean_box(0);
                        v_isShared_1438_ = v_isSharedCheck_1461_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1412_ = lean_array_size(v_cs_1408_);
                v___x_1413_ = 0usize;
                v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_1396_, v_ctx_x3f_1397_, v_sz_1412_, v___x_1413_, v_cs_1408_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
                if leanh::lean_obj_tag(v___x_1414_) == 0 {
                    v_a_1415_ = leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1425_ = (!leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1425_ == 0 {
                        v___x_1417_ = v___x_1414_;
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1415_);
                        leanh::lean_dec(v___x_1414_);
                        v___x_1417_ = leanh::lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1410_);
                    v_a_1426_ = leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1433_ = (!leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1428_ = v___x_1414_;
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1426_);
                        leanh::lean_dec(v___x_1414_);
                        v___x_1428_ = leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1411_ == 0 {
                    leanh::lean_ctor_set(v___x_1410_, 0, v_a_1415_);
                    v___x_1420_ = v___x_1410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1418_ == 0 {
                    leanh::lean_ctor_set(v___x_1417_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1422_;
            }
            5 => {
                if v_isShared_1429_ == 0 {
                    v___x_1431_ = v___x_1428_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
                    v___x_1431_ = v_reuseFailAlloc_1432_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1431_;
            }
            7 => {
                v_sz_1439_ = lean_array_size(v_vs_1435_);
                v___x_1440_ = 0usize;
                v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1396_, v_ctx_x3f_1397_, v_sz_1439_, v___x_1440_, v_vs_1435_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
                if leanh::lean_obj_tag(v___x_1441_) == 0 {
                    v_a_1442_ = leanh::lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1452_ = (!leanh::lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1452_ == 0 {
                        v___x_1444_ = v___x_1441_;
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1442_);
                        leanh::lean_dec(v___x_1441_);
                        v___x_1444_ = leanh::lean_box(0);
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1437_);
                    v_a_1453_ = leanh::lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1460_ = (!leanh::lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1460_ == 0 {
                        v___x_1455_ = v___x_1441_;
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1453_);
                        leanh::lean_dec(v___x_1441_);
                        v___x_1455_ = leanh::lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1438_ == 0 {
                    leanh::lean_ctor_set(v___x_1437_, 0, v_a_1442_);
                    v___x_1447_ = v___x_1437_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1442_);
                    v___x_1447_ = v_reuseFailAlloc_1451_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1445_ == 0 {
                    leanh::lean_ctor_set(v___x_1444_, 0, v___x_1447_);
                    v___x_1449_ = v___x_1444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
                    v___x_1449_ = v_reuseFailAlloc_1450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1449_;
            }
            11 => {
                if v_isShared_1456_ == 0 {
                    v___x_1458_ = v___x_1455_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
                    v___x_1458_ = v_reuseFailAlloc_1459_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(
    mut v___x_1462_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1463_: *mut leanh::LeanObject,
    mut v_sz_1464_: usize,
    mut v_i_1465_: usize,
    mut v_bs_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1476_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
                if v___x_1476_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_1463_);
                    v___x_1477_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1477_, 0, v_bs_1466_);
                    return v___x_1477_;
                } else {
                    v_v_1478_ = lean_array_uget_borrowed(v_bs_1466_, v_i_1465_);
                    leanh::lean_inc(v_v_1478_);
                    leanh::lean_inc_ref(v_ctx_x3f_1463_);
                    v___x_1479_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1462_, v_ctx_x3f_1463_, v_v_1478_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
                    if leanh::lean_obj_tag(v___x_1479_) == 0 {
                        v_a_1480_ = leanh::lean_ctor_get(v___x_1479_, 0);
                        leanh::lean_inc(v_a_1480_);
                        leanh::lean_dec_ref_known(v___x_1479_, 1);
                        v___x_1481_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1482_ = lean_array_uset(v_bs_1466_, v_i_1465_, v___x_1481_);
                        v___x_1483_ = 1usize;
                        v___x_1484_ = lean_usize_add(v_i_1465_, v___x_1483_);
                        v___x_1485_ = lean_array_uset(v_bs_x27_1482_, v_i_1465_, v_a_1480_);
                        v_i_1465_ = v___x_1484_;
                        v_bs_1466_ = v___x_1485_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1466_);
                        leanh::lean_dec_ref(v_ctx_x3f_1463_);
                        v_a_1487_ = leanh::lean_ctor_get(v___x_1479_, 0);
                        v_isSharedCheck_1494_ =
                            (!leanh::lean_is_exclusive(v___x_1479_)) as u8;
                        if v_isSharedCheck_1494_ == 0 {
                            v___x_1489_ = v___x_1479_;
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1487_);
                            leanh::lean_dec(v___x_1479_);
                            v___x_1489_ = leanh::lean_box(0);
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(
    mut v___x_1495_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1496_: *mut leanh::LeanObject,
    mut v_sz_1497_: *mut leanh::LeanObject,
    mut v_i_1498_: *mut leanh::LeanObject,
    mut v_bs_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
    mut v___y_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1509_: usize = 0;
    let mut v_i_boxed_1510_: usize = 0;
    let mut v_res_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1509_ = leanh::lean_unbox_usize(v_sz_1497_);
    leanh::lean_dec(v_sz_1497_);
    v_i_boxed_1510_ = leanh::lean_unbox_usize(v_i_1498_);
    leanh::lean_dec(v_i_1498_);
    v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_1495_, v_ctx_x3f_1496_, v_sz_boxed_1509_, v_i_boxed_1510_, v_bs_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
    leanh::lean_dec(v___y_1507_);
    leanh::lean_dec_ref(v___y_1506_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec_ref(v___y_1504_);
    leanh::lean_dec(v___y_1503_);
    leanh::lean_dec_ref(v___y_1502_);
    leanh::lean_dec(v___y_1501_);
    leanh::lean_dec_ref(v___y_1500_);
    leanh::lean_dec_ref(v___x_1495_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(
    mut v___x_1512_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1513_: *mut leanh::LeanObject,
    mut v_x_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
    mut v___y_1517_: *mut leanh::LeanObject,
    mut v___y_1518_: *mut leanh::LeanObject,
    mut v___y_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1512_, v_ctx_x3f_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
    leanh::lean_dec(v___y_1522_);
    leanh::lean_dec_ref(v___y_1521_);
    leanh::lean_dec(v___y_1520_);
    leanh::lean_dec_ref(v___y_1519_);
    leanh::lean_dec(v___y_1518_);
    leanh::lean_dec_ref(v___y_1517_);
    leanh::lean_dec(v___y_1516_);
    leanh::lean_dec_ref(v___y_1515_);
    leanh::lean_dec_ref(v___x_1512_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(
    mut v___x_1525_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1526_: *mut leanh::LeanObject,
    mut v_t_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_1540_: usize = 0;
    let mut v_tailOff_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_a_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1537_ = leanh::lean_ctor_get(v_t_1527_, 0);
                v_tail_1538_ = leanh::lean_ctor_get(v_t_1527_, 1);
                v_size_1539_ = leanh::lean_ctor_get(v_t_1527_, 2);
                v_shift_1540_ = leanh::lean_ctor_get_usize(v_t_1527_, 4);
                v_tailOff_1541_ = leanh::lean_ctor_get(v_t_1527_, 3);
                v_isSharedCheck_1577_ = (!leanh::lean_is_exclusive(v_t_1527_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1543_ = v_t_1527_;
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_1541_);
                    leanh::lean_inc(v_size_1539_);
                    leanh::lean_inc(v_tail_1538_);
                    leanh::lean_inc(v_root_1537_);
                    leanh::lean_dec(v_t_1527_);
                    v___x_1543_ = leanh::lean_box(0);
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_ctx_x3f_1526_);
                v___x_1545_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1525_, v_ctx_x3f_1526_, v_root_1537_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                if leanh::lean_obj_tag(v___x_1545_) == 0 {
                    v_a_1546_ = leanh::lean_ctor_get(v___x_1545_, 0);
                    leanh::lean_inc(v_a_1546_);
                    leanh::lean_dec_ref_known(v___x_1545_, 1);
                    v_sz_1547_ = lean_array_size(v_tail_1538_);
                    v___x_1548_ = 0usize;
                    v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1525_, v_ctx_x3f_1526_, v_sz_1547_, v___x_1548_, v_tail_1538_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                    if leanh::lean_obj_tag(v___x_1549_) == 0 {
                        v_a_1550_ = leanh::lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1560_ =
                            (!leanh::lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1560_ == 0 {
                            v___x_1552_ = v___x_1549_;
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1550_);
                            leanh::lean_dec(v___x_1549_);
                            v___x_1552_ = leanh::lean_box(0);
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1546_);
                        leanh::lean_del_object(v___x_1543_);
                        leanh::lean_dec(v_tailOff_1541_);
                        leanh::lean_dec(v_size_1539_);
                        v_a_1561_ = leanh::lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1568_ =
                            (!leanh::lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1568_ == 0 {
                            v___x_1563_ = v___x_1549_;
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1561_);
                            leanh::lean_dec(v___x_1549_);
                            v___x_1563_ = leanh::lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1543_);
                    leanh::lean_dec(v_tailOff_1541_);
                    leanh::lean_dec(v_size_1539_);
                    leanh::lean_dec_ref(v_tail_1538_);
                    leanh::lean_dec_ref(v_ctx_x3f_1526_);
                    v_a_1569_ = leanh::lean_ctor_get(v___x_1545_, 0);
                    v_isSharedCheck_1576_ = (!leanh::lean_is_exclusive(v___x_1545_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1571_ = v___x_1545_;
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1569_);
                        leanh::lean_dec(v___x_1545_);
                        v___x_1571_ = leanh::lean_box(0);
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1544_ == 0 {
                    leanh::lean_ctor_set(v___x_1543_, 1, v_a_1550_);
                    leanh::lean_ctor_set(v___x_1543_, 0, v_a_1546_);
                    v___x_1555_ = v___x_1543_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_size_1539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_tailOff_1541_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_1559_, 4, v_shift_1540_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1553_ == 0 {
                    leanh::lean_ctor_set(v___x_1552_, 0, v___x_1555_);
                    v___x_1557_ = v___x_1552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1557_;
            }
            5 => {
                if v_isShared_1564_ == 0 {
                    v___x_1566_ = v___x_1563_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
                    v___x_1566_ = v_reuseFailAlloc_1567_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1566_;
            }
            7 => {
                if v_isShared_1572_ == 0 {
                    v___x_1574_ = v___x_1571_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
                    v___x_1574_ = v_reuseFailAlloc_1575_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5___boxed(
    mut v___x_1578_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1579_: *mut leanh::LeanObject,
    mut v_t_1580_: *mut leanh::LeanObject,
    mut v___y_1581_: *mut leanh::LeanObject,
    mut v___y_1582_: *mut leanh::LeanObject,
    mut v___y_1583_: *mut leanh::LeanObject,
    mut v___y_1584_: *mut leanh::LeanObject,
    mut v___y_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_1578_, v_ctx_x3f_1579_, v_t_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
    leanh::lean_dec(v___y_1588_);
    leanh::lean_dec_ref(v___y_1587_);
    leanh::lean_dec(v___y_1586_);
    leanh::lean_dec_ref(v___y_1585_);
    leanh::lean_dec(v___y_1584_);
    leanh::lean_dec_ref(v___y_1583_);
    leanh::lean_dec(v___y_1582_);
    leanh::lean_dec_ref(v___y_1581_);
    leanh::lean_dec_ref(v___x_1578_);
    return v_res_1590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(
    mut v___y_1591_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_a_x3f_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_enabled_1624_: u8 = 0;
    let mut v_assignment_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v_a_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_st_ref_get(v___y_1591_);
                v_infoState_1604_ = leanh::lean_ctor_get(v___x_1603_, 7);
                leanh::lean_inc_ref(v_infoState_1604_);
                leanh::lean_dec(v___x_1603_);
                v_trees_1605_ = leanh::lean_ctor_get(v_infoState_1604_, 2);
                leanh::lean_inc_ref(v_trees_1605_);
                v___x_1606_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_1604_, v_ctx_x3f_1592_, v_trees_1605_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1591_);
                leanh::lean_dec_ref(v_infoState_1604_);
                if leanh::lean_obj_tag(v___x_1606_) == 0 {
                    v_a_1607_ = leanh::lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1645_ = (!leanh::lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1609_ = v___x_1606_;
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1607_);
                        leanh::lean_dec(v___x_1606_);
                        v___x_1609_ = leanh::lean_box(0);
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1600_);
                    v_a_1646_ = leanh::lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1653_ = (!leanh::lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1648_ = v___x_1606_;
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1646_);
                        leanh::lean_dec(v___x_1606_);
                        v___x_1648_ = leanh::lean_box(0);
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1611_ = lean_st_ref_take(v___y_1591_);
                v_infoState_1612_ = leanh::lean_ctor_get(v___x_1611_, 7);
                v_env_1613_ = leanh::lean_ctor_get(v___x_1611_, 0);
                v_nextMacroScope_1614_ = leanh::lean_ctor_get(v___x_1611_, 1);
                v_ngen_1615_ = leanh::lean_ctor_get(v___x_1611_, 2);
                v_auxDeclNGen_1616_ = leanh::lean_ctor_get(v___x_1611_, 3);
                v_traceState_1617_ = leanh::lean_ctor_get(v___x_1611_, 4);
                v_cache_1618_ = leanh::lean_ctor_get(v___x_1611_, 5);
                v_messages_1619_ = leanh::lean_ctor_get(v___x_1611_, 6);
                v_snapshotTasks_1620_ = leanh::lean_ctor_get(v___x_1611_, 8);
                v_isSharedCheck_1644_ = (!leanh::lean_is_exclusive(v___x_1611_)) as u8;
                if v_isSharedCheck_1644_ == 0 {
                    v___x_1622_ = v___x_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1620_);
                    leanh::lean_inc(v_infoState_1612_);
                    leanh::lean_inc(v_messages_1619_);
                    leanh::lean_inc(v_cache_1618_);
                    leanh::lean_inc(v_traceState_1617_);
                    leanh::lean_inc(v_auxDeclNGen_1616_);
                    leanh::lean_inc(v_ngen_1615_);
                    leanh::lean_inc(v_nextMacroScope_1614_);
                    leanh::lean_inc(v_env_1613_);
                    leanh::lean_dec(v___x_1611_);
                    v___x_1622_ = leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1624_ = leanh::lean_ctor_get_uint8(
                    v_infoState_1612_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1625_ = leanh::lean_ctor_get(v_infoState_1612_, 0);
                v_lazyAssignment_1626_ = leanh::lean_ctor_get(v_infoState_1612_, 1);
                v_isSharedCheck_1642_ = (!leanh::lean_is_exclusive(v_infoState_1612_)) as u8;
                if v_isSharedCheck_1642_ == 0 {
                    v_unused_1643_ = leanh::lean_ctor_get(v_infoState_1612_, 2);
                    leanh::lean_dec(v_unused_1643_);
                    v___x_1628_ = v_infoState_1612_;
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_1626_);
                    leanh::lean_inc(v_assignment_1625_);
                    leanh::lean_dec(v_infoState_1612_);
                    v___x_1628_ = leanh::lean_box(0);
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1630_ = l_Lean_PersistentArray_append___redArg(v_a_1600_, v_a_1607_);
                leanh::lean_dec(v_a_1607_);
                if v_isShared_1629_ == 0 {
                    leanh::lean_ctor_set(v___x_1628_, 2, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_assignment_1625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_lazyAssignment_1626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1630_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1641_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_1624_,
                    );
                    v___x_1632_ = v_reuseFailAlloc_1641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1623_ == 0 {
                    leanh::lean_ctor_set(v___x_1622_, 7, v___x_1632_);
                    v___x_1634_ = v___x_1622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_env_1613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_nextMacroScope_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_ngen_1615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_auxDeclNGen_1616_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_traceState_1617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 5, v_cache_1618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 6, v_messages_1619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 7, v___x_1632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 8, v_snapshotTasks_1620_);
                    v___x_1634_ = v_reuseFailAlloc_1640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1635_ = lean_st_ref_set(v___y_1591_, v___x_1634_);
                v___x_1636_ = leanh::lean_box(0);
                if v_isShared_1610_ == 0 {
                    leanh::lean_ctor_set(v___x_1609_, 0, v___x_1636_);
                    v___x_1638_ = v___x_1609_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1639_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
                    v___x_1638_ = v_reuseFailAlloc_1639_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1638_;
            }
            7 => {
                if v_isShared_1649_ == 0 {
                    v___x_1651_ = v___x_1648_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
                    v___x_1651_ = v_reuseFailAlloc_1652_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0___boxed(
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v_a_1663_: *mut leanh::LeanObject,
    mut v_a_x3f_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1654_, v_ctx_x3f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v_a_1663_, v_a_x3f_1664_);
    leanh::lean_dec(v_a_x3f_1664_);
    leanh::lean_dec_ref(v___y_1662_);
    leanh::lean_dec(v___y_1661_);
    leanh::lean_dec_ref(v___y_1660_);
    leanh::lean_dec(v___y_1659_);
    leanh::lean_dec_ref(v___y_1658_);
    leanh::lean_dec(v___y_1657_);
    leanh::lean_dec_ref(v___y_1656_);
    leanh::lean_dec(v___y_1654_);
    return v_res_1666_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = leanh::lean_unsigned_to_nat(32);
    v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
    v___x_1669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = 5usize;
    v___x_1671_ = leanh::lean_unsigned_to_nat(0);
    v___x_1672_ = leanh::lean_unsigned_to_nat(32);
    v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
    v___x_1674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_1675_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    leanh::lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    leanh::lean_ctor_set(v___x_1675_, 2, v___x_1671_);
    leanh::lean_ctor_set(v___x_1675_, 3, v___x_1671_);
    leanh::lean_ctor_set_usize(v___x_1675_, 4, v___x_1670_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(
    mut v___y_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v_enabled_1694_: u8 = 0;
    let mut v_assignment_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_unused_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1678_ = lean_st_ref_get(v___y_1676_);
                v_infoState_1679_ = leanh::lean_ctor_get(v___x_1678_, 7);
                leanh::lean_inc_ref(v_infoState_1679_);
                leanh::lean_dec(v___x_1678_);
                v_trees_1680_ = leanh::lean_ctor_get(v_infoState_1679_, 2);
                leanh::lean_inc_ref(v_trees_1680_);
                leanh::lean_dec_ref(v_infoState_1679_);
                v___x_1681_ = lean_st_ref_take(v___y_1676_);
                v_infoState_1682_ = leanh::lean_ctor_get(v___x_1681_, 7);
                v_env_1683_ = leanh::lean_ctor_get(v___x_1681_, 0);
                v_nextMacroScope_1684_ = leanh::lean_ctor_get(v___x_1681_, 1);
                v_ngen_1685_ = leanh::lean_ctor_get(v___x_1681_, 2);
                v_auxDeclNGen_1686_ = leanh::lean_ctor_get(v___x_1681_, 3);
                v_traceState_1687_ = leanh::lean_ctor_get(v___x_1681_, 4);
                v_cache_1688_ = leanh::lean_ctor_get(v___x_1681_, 5);
                v_messages_1689_ = leanh::lean_ctor_get(v___x_1681_, 6);
                v_snapshotTasks_1690_ = leanh::lean_ctor_get(v___x_1681_, 8);
                v_isSharedCheck_1711_ = (!leanh::lean_is_exclusive(v___x_1681_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v___x_1692_ = v___x_1681_;
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1690_);
                    leanh::lean_inc(v_infoState_1682_);
                    leanh::lean_inc(v_messages_1689_);
                    leanh::lean_inc(v_cache_1688_);
                    leanh::lean_inc(v_traceState_1687_);
                    leanh::lean_inc(v_auxDeclNGen_1686_);
                    leanh::lean_inc(v_ngen_1685_);
                    leanh::lean_inc(v_nextMacroScope_1684_);
                    leanh::lean_inc(v_env_1683_);
                    leanh::lean_dec(v___x_1681_);
                    v___x_1692_ = leanh::lean_box(0);
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1694_ = leanh::lean_ctor_get_uint8(
                    v_infoState_1682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1695_ = leanh::lean_ctor_get(v_infoState_1682_, 0);
                v_lazyAssignment_1696_ = leanh::lean_ctor_get(v_infoState_1682_, 1);
                v_isSharedCheck_1709_ = (!leanh::lean_is_exclusive(v_infoState_1682_)) as u8;
                if v_isSharedCheck_1709_ == 0 {
                    v_unused_1710_ = leanh::lean_ctor_get(v_infoState_1682_, 2);
                    leanh::lean_dec(v_unused_1710_);
                    v___x_1698_ = v_infoState_1682_;
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_1696_);
                    leanh::lean_inc(v_assignment_1695_);
                    leanh::lean_dec(v_infoState_1682_);
                    v___x_1698_ = leanh::lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
                if v_isShared_1699_ == 0 {
                    leanh::lean_ctor_set(v___x_1698_, 2, v___x_1700_);
                    v___x_1702_ = v___x_1698_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1708_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_assignment_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_lazyAssignment_1696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 2, v___x_1700_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1708_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_1694_,
                    );
                    v___x_1702_ = v_reuseFailAlloc_1708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1693_ == 0 {
                    leanh::lean_ctor_set(v___x_1692_, 7, v___x_1702_);
                    v___x_1704_ = v___x_1692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_env_1683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nextMacroScope_1684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_ngen_1685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_auxDeclNGen_1686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_traceState_1687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_cache_1688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_messages_1689_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 7, v___x_1702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_snapshotTasks_1690_);
                    v___x_1704_ = v_reuseFailAlloc_1707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1705_ = lean_st_ref_set(v___y_1676_, v___x_1704_);
                v___x_1706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1706_, 0, v_trees_1680_);
                return v___x_1706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1712_);
    leanh::lean_dec(v___y_1712_);
    return v_res_1714_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(
    mut v_x_1715_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
    mut v___y_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
    mut v___y_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1728_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_unused_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_reuseFailAlloc_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_a_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_unused_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1726_ = lean_st_ref_get(v___y_1724_);
                v_infoState_1727_ = leanh::lean_ctor_get(v___x_1726_, 7);
                leanh::lean_inc_ref(v_infoState_1727_);
                leanh::lean_dec(v___x_1726_);
                v_enabled_1728_ = leanh::lean_ctor_get_uint8(
                    v_infoState_1727_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_1727_);
                if v_enabled_1728_ == 0 {
                    leanh::lean_dec_ref(v_ctx_x3f_1716_);
                    leanh::lean_inc(v___y_1724_);
                    leanh::lean_inc_ref(v___y_1723_);
                    leanh::lean_inc(v___y_1722_);
                    leanh::lean_inc_ref(v___y_1721_);
                    leanh::lean_inc(v___y_1720_);
                    leanh::lean_inc_ref(v___y_1719_);
                    leanh::lean_inc(v___y_1718_);
                    leanh::lean_inc_ref(v___y_1717_);
                    v___x_1729_ = leanh::lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        leanh::lean_box(0),
                    );
                    return v___x_1729_;
                } else {
                    v___x_1730_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1724_);
                    v_a_1731_ = leanh::lean_ctor_get(v___x_1730_, 0);
                    leanh::lean_inc(v_a_1731_);
                    leanh::lean_dec_ref(v___x_1730_);
                    leanh::lean_inc(v___y_1724_);
                    leanh::lean_inc_ref(v___y_1723_);
                    leanh::lean_inc(v___y_1722_);
                    leanh::lean_inc_ref(v___y_1721_);
                    leanh::lean_inc(v___y_1720_);
                    leanh::lean_inc_ref(v___y_1719_);
                    leanh::lean_inc(v___y_1718_);
                    leanh::lean_inc_ref(v___y_1717_);
                    v_r_1732_ = leanh::lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_1732_) == 0 {
                        v_a_1733_ = leanh::lean_ctor_get(v_r_1732_, 0);
                        v_isSharedCheck_1757_ = (!leanh::lean_is_exclusive(v_r_1732_)) as u8;
                        if v_isSharedCheck_1757_ == 0 {
                            v___x_1735_ = v_r_1732_;
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1733_);
                            leanh::lean_dec(v_r_1732_);
                            v___x_1735_ = leanh::lean_box(0);
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1758_ = leanh::lean_ctor_get(v_r_1732_, 0);
                        leanh::lean_inc(v_a_1758_);
                        leanh::lean_dec_ref_known(v_r_1732_, 1);
                        v___x_1759_ = leanh::lean_box(0);
                        v___x_1760_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1759_);
                        if leanh::lean_obj_tag(v___x_1760_) == 0 {
                            v_isSharedCheck_1767_ =
                                (!leanh::lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v_unused_1768_ = leanh::lean_ctor_get(v___x_1760_, 0);
                                leanh::lean_dec(v_unused_1768_);
                                v___x_1762_ = v___x_1760_;
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1760_);
                                v___x_1762_ = leanh::lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1758_);
                            v_a_1769_ = leanh::lean_ctor_get(v___x_1760_, 0);
                            v_isSharedCheck_1776_ =
                                (!leanh::lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1776_ == 0 {
                                v___x_1771_ = v___x_1760_;
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1769_);
                                leanh::lean_dec(v___x_1760_);
                                v___x_1771_ = leanh::lean_box(0);
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1733_);
                if v_isShared_1736_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1735_, 1);
                    v___x_1738_ = v___x_1735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1739_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1738_);
                leanh::lean_dec_ref(v___x_1738_);
                if leanh::lean_obj_tag(v___x_1739_) == 0 {
                    v_isSharedCheck_1746_ = (!leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v_unused_1747_ = leanh::lean_ctor_get(v___x_1739_, 0);
                        leanh::lean_dec(v_unused_1747_);
                        v___x_1741_ = v___x_1739_;
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1739_);
                        v___x_1741_ = leanh::lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1733_);
                    v_a_1748_ = leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1755_ = (!leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1739_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1748_);
                        leanh::lean_dec(v___x_1739_);
                        v___x_1750_ = leanh::lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1742_ == 0 {
                    leanh::lean_ctor_set(v___x_1741_, 0, v_a_1733_);
                    v___x_1744_ = v___x_1741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1733_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1744_;
            }
            5 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1753_;
            }
            7 => {
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1762_, 1);
                    leanh::lean_ctor_set(v___x_1762_, 0, v_a_1758_);
                    v___x_1765_ = v___x_1762_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1758_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1765_;
            }
            9 => {
                if v_isShared_1772_ == 0 {
                    v___x_1774_ = v___x_1771_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___boxed(
    mut v_x_1777_: *mut leanh::LeanObject,
    mut v_ctx_x3f_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
    mut v___y_1787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1777_, v_ctx_x3f_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
    leanh::lean_dec(v___y_1786_);
    leanh::lean_dec_ref(v___y_1785_);
    leanh::lean_dec(v___y_1784_);
    leanh::lean_dec_ref(v___y_1783_);
    leanh::lean_dec(v___y_1782_);
    leanh::lean_dec_ref(v___y_1781_);
    leanh::lean_dec(v___y_1780_);
    leanh::lean_dec_ref(v___y_1779_);
    return v_res_1788_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(
    mut v___y_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = lean_st_ref_get(v___y_1791_);
    v_env_1794_ = leanh::lean_ctor_get(v___x_1793_, 0);
    leanh::lean_inc_ref(v_env_1794_);
    leanh::lean_dec(v___x_1793_);
    v___x_1795_ = lean_st_ref_get(v___y_1789_);
    v_mctx_1796_ = leanh::lean_ctor_get(v___x_1795_, 0);
    leanh::lean_inc_ref(v_mctx_1796_);
    leanh::lean_dec(v___x_1795_);
    v_options_1797_ = leanh::lean_ctor_get(v___y_1790_, 2);
    v_currNamespace_1798_ = leanh::lean_ctor_get(v___y_1790_, 6);
    v_openDecls_1799_ = leanh::lean_ctor_get(v___y_1790_, 7);
    v___x_1800_ = lean_st_ref_get(v___y_1791_);
    v_ngen_1801_ = leanh::lean_ctor_get(v___x_1800_, 2);
    leanh::lean_inc_ref(v_ngen_1801_);
    leanh::lean_dec(v___x_1800_);
    v___x_1802_ = leanh::lean_box(0);
    v___x_1803_ = l_Lean_instInhabitedFileMap_default;
    leanh::lean_inc(v_openDecls_1799_);
    leanh::lean_inc(v_currNamespace_1798_);
    leanh::lean_inc_ref(v_options_1797_);
    v___x_1804_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_1804_, 0, v_env_1794_);
    leanh::lean_ctor_set(v___x_1804_, 1, v___x_1802_);
    leanh::lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    leanh::lean_ctor_set(v___x_1804_, 3, v_mctx_1796_);
    leanh::lean_ctor_set(v___x_1804_, 4, v_options_1797_);
    leanh::lean_ctor_set(v___x_1804_, 5, v_currNamespace_1798_);
    leanh::lean_ctor_set(v___x_1804_, 6, v_openDecls_1799_);
    leanh::lean_ctor_set(v___x_1804_, 7, v_ngen_1801_);
    v___x_1805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1806_, v___y_1807_, v___y_1808_);
    leanh::lean_dec(v___y_1808_);
    leanh::lean_dec_ref(v___y_1807_);
    leanh::lean_dec(v___y_1806_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v_fileMap_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut v_unused_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1820_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1816_, v___y_1817_, v___y_1818_);
                v_a_1821_ = leanh::lean_ctor_get(v___x_1820_, 0);
                v_isSharedCheck_1845_ = (!leanh::lean_is_exclusive(v___x_1820_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1821_);
                    leanh::lean_dec(v___x_1820_);
                    v___x_1823_ = leanh::lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1825_ = leanh::lean_ctor_get(v___y_1817_, 1);
                v_env_1826_ = leanh::lean_ctor_get(v_a_1821_, 0);
                v_mctx_1827_ = leanh::lean_ctor_get(v_a_1821_, 3);
                v_options_1828_ = leanh::lean_ctor_get(v_a_1821_, 4);
                v_currNamespace_1829_ = leanh::lean_ctor_get(v_a_1821_, 5);
                v_openDecls_1830_ = leanh::lean_ctor_get(v_a_1821_, 6);
                v_ngen_1831_ = leanh::lean_ctor_get(v_a_1821_, 7);
                v_isSharedCheck_1842_ = (!leanh::lean_is_exclusive(v_a_1821_)) as u8;
                if v_isSharedCheck_1842_ == 0 {
                    v_unused_1843_ = leanh::lean_ctor_get(v_a_1821_, 2);
                    leanh::lean_dec(v_unused_1843_);
                    v_unused_1844_ = leanh::lean_ctor_get(v_a_1821_, 1);
                    leanh::lean_dec(v_unused_1844_);
                    v___x_1833_ = v_a_1821_;
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ngen_1831_);
                    leanh::lean_inc(v_openDecls_1830_);
                    leanh::lean_inc(v_currNamespace_1829_);
                    leanh::lean_inc(v_options_1828_);
                    leanh::lean_inc(v_mctx_1827_);
                    leanh::lean_inc(v_env_1826_);
                    leanh::lean_dec(v_a_1821_);
                    v___x_1833_ = leanh::lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1835_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_fileMap_1825_);
                if v_isShared_1834_ == 0 {
                    leanh::lean_ctor_set(v___x_1833_, 2, v_fileMap_1825_);
                    leanh::lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_fileMap_1825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_mctx_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_options_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_currNamespace_1829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_openDecls_1830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_ngen_1831_);
                    v___x_1837_ = v_reuseFailAlloc_1841_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    leanh::lean_ctor_set(v___x_1823_, 0, v___x_1837_);
                    v___x_1839_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
                    v___x_1839_ = v_reuseFailAlloc_1840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0___boxed(
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    leanh::lean_dec(v___y_1853_);
    leanh::lean_dec_ref(v___y_1852_);
    leanh::lean_dec(v___y_1851_);
    leanh::lean_dec_ref(v___y_1850_);
    leanh::lean_dec(v___y_1849_);
    leanh::lean_dec_ref(v___y_1848_);
    leanh::lean_dec(v___y_1847_);
    leanh::lean_dec_ref(v___y_1846_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1865_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
                v_a_1866_ = leanh::lean_ctor_get(v___x_1865_, 0);
                v_isSharedCheck_1875_ = (!leanh::lean_is_exclusive(v___x_1865_)) as u8;
                if v_isSharedCheck_1875_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1866_);
                    leanh::lean_dec(v___x_1865_);
                    v___x_1868_ = leanh::lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1870_, 0, v_a_1866_);
                v___x_1871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1871_, 0, v___x_1870_);
                if v_isShared_1869_ == 0 {
                    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1871_);
                    v___x_1873_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
                    v___x_1873_ = v_reuseFailAlloc_1874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed(
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
    leanh::lean_dec(v___y_1883_);
    leanh::lean_dec_ref(v___y_1882_);
    leanh::lean_dec(v___y_1881_);
    leanh::lean_dec_ref(v___y_1880_);
    leanh::lean_dec(v___y_1879_);
    leanh::lean_dec_ref(v___y_1878_);
    leanh::lean_dec(v___y_1877_);
    leanh::lean_dec_ref(v___y_1876_);
    return v_res_1885_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(
    mut v_x_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1897_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0;
    v___x_1898_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1887_, v___f_1897_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(
    mut v_x_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(
            v_x_1899_,
            v___y_1900_,
            v___y_1901_,
            v___y_1902_,
            v___y_1903_,
            v___y_1904_,
            v___y_1905_,
            v___y_1906_,
            v___y_1907_,
        );
    leanh::lean_dec(v___y_1907_);
    leanh::lean_dec_ref(v___y_1906_);
    leanh::lean_dec(v___y_1905_);
    leanh::lean_dec_ref(v___y_1904_);
    leanh::lean_dec(v___y_1903_);
    leanh::lean_dec_ref(v___y_1902_);
    leanh::lean_dec(v___y_1901_);
    leanh::lean_dec_ref(v___y_1900_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(
    mut v_00_u03b1_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ =
        l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(
            v_x_1911_,
            v___y_1912_,
            v___y_1913_,
            v___y_1914_,
            v___y_1915_,
            v___y_1916_,
            v___y_1917_,
            v___y_1918_,
            v___y_1919_,
        );
    return v___x_1921_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed(
    mut v_00_u03b1_1922_: *mut leanh::LeanObject,
    mut v_x_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(
        v_00_u03b1_1922_,
        v_x_1923_,
        v___y_1924_,
        v___y_1925_,
        v___y_1926_,
        v___y_1927_,
        v___y_1928_,
        v___y_1929_,
        v___y_1930_,
        v___y_1931_,
    );
    leanh::lean_dec(v___y_1931_);
    leanh::lean_dec_ref(v___y_1930_);
    leanh::lean_dec(v___y_1929_);
    leanh::lean_dec_ref(v___y_1928_);
    leanh::lean_dec(v___y_1927_);
    leanh::lean_dec_ref(v___y_1926_);
    leanh::lean_dec(v___y_1925_);
    leanh::lean_dec_ref(v___y_1924_);
    return v_res_1933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(
    mut v_atLocal_1934_: *mut leanh::LeanObject,
    mut v_as_1935_: *mut leanh::LeanObject,
    mut v_sz_1936_: usize,
    mut v_i_1937_: usize,
    mut v_b_1938_: u8,
    mut v___y_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v_a_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1953_ = lean_usize_dec_lt(v_i_1937_, v_sz_1936_);
                if v___x_1953_ == 0 {
                    leanh::lean_dec_ref(v_atLocal_1934_);
                    v___x_1954_ = leanh::lean_box((v_b_1938_) as usize);
                    v___x_1955_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
                    return v___x_1955_;
                } else {
                    v_a_1956_ = lean_array_uget_borrowed(v_as_1935_, v_i_1937_);
                    leanh::lean_inc(v_a_1956_);
                    v___x_1957_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_1956_,
                        v___y_1943_,
                        v___y_1945_,
                        v___y_1946_,
                    );
                    if leanh::lean_obj_tag(v___x_1957_) == 0 {
                        v_a_1958_ = leanh::lean_ctor_get(v___x_1957_, 0);
                        leanh::lean_inc(v_a_1958_);
                        leanh::lean_dec_ref_known(v___x_1957_, 1);
                        v___x_1959_ = l_Lean_LocalDecl_isImplementationDetail(v_a_1958_);
                        leanh::lean_dec(v_a_1958_);
                        if v___x_1959_ == 0 {
                            leanh::lean_inc_ref(v_atLocal_1934_);
                            leanh::lean_inc(v_a_1956_);
                            v___x_1960_ = leanh::lean_apply_1(v_atLocal_1934_, v_a_1956_);
                            v___x_1961_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_withMainContext___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            leanh::lean_closure_set(
                                v___x_1961_,
                                0,
                                leanh::lean_box(0),
                            );
                            leanh::lean_closure_set(v___x_1961_, 1, v___x_1960_);
                            v___x_1962_ = leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                            leanh::lean_closure_set(
                                v___x_1962_,
                                0,
                                leanh::lean_box(0),
                            );
                            leanh::lean_closure_set(v___x_1962_, 1, v___x_1961_);
                            v___x_1963_ = l_Lean_Elab_Tactic_tryTactic___redArg(
                                v___x_1962_,
                                v___y_1939_,
                                v___y_1940_,
                                v___y_1941_,
                                v___y_1942_,
                                v___y_1943_,
                                v___y_1944_,
                                v___y_1945_,
                                v___y_1946_,
                            );
                            if leanh::lean_obj_tag(v___x_1963_) == 0 {
                                if v_b_1938_ == 0 {
                                    v_a_1964_ = leanh::lean_ctor_get(v___x_1963_, 0);
                                    leanh::lean_inc(v_a_1964_);
                                    leanh::lean_dec_ref_known(v___x_1963_, 1);
                                    v___x_1965_ = (leanh::lean_unbox(v_a_1964_) as u8);
                                    leanh::lean_dec(v_a_1964_);
                                    v_a_1949_ = v___x_1965_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_1963_, 1);
                                    v_a_1949_ = v_b_1938_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_atLocal_1934_);
                                return v___x_1963_;
                            }
                        } else {
                            v_a_1949_ = v_b_1938_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_atLocal_1934_);
                        v_a_1966_ = leanh::lean_ctor_get(v___x_1957_, 0);
                        v_isSharedCheck_1973_ =
                            (!leanh::lean_is_exclusive(v___x_1957_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1968_ = v___x_1957_;
                            v_isShared_1969_ = v_isSharedCheck_1973_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1966_);
                            leanh::lean_dec(v___x_1957_);
                            v___x_1968_ = leanh::lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_1973_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1950_ = 1usize;
                v___x_1951_ = lean_usize_add(v_i_1937_, v___x_1950_);
                v_i_1937_ = v___x_1951_;
                v_b_1938_ = v_a_1949_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1969_ == 0 {
                    v___x_1971_ = v___x_1968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
                    v___x_1971_ = v_reuseFailAlloc_1972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1___boxed(
    mut v_atLocal_1974_: *mut leanh::LeanObject,
    mut v_as_1975_: *mut leanh::LeanObject,
    mut v_sz_1976_: *mut leanh::LeanObject,
    mut v_i_1977_: *mut leanh::LeanObject,
    mut v_b_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1988_: usize = 0;
    let mut v_i_boxed_1989_: usize = 0;
    let mut v_b_boxed_1990_: u8 = 0;
    let mut v_res_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1988_ = leanh::lean_unbox_usize(v_sz_1976_);
    leanh::lean_dec(v_sz_1976_);
    v_i_boxed_1989_ = leanh::lean_unbox_usize(v_i_1977_);
    leanh::lean_dec(v_i_1977_);
    v_b_boxed_1990_ = (leanh::lean_unbox(v_b_1978_) as u8);
    v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1974_, v_as_1975_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_boxed_1990_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
    leanh::lean_dec(v___y_1986_);
    leanh::lean_dec_ref(v___y_1985_);
    leanh::lean_dec(v___y_1984_);
    leanh::lean_dec_ref(v___y_1983_);
    leanh::lean_dec(v___y_1982_);
    leanh::lean_dec_ref(v___y_1981_);
    leanh::lean_dec(v___y_1980_);
    leanh::lean_dec_ref(v___y_1979_);
    leanh::lean_dec_ref(v_as_1975_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___lam__0(
    mut v_atLocal_1992_: *mut leanh::LeanObject,
    mut v_a_1993_: u8,
    mut v_failed_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2007_: usize = 0;
    let mut v___x_2008_: usize = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2004_ = leanh::lean_ctor_get(v___y_1999_, 2);
                v___x_2005_ = l_Lean_LocalContext_getFVarIds(v_lctx_2004_);
                v___x_2006_ = l_Array_reverse___redArg(v___x_2005_);
                v_sz_2007_ = lean_array_size(v___x_2006_);
                v___x_2008_ = 0usize;
                v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1992_, v___x_2006_, v_sz_2007_, v___x_2008_, v_a_1993_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                leanh::lean_dec_ref(v___x_2006_);
                if leanh::lean_obj_tag(v___x_2009_) == 0 {
                    v_a_2010_ = leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2030_ = (!leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2030_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2010_);
                        leanh::lean_dec(v___x_2009_);
                        v___x_2012_ = leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2002_);
                    leanh::lean_dec_ref(v___y_2001_);
                    leanh::lean_dec(v___y_2000_);
                    leanh::lean_dec_ref(v___y_1999_);
                    leanh::lean_dec(v___y_1998_);
                    leanh::lean_dec_ref(v___y_1997_);
                    leanh::lean_dec(v___y_1996_);
                    leanh::lean_dec_ref(v___y_1995_);
                    leanh::lean_dec_ref(v_failed_1994_);
                    v_a_2031_ = leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2038_ = (!leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2033_ = v___x_2009_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2031_);
                        leanh::lean_dec(v___x_2009_);
                        v___x_2033_ = leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2014_ = (leanh::lean_unbox(v_a_2010_) as u8);
                leanh::lean_dec(v_a_2010_);
                if v___x_2014_ == 0 {
                    leanh::lean_del_object(v___x_2012_);
                    v___x_2015_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_1996_,
                        v___y_1999_,
                        v___y_2000_,
                        v___y_2001_,
                        v___y_2002_,
                    );
                    if leanh::lean_obj_tag(v___x_2015_) == 0 {
                        v_a_2016_ = leanh::lean_ctor_get(v___x_2015_, 0);
                        leanh::lean_inc(v_a_2016_);
                        leanh::lean_dec_ref_known(v___x_2015_, 1);
                        v___x_2017_ = leanh::lean_apply_10(
                            v_failed_1994_,
                            v_a_2016_,
                            v___y_1995_,
                            v___y_1996_,
                            v___y_1997_,
                            v___y_1998_,
                            v___y_1999_,
                            v___y_2000_,
                            v___y_2001_,
                            v___y_2002_,
                            leanh::lean_box(0),
                        );
                        return v___x_2017_;
                    } else {
                        leanh::lean_dec(v___y_2002_);
                        leanh::lean_dec_ref(v___y_2001_);
                        leanh::lean_dec(v___y_2000_);
                        leanh::lean_dec_ref(v___y_1999_);
                        leanh::lean_dec(v___y_1998_);
                        leanh::lean_dec_ref(v___y_1997_);
                        leanh::lean_dec(v___y_1996_);
                        leanh::lean_dec_ref(v___y_1995_);
                        leanh::lean_dec_ref(v_failed_1994_);
                        v_a_2018_ = leanh::lean_ctor_get(v___x_2015_, 0);
                        v_isSharedCheck_2025_ =
                            (!leanh::lean_is_exclusive(v___x_2015_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_2015_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2018_);
                            leanh::lean_dec(v___x_2015_);
                            v___x_2020_ = leanh::lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2002_);
                    leanh::lean_dec_ref(v___y_2001_);
                    leanh::lean_dec(v___y_2000_);
                    leanh::lean_dec_ref(v___y_1999_);
                    leanh::lean_dec(v___y_1998_);
                    leanh::lean_dec_ref(v___y_1997_);
                    leanh::lean_dec(v___y_1996_);
                    leanh::lean_dec_ref(v___y_1995_);
                    leanh::lean_dec_ref(v_failed_1994_);
                    v___x_2026_ = leanh::lean_box(0);
                    if v_isShared_2013_ == 0 {
                        leanh::lean_ctor_set(v___x_2012_, 0, v___x_2026_);
                        v___x_2028_ = v___x_2012_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                        v___x_2028_ = v_reuseFailAlloc_2029_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2021_ == 0 {
                    v___x_2023_ = v___x_2020_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2023_;
            }
            4 => {
                return v___x_2028_;
            }
            5 => {
                if v_isShared_2034_ == 0 {
                    v___x_2036_ = v___x_2033_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___lam__0___boxed(
    mut v_atLocal_2039_: *mut leanh::LeanObject,
    mut v_a_2040_: *mut leanh::LeanObject,
    mut v_failed_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
    mut v___y_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_17057__boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_17057__boxed_2051_ = (leanh::lean_unbox(v_a_2040_) as u8);
    v_res_2052_ = l_Lean_Elab_Tactic_withLocation___lam__0(
        v_atLocal_2039_,
        v_a_17057__boxed_2051_,
        v_failed_2041_,
        v___y_2042_,
        v___y_2043_,
        v___y_2044_,
        v___y_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
        v___y_2049_,
    );
    return v_res_2052_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(
    mut v___x_2053_: *mut leanh::LeanObject,
    mut v_atLocal_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
    mut v___y_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2064_ = l_Lean_Elab_Tactic_getFVarId(
                    v___x_2053_,
                    v___y_2055_,
                    v___y_2056_,
                    v___y_2057_,
                    v___y_2058_,
                    v___y_2059_,
                    v___y_2060_,
                    v___y_2061_,
                    v___y_2062_,
                );
                if leanh::lean_obj_tag(v___x_2064_) == 0 {
                    v_a_2065_ = leanh::lean_ctor_get(v___x_2064_, 0);
                    leanh::lean_inc(v_a_2065_);
                    leanh::lean_dec_ref_known(v___x_2064_, 1);
                    v___x_2066_ = leanh::lean_apply_10(
                        v_atLocal_2054_,
                        v_a_2065_,
                        v___y_2055_,
                        v___y_2056_,
                        v___y_2057_,
                        v___y_2058_,
                        v___y_2059_,
                        v___y_2060_,
                        v___y_2061_,
                        v___y_2062_,
                        leanh::lean_box(0),
                    );
                    return v___x_2066_;
                } else {
                    leanh::lean_dec(v___y_2062_);
                    leanh::lean_dec_ref(v___y_2061_);
                    leanh::lean_dec(v___y_2060_);
                    leanh::lean_dec_ref(v___y_2059_);
                    leanh::lean_dec(v___y_2058_);
                    leanh::lean_dec_ref(v___y_2057_);
                    leanh::lean_dec(v___y_2056_);
                    leanh::lean_dec_ref(v___y_2055_);
                    leanh::lean_dec_ref(v_atLocal_2054_);
                    v_a_2067_ = leanh::lean_ctor_get(v___x_2064_, 0);
                    v_isSharedCheck_2074_ = (!leanh::lean_is_exclusive(v___x_2064_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2064_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2067_);
                        leanh::lean_dec(v___x_2064_);
                        v___x_2069_ = leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed(
    mut v___x_2075_: *mut leanh::LeanObject,
    mut v_atLocal_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_2075_, v_atLocal_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
    return v_res_2086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(
    mut v_atLocal_2087_: *mut leanh::LeanObject,
    mut v_as_2088_: *mut leanh::LeanObject,
    mut v_i_2089_: usize,
    mut v_stop_2090_: usize,
    mut v_b_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: usize = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2101_ = lean_usize_dec_eq(v_i_2089_, v_stop_2090_);
                if v___x_2101_ == 0 {
                    v___x_2102_ = lean_array_uget_borrowed(v_as_2088_, v_i_2089_);
                    leanh::lean_inc_ref(v_atLocal_2087_);
                    leanh::lean_inc(v___x_2102_);
                    v___f_2103_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                    leanh::lean_closure_set(v___f_2103_, 0, v___x_2102_);
                    leanh::lean_closure_set(v___f_2103_, 1, v_atLocal_2087_);
                    v___x_2104_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_2103_,
                        v___y_2092_,
                        v___y_2093_,
                        v___y_2094_,
                        v___y_2095_,
                        v___y_2096_,
                        v___y_2097_,
                        v___y_2098_,
                        v___y_2099_,
                    );
                    if leanh::lean_obj_tag(v___x_2104_) == 0 {
                        v_a_2105_ = leanh::lean_ctor_get(v___x_2104_, 0);
                        leanh::lean_inc(v_a_2105_);
                        leanh::lean_dec_ref_known(v___x_2104_, 1);
                        v___x_2106_ = 1usize;
                        v___x_2107_ = lean_usize_add(v_i_2089_, v___x_2106_);
                        v_i_2089_ = v___x_2107_;
                        v_b_2091_ = v_a_2105_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_atLocal_2087_);
                        return v___x_2104_;
                    }
                } else {
                    leanh::lean_dec_ref(v_atLocal_2087_);
                    v___x_2109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2109_, 0, v_b_2091_);
                    return v___x_2109_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(
    mut v_atLocal_2110_: *mut leanh::LeanObject,
    mut v_as_2111_: *mut leanh::LeanObject,
    mut v_i_2112_: *mut leanh::LeanObject,
    mut v_stop_2113_: *mut leanh::LeanObject,
    mut v_b_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
    mut v___y_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2124_: usize = 0;
    let mut v_stop_boxed_2125_: usize = 0;
    let mut v_res_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2124_ = leanh::lean_unbox_usize(v_i_2112_);
    leanh::lean_dec(v_i_2112_);
    v_stop_boxed_2125_ = leanh::lean_unbox_usize(v_stop_2113_);
    leanh::lean_dec(v_stop_2113_);
    v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_2110_, v_as_2111_, v_i_boxed_2124_, v_stop_boxed_2125_, v_b_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    leanh::lean_dec(v___y_2122_);
    leanh::lean_dec_ref(v___y_2121_);
    leanh::lean_dec(v___y_2120_);
    leanh::lean_dec_ref(v___y_2119_);
    leanh::lean_dec(v___y_2118_);
    leanh::lean_dec_ref(v___y_2117_);
    leanh::lean_dec(v___y_2116_);
    leanh::lean_dec_ref(v___y_2115_);
    leanh::lean_dec_ref(v_as_2111_);
    return v_res_2126_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation(
    mut v_loc_2127_: *mut leanh::LeanObject,
    mut v_atLocal_2128_: *mut leanh::LeanObject,
    mut v_atTarget_2129_: *mut leanh::LeanObject,
    mut v_failed_2130_: *mut leanh::LeanObject,
    mut v_a_2131_: *mut leanh::LeanObject,
    mut v_a_2132_: *mut leanh::LeanObject,
    mut v_a_2133_: *mut leanh::LeanObject,
    mut v_a_2134_: *mut leanh::LeanObject,
    mut v_a_2135_: *mut leanh::LeanObject,
    mut v_a_2136_: *mut leanh::LeanObject,
    mut v_a_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___y_2155_: u8 = 0;
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_unused_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2170_: u8 = 0;
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_a_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_hypotheses_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2189_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_loc_2127_) == 0 {
                    v___x_2140_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_withMainContext___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___x_2140_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_2140_, 1, v_atTarget_2129_);
                    v___x_2141_ = leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                    leanh::lean_closure_set(v___x_2141_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_2141_, 1, v___x_2140_);
                    v___x_2142_ = l_Lean_Elab_Tactic_tryTactic___redArg(
                        v___x_2141_,
                        v_a_2131_,
                        v_a_2132_,
                        v_a_2133_,
                        v_a_2134_,
                        v_a_2135_,
                        v_a_2136_,
                        v_a_2137_,
                        v_a_2138_,
                    );
                    if leanh::lean_obj_tag(v___x_2142_) == 0 {
                        v_a_2143_ = leanh::lean_ctor_get(v___x_2142_, 0);
                        leanh::lean_inc(v_a_2143_);
                        leanh::lean_dec_ref_known(v___x_2142_, 1);
                        v___x_2144_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_2132_, v_a_2134_, v_a_2136_, v_a_2138_,
                        );
                        if leanh::lean_obj_tag(v___x_2144_) == 0 {
                            v_a_2145_ = leanh::lean_ctor_get(v___x_2144_, 0);
                            leanh::lean_inc(v_a_2145_);
                            leanh::lean_dec_ref_known(v___x_2144_, 1);
                            v___x_2146_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v_a_2132_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
                            );
                            if leanh::lean_obj_tag(v___x_2146_) == 0 {
                                leanh::lean_dec(v_a_2145_);
                                v_a_2147_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                leanh::lean_inc(v_a_2147_);
                                leanh::lean_dec_ref_known(v___x_2146_, 1);
                                v___f_2148_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_withLocation___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_2148_, 0, v_atLocal_2128_);
                                leanh::lean_closure_set(v___f_2148_, 1, v_a_2143_);
                                leanh::lean_closure_set(v___f_2148_, 2, v_failed_2130_);
                                v___x_2149_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_2147_, v___f_2148_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
                                return v___x_2149_;
                            } else {
                                leanh::lean_dec(v_a_2143_);
                                leanh::lean_dec_ref(v_failed_2130_);
                                leanh::lean_dec_ref(v_atLocal_2128_);
                                v_a_2150_ = leanh::lean_ctor_get(v___x_2146_, 0);
                                v_isSharedCheck_2171_ =
                                    (!leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                if v_isSharedCheck_2171_ == 0 {
                                    v___x_2152_ = v___x_2146_;
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2150_);
                                    leanh::lean_dec(v___x_2146_);
                                    v___x_2152_ = leanh::lean_box(0);
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2143_);
                            leanh::lean_dec_ref(v_failed_2130_);
                            leanh::lean_dec_ref(v_atLocal_2128_);
                            v_a_2172_ = leanh::lean_ctor_get(v___x_2144_, 0);
                            v_isSharedCheck_2179_ =
                                (!leanh::lean_is_exclusive(v___x_2144_)) as u8;
                            if v_isSharedCheck_2179_ == 0 {
                                v___x_2174_ = v___x_2144_;
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2172_);
                                leanh::lean_dec(v___x_2144_);
                                v___x_2174_ = leanh::lean_box(0);
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_failed_2130_);
                        leanh::lean_dec_ref(v_atLocal_2128_);
                        v_a_2180_ = leanh::lean_ctor_get(v___x_2142_, 0);
                        v_isSharedCheck_2187_ =
                            (!leanh::lean_is_exclusive(v___x_2142_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2142_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2180_);
                            leanh::lean_dec(v___x_2142_);
                            v___x_2182_ = leanh::lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_failed_2130_);
                    v_hypotheses_2188_ = leanh::lean_ctor_get(v_loc_2127_, 0);
                    v_type_2189_ = leanh::lean_ctor_get_uint8(
                        v_loc_2127_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_2196_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2197_ = lean_array_get_size(v_hypotheses_2188_);
                    v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
                    if v___x_2198_ == 0 {
                        leanh::lean_dec_ref(v_atLocal_2128_);
                        state = 10;
                        continue;
                    } else {
                        v___x_2199_ = leanh::lean_box(0);
                        v___x_2200_ = lean_nat_dec_le(v___x_2197_, v___x_2197_);
                        if v___x_2200_ == 0 {
                            if v___x_2198_ == 0 {
                                leanh::lean_dec_ref(v_atLocal_2128_);
                                state = 10;
                                continue;
                            } else {
                                v___x_2201_ = 0usize;
                                v___x_2202_ = lean_usize_of_nat(v___x_2197_);
                                v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_2128_, v_hypotheses_2188_, v___x_2201_, v___x_2202_, v___x_2199_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
                                v___y_2195_ = v___x_2203_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v___x_2204_ = 0usize;
                            v___x_2205_ = lean_usize_of_nat(v___x_2197_);
                            v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_2128_, v_hypotheses_2188_, v___x_2204_, v___x_2205_, v___x_2199_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
                            v___y_2195_ = v___x_2206_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2169_ = l_Lean_Exception_isInterrupt(v_a_2150_);
                if v___x_2169_ == 0 {
                    leanh::lean_inc(v_a_2150_);
                    v___x_2170_ = l_Lean_Exception_isRuntime(v_a_2150_);
                    v___y_2155_ = v___x_2170_;
                    state = 2;
                    continue;
                } else {
                    v___y_2155_ = v___x_2169_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_2155_ == 0 {
                    leanh::lean_del_object(v___x_2152_);
                    leanh::lean_dec(v_a_2150_);
                    v___x_2156_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_2145_,
                        v___y_2155_,
                        v_a_2132_,
                        v_a_2133_,
                        v_a_2134_,
                        v_a_2135_,
                        v_a_2136_,
                        v_a_2137_,
                        v_a_2138_,
                    );
                    if leanh::lean_obj_tag(v___x_2156_) == 0 {
                        v_isSharedCheck_2164_ =
                            (!leanh::lean_is_exclusive(v___x_2156_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v_unused_2165_ = leanh::lean_ctor_get(v___x_2156_, 0);
                            leanh::lean_dec(v_unused_2165_);
                            v___x_2158_ = v___x_2156_;
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2156_);
                            v___x_2158_ = leanh::lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_2156_;
                    }
                } else {
                    leanh::lean_dec(v_a_2145_);
                    if v_isShared_2153_ == 0 {
                        v___x_2167_ = v___x_2152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2150_);
                        v___x_2167_ = v_reuseFailAlloc_2168_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2160_ = leanh::lean_box(0);
                if v_isShared_2159_ == 0 {
                    leanh::lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2162_;
            }
            5 => {
                return v___x_2167_;
            }
            6 => {
                if v_isShared_2175_ == 0 {
                    v___x_2177_ = v___x_2174_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
                    v___x_2177_ = v_reuseFailAlloc_2178_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2177_;
            }
            8 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2185_;
            }
            10 => {
                if v_type_2189_ == 0 {
                    leanh::lean_dec_ref(v_atTarget_2129_);
                    v___x_2191_ = leanh::lean_box(0);
                    v___x_2192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
                    return v___x_2192_;
                } else {
                    v___x_2193_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v_atTarget_2129_,
                        v_a_2131_,
                        v_a_2132_,
                        v_a_2133_,
                        v_a_2134_,
                        v_a_2135_,
                        v_a_2136_,
                        v_a_2137_,
                        v_a_2138_,
                    );
                    return v___x_2193_;
                }
            }
            11 => {
                if leanh::lean_obj_tag(v___y_2195_) == 0 {
                    leanh::lean_dec_ref_known(v___y_2195_, 1);
                    state = 10;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_atTarget_2129_);
                    return v___y_2195_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___boxed(
    mut v_loc_2207_: *mut leanh::LeanObject,
    mut v_atLocal_2208_: *mut leanh::LeanObject,
    mut v_atTarget_2209_: *mut leanh::LeanObject,
    mut v_failed_2210_: *mut leanh::LeanObject,
    mut v_a_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v_a_2213_: *mut leanh::LeanObject,
    mut v_a_2214_: *mut leanh::LeanObject,
    mut v_a_2215_: *mut leanh::LeanObject,
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
    mut v_a_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Lean_Elab_Tactic_withLocation(
        v_loc_2207_,
        v_atLocal_2208_,
        v_atTarget_2209_,
        v_failed_2210_,
        v_a_2211_,
        v_a_2212_,
        v_a_2213_,
        v_a_2214_,
        v_a_2215_,
        v_a_2216_,
        v_a_2217_,
        v_a_2218_,
    );
    leanh::lean_dec(v_a_2218_);
    leanh::lean_dec_ref(v_a_2217_);
    leanh::lean_dec(v_a_2216_);
    leanh::lean_dec_ref(v_a_2215_);
    leanh::lean_dec(v_a_2214_);
    leanh::lean_dec_ref(v_a_2213_);
    leanh::lean_dec(v_a_2212_);
    leanh::lean_dec_ref(v_a_2211_);
    leanh::lean_dec(v_loc_2207_);
    return v_res_2220_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(
    mut v___y_2221_: *mut leanh::LeanObject,
    mut v___y_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
    mut v___y_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_2226_, v___y_2227_, v___y_2228_);
    return v___x_2230_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(
    mut v___y_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
    mut v___y_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
    mut v___y_2238_: *mut leanh::LeanObject,
    mut v___y_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
    leanh::lean_dec(v___y_2238_);
    leanh::lean_dec_ref(v___y_2237_);
    leanh::lean_dec(v___y_2236_);
    leanh::lean_dec_ref(v___y_2235_);
    leanh::lean_dec(v___y_2234_);
    leanh::lean_dec_ref(v___y_2233_);
    leanh::lean_dec(v___y_2232_);
    leanh::lean_dec_ref(v___y_2231_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(
    mut v___y_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
    mut v___y_2245_: *mut leanh::LeanObject,
    mut v___y_2246_: *mut leanh::LeanObject,
    mut v___y_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_2248_);
    return v___x_2250_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
    mut v___y_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
    leanh::lean_dec(v___y_2258_);
    leanh::lean_dec_ref(v___y_2257_);
    leanh::lean_dec(v___y_2256_);
    leanh::lean_dec_ref(v___y_2255_);
    leanh::lean_dec(v___y_2254_);
    leanh::lean_dec_ref(v___y_2253_);
    leanh::lean_dec(v___y_2252_);
    leanh::lean_dec_ref(v___y_2251_);
    return v_res_2260_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(
    mut v_00_u03b1_2261_: *mut leanh::LeanObject,
    mut v_x_2262_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
    mut v___y_2270_: *mut leanh::LeanObject,
    mut v___y_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_2262_, v_ctx_x3f_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
    return v___x_2273_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(
    mut v_00_u03b1_2274_: *mut leanh::LeanObject,
    mut v_x_2275_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
    mut v___y_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_2274_, v_x_2275_, v_ctx_x3f_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
    leanh::lean_dec(v___y_2284_);
    leanh::lean_dec_ref(v___y_2283_);
    leanh::lean_dec(v___y_2282_);
    leanh::lean_dec_ref(v___y_2281_);
    leanh::lean_dec(v___y_2280_);
    leanh::lean_dec_ref(v___y_2279_);
    leanh::lean_dec(v___y_2278_);
    leanh::lean_dec_ref(v___y_2277_);
    return v_res_2286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Location(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Location(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Location(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Location(builtin);
}