// Lean compiler output
// Module: Lean.Elab.Tactic.Location
// Imports: Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_9, lean_apply_10, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 84, 121, 112, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut LeanObject,5573707264546329628 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_expandLocation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_expandLocation___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value)
                as *mut LeanObject,
            1262264483427375750 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_expandLocation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__2_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_Tactic_expandLocation___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx(
    mut v_x_1144_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1144_) == 0 {
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        v___x_1145_ = lean_unsigned_to_nat(0);
        return v___x_1145_;
    } else {
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        v___x_1146_ = lean_unsigned_to_nat(1);
        return v___x_1146_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx___boxed(
    mut v_x_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Elab_Tactic_Location_ctorIdx(v_x_1147_);
    lean_dec(v_x_1147_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___redArg(
    mut v_t_1149_: *mut LeanObject,
    mut v_k_1150_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1149_) == 0 {
        return v_k_1150_;
    } else {
        let mut v_hypotheses_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_1152_: u8 = 0;
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
        v_hypotheses_1151_ = lean_ctor_get(v_t_1149_, 0);
        lean_inc_ref(v_hypotheses_1151_);
        v_type_1152_ = lean_ctor_get_uint8(
            v_t_1149_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        lean_dec_ref_known(v_t_1149_, 1);
        v___x_1153_ = lean_box((v_type_1152_) as usize);
        v___x_1154_ = lean_apply_2(v_k_1150_, v_hypotheses_1151_, v___x_1153_);
        return v___x_1154_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim(
    mut v_motive_1155_: *mut LeanObject,
    mut v_ctorIdx_1156_: *mut LeanObject,
    mut v_t_1157_: *mut LeanObject,
    mut v_h_1158_: *mut LeanObject,
    mut v_k_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1157_, v_k_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___boxed(
    mut v_motive_1161_: *mut LeanObject,
    mut v_ctorIdx_1162_: *mut LeanObject,
    mut v_t_1163_: *mut LeanObject,
    mut v_h_1164_: *mut LeanObject,
    mut v_k_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1166_: *mut LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_Elab_Tactic_Location_ctorElim(
        v_motive_1161_,
        v_ctorIdx_1162_,
        v_t_1163_,
        v_h_1164_,
        v_k_1165_,
    );
    lean_dec(v_ctorIdx_1162_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(
    mut v_t_1167_: *mut LeanObject,
    mut v_wildcard_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1167_, v_wildcard_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim(
    mut v_motive_1170_: *mut LeanObject,
    mut v_t_1171_: *mut LeanObject,
    mut v_h_1172_: *mut LeanObject,
    mut v_wildcard_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1171_, v_wildcard_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim___redArg(
    mut v_t_1175_: *mut LeanObject,
    mut v_targets_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1175_, v_targets_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim(
    mut v_motive_1178_: *mut LeanObject,
    mut v_t_1179_: *mut LeanObject,
    mut v_h_1180_: *mut LeanObject,
    mut v_targets_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1179_, v_targets_1181_);
    return v___x_1182_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(
    mut v_as_1192_: *mut LeanObject,
    mut v_i_1193_: usize,
    mut v_stop_1194_: usize,
    mut v_b_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1201_ = lean_usize_dec_eq(v_i_1193_, v_stop_1194_);
                if v___x_1201_ == 0 {
                    v___x_1202_ = lean_array_uget_borrowed(v_as_1192_, v_i_1193_);
                    lean_inc(v___x_1202_);
                    v___x_1203_ = l_Lean_Syntax_getKind(v___x_1202_);
                    v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4;
                    v___x_1205_ = lean_name_eq(v___x_1203_, v___x_1204_);
                    lean_dec(v___x_1203_);
                    if v___x_1205_ == 0 {
                        lean_inc(v___x_1202_);
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
    mut v_as_1207_: *mut LeanObject,
    mut v_i_1208_: *mut LeanObject,
    mut v_stop_1209_: *mut LeanObject,
    mut v_b_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1211_: usize = 0;
    let mut v_stop_boxed_1212_: usize = 0;
    let mut v_res_1213_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1211_ = lean_unbox_usize(v_i_1208_);
    lean_dec(v_i_1208_);
    v_stop_boxed_1212_ = lean_unbox_usize(v_stop_1209_);
    lean_dec(v_stop_1209_);
    v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_as_1207_, v_i_boxed_1211_, v_stop_boxed_1212_, v_b_1210_);
    lean_dec_ref(v_as_1207_);
    return v_res_1213_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation(
    mut v_stx_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_locationHyps_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numTurnstiles_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___x_1240_: u8 = 0;
    let mut v___x_1241_: usize = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1223_ = lean_unsigned_to_nat(1);
                v_arg_1224_ = l_Lean_Syntax_getArg(v_stx_1222_, v___x_1223_);
                lean_inc(v_arg_1224_);
                v___x_1225_ = l_Lean_Syntax_getKind(v_arg_1224_);
                v___x_1226_ = l_Lean_Elab_Tactic_expandLocation___closed__1;
                v___x_1227_ = lean_name_eq(v___x_1225_, v___x_1226_);
                lean_dec(v___x_1225_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = lean_unsigned_to_nat(0);
                    v___x_1229_ = l_Lean_Syntax_getArg(v_arg_1224_, v___x_1228_);
                    lean_dec(v_arg_1224_);
                    v_locationHyps_1230_ = l_Lean_Syntax_getArgs(v___x_1229_);
                    lean_dec(v___x_1229_);
                    v___x_1231_ = lean_array_get_size(v_locationHyps_1230_);
                    v___x_1238_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
                    v___x_1239_ = lean_nat_dec_lt(v___x_1228_, v___x_1231_);
                    if v___x_1239_ == 0 {
                        lean_dec_ref(v_locationHyps_1230_);
                        v___y_1233_ = v___x_1238_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1240_ = lean_nat_dec_le(v___x_1231_, v___x_1231_);
                        if v___x_1240_ == 0 {
                            if v___x_1239_ == 0 {
                                lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1238_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1241_ = 0usize;
                                v___x_1242_ = lean_usize_of_nat(v___x_1231_);
                                v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1241_, v___x_1242_, v___x_1238_);
                                lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1243_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1244_ = 0usize;
                            v___x_1245_ = lean_usize_of_nat(v___x_1231_);
                            v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1244_, v___x_1245_, v___x_1238_);
                            lean_dec_ref(v_locationHyps_1230_);
                            v___y_1233_ = v___x_1246_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_arg_1224_);
                    v___x_1247_ = lean_box(0);
                    return v___x_1247_;
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v___y_1233_);
                v_numTurnstiles_1235_ = lean_nat_sub(v___x_1231_, v___x_1234_);
                v___x_1236_ = lean_nat_dec_lt(v___x_1228_, v_numTurnstiles_1235_);
                lean_dec(v_numTurnstiles_1235_);
                v___x_1237_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_1237_, 0, v___y_1233_);
                lean_ctor_set_uint8(
                    v___x_1237_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1236_,
                );
                return v___x_1237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation___boxed(
    mut v_stx_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_Tactic_expandLocation(v_stx_1248_);
    lean_dec(v_stx_1248_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation(
    mut v_stx_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1251_: u8 = 0;
    v___x_1251_ = l_Lean_Syntax_isNone(v_stx_1250_);
    if v___x_1251_ == 0 {
        let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
        v___x_1252_ = lean_unsigned_to_nat(0);
        v___x_1253_ = l_Lean_Syntax_getArg(v_stx_1250_, v___x_1252_);
        v___x_1254_ = l_Lean_Elab_Tactic_expandLocation(v___x_1253_);
        lean_dec(v___x_1253_);
        return v___x_1254_;
    } else {
        let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
        v___x_1255_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
        v___x_1256_ = lean_alloc_ctor(1, 1, (1) as u32);
        lean_ctor_set(v___x_1256_, 0, v___x_1255_);
        lean_ctor_set_uint8(
            v___x_1256_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_1251_,
        );
        return v___x_1256_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation___boxed(
    mut v_stx_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_1257_);
    lean_dec(v_stx_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(
    mut v_x_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1263_);
    lean_inc_ref(v___y_1262_);
    lean_inc(v___y_1261_);
    lean_inc_ref(v___y_1260_);
    v___x_1269_ = lean_apply_9(
        v_x_1259_,
        v___y_1260_,
        v___y_1261_,
        v___y_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        lean_box(0),
    );
    return v___x_1269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(
    mut v_x_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1280_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1274_);
    lean_dec_ref(v___y_1273_);
    lean_dec(v___y_1272_);
    lean_dec_ref(v___y_1271_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(
    mut v_mvarId_1281_: *mut LeanObject,
    mut v_x_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1286_);
                lean_inc_ref(v___y_1285_);
                lean_inc(v___y_1284_);
                lean_inc_ref(v___y_1283_);
                v___f_1292_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_1292_, 0, v_x_1282_);
                lean_closure_set(v___f_1292_, 1, v___y_1283_);
                lean_closure_set(v___f_1292_, 2, v___y_1284_);
                lean_closure_set(v___f_1292_, 3, v___y_1285_);
                lean_closure_set(v___f_1292_, 4, v___y_1286_);
                v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1281_,
                    v___f_1292_,
                    v___y_1287_,
                    v___y_1288_,
                    v___y_1289_,
                    v___y_1290_,
                );
                if lean_obj_tag(v___x_1293_) == 0 {
                    return v___x_1293_;
                } else {
                    v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
                    v_isSharedCheck_1301_ = (!lean_is_exclusive(v___x_1293_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1296_ = v___x_1293_;
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1294_);
                        lean_dec(v___x_1293_);
                        v___x_1296_ = lean_box(0);
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
                    v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
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
    mut v_mvarId_1302_: *mut LeanObject,
    mut v_x_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1311_);
    lean_dec_ref(v___y_1310_);
    lean_dec(v___y_1309_);
    lean_dec_ref(v___y_1308_);
    lean_dec(v___y_1307_);
    lean_dec_ref(v___y_1306_);
    lean_dec(v___y_1305_);
    lean_dec_ref(v___y_1304_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(
    mut v_00_u03b1_1314_: *mut LeanObject,
    mut v_mvarId_1315_: *mut LeanObject,
    mut v_x_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1327_: *mut LeanObject,
    mut v_mvarId_1328_: *mut LeanObject,
    mut v_x_1329_: *mut LeanObject,
    mut v___y_1330_: *mut LeanObject,
    mut v___y_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1339_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1337_);
    lean_dec_ref(v___y_1336_);
    lean_dec(v___y_1335_);
    lean_dec_ref(v___y_1334_);
    lean_dec(v___y_1333_);
    lean_dec_ref(v___y_1332_);
    lean_dec(v___y_1331_);
    lean_dec_ref(v___y_1330_);
    return v_res_1339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(
    mut v___x_1340_: *mut LeanObject,
    mut v_ctx_x3f_1341_: *mut LeanObject,
    mut v_sz_1342_: usize,
    mut v_i_1343_: usize,
    mut v_bs_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
    mut v___y_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
    mut v___y_1351_: *mut LeanObject,
    mut v___y_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
                if v___x_1354_ == 0 {
                    lean_dec_ref(v_ctx_x3f_1341_);
                    v___x_1355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1355_, 0, v_bs_1344_);
                    return v___x_1355_;
                } else {
                    v_assignment_1356_ = lean_ctor_get(v___x_1340_, 0);
                    lean_inc_ref(v_ctx_x3f_1341_);
                    lean_inc(v___y_1352_);
                    lean_inc_ref(v___y_1351_);
                    lean_inc(v___y_1350_);
                    lean_inc_ref(v___y_1349_);
                    lean_inc(v___y_1348_);
                    lean_inc_ref(v___y_1347_);
                    lean_inc(v___y_1346_);
                    lean_inc_ref(v___y_1345_);
                    v___x_1357_ = lean_apply_9(
                        v_ctx_x3f_1341_,
                        v___y_1345_,
                        v___y_1346_,
                        v___y_1347_,
                        v___y_1348_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                        v___y_1352_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1357_) == 0 {
                        v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
                        lean_inc(v_a_1358_);
                        lean_dec_ref_known(v___x_1357_, 1);
                        v_v_1359_ = lean_array_uget(v_bs_1344_, v_i_1343_);
                        v___x_1360_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1361_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1360_);
                        v_tree_1368_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_1359_, v_assignment_1356_);
                        if lean_obj_tag(v_a_1358_) == 0 {
                            v_a_1363_ = v_tree_1368_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1369_ = lean_ctor_get(v_a_1358_, 0);
                            lean_inc(v_val_1369_);
                            lean_dec_ref_known(v_a_1358_, 1);
                            v___x_1370_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1370_, 0, v_val_1369_);
                            lean_ctor_set(v___x_1370_, 1, v_tree_1368_);
                            v_a_1363_ = v___x_1370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_bs_1344_);
                        lean_dec_ref(v_ctx_x3f_1341_);
                        v_a_1371_ = lean_ctor_get(v___x_1357_, 0);
                        v_isSharedCheck_1378_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1357_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1371_);
                            lean_dec(v___x_1357_);
                            v___x_1373_ = lean_box(0);
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
                    v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
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
    mut v___x_1379_: *mut LeanObject,
    mut v_ctx_x3f_1380_: *mut LeanObject,
    mut v_sz_1381_: *mut LeanObject,
    mut v_i_1382_: *mut LeanObject,
    mut v_bs_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1393_: usize = 0;
    let mut v_i_boxed_1394_: usize = 0;
    let mut v_res_1395_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1381_);
    lean_dec(v_sz_1381_);
    v_i_boxed_1394_ = lean_unbox_usize(v_i_1382_);
    lean_dec(v_i_1382_);
    v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1379_, v_ctx_x3f_1380_, v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
    lean_dec(v___y_1391_);
    lean_dec_ref(v___y_1390_);
    lean_dec(v___y_1389_);
    lean_dec_ref(v___y_1388_);
    lean_dec(v___y_1387_);
    lean_dec_ref(v___y_1386_);
    lean_dec(v___y_1385_);
    lean_dec_ref(v___y_1384_);
    lean_dec_ref(v___x_1379_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(
    mut v___x_1396_: *mut LeanObject,
    mut v_ctx_x3f_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_sz_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut v_a_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_vs_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v_sz_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1445_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1452_: u8 = 0;
    let mut v_a_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1398_) == 0 {
                    v_cs_1408_ = lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1434_ = (!lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1410_ = v_x_1398_;
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_1408_);
                        lean_dec(v_x_1398_);
                        v___x_1410_ = lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1435_ = lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1461_ = (!lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1437_ = v_x_1398_;
                        v_isShared_1438_ = v_isSharedCheck_1461_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_vs_1435_);
                        lean_dec(v_x_1398_);
                        v___x_1437_ = lean_box(0);
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
                if lean_obj_tag(v___x_1414_) == 0 {
                    v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1425_ = (!lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1425_ == 0 {
                        v___x_1417_ = v___x_1414_;
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1415_);
                        lean_dec(v___x_1414_);
                        v___x_1417_ = lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1410_);
                    v_a_1426_ = lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1433_ = (!lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1428_ = v___x_1414_;
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1426_);
                        lean_dec(v___x_1414_);
                        v___x_1428_ = lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1411_ == 0 {
                    lean_ctor_set(v___x_1410_, 0, v_a_1415_);
                    v___x_1420_ = v___x_1410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1418_ == 0 {
                    lean_ctor_set(v___x_1417_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
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
                    v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
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
                if lean_obj_tag(v___x_1441_) == 0 {
                    v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1452_ = (!lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1452_ == 0 {
                        v___x_1444_ = v___x_1441_;
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1442_);
                        lean_dec(v___x_1441_);
                        v___x_1444_ = lean_box(0);
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1437_);
                    v_a_1453_ = lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1460_ = (!lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1460_ == 0 {
                        v___x_1455_ = v___x_1441_;
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1453_);
                        lean_dec(v___x_1441_);
                        v___x_1455_ = lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1438_ == 0 {
                    lean_ctor_set(v___x_1437_, 0, v_a_1442_);
                    v___x_1447_ = v___x_1437_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1442_);
                    v___x_1447_ = v_reuseFailAlloc_1451_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1445_ == 0 {
                    lean_ctor_set(v___x_1444_, 0, v___x_1447_);
                    v___x_1449_ = v___x_1444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
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
                    v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
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
    mut v___x_1462_: *mut LeanObject,
    mut v_ctx_x3f_1463_: *mut LeanObject,
    mut v_sz_1464_: usize,
    mut v_i_1465_: usize,
    mut v_bs_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1476_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
                if v___x_1476_ == 0 {
                    lean_dec_ref(v_ctx_x3f_1463_);
                    v___x_1477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1477_, 0, v_bs_1466_);
                    return v___x_1477_;
                } else {
                    v_v_1478_ = lean_array_uget_borrowed(v_bs_1466_, v_i_1465_);
                    lean_inc(v_v_1478_);
                    lean_inc_ref(v_ctx_x3f_1463_);
                    v___x_1479_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1462_, v_ctx_x3f_1463_, v_v_1478_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
                    if lean_obj_tag(v___x_1479_) == 0 {
                        v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
                        lean_inc(v_a_1480_);
                        lean_dec_ref_known(v___x_1479_, 1);
                        v___x_1481_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1482_ = lean_array_uset(v_bs_1466_, v_i_1465_, v___x_1481_);
                        v___x_1483_ = 1usize;
                        v___x_1484_ = lean_usize_add(v_i_1465_, v___x_1483_);
                        v___x_1485_ = lean_array_uset(v_bs_x27_1482_, v_i_1465_, v_a_1480_);
                        v_i_1465_ = v___x_1484_;
                        v_bs_1466_ = v___x_1485_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1466_);
                        lean_dec_ref(v_ctx_x3f_1463_);
                        v_a_1487_ = lean_ctor_get(v___x_1479_, 0);
                        v_isSharedCheck_1494_ = (!lean_is_exclusive(v___x_1479_)) as u8;
                        if v_isSharedCheck_1494_ == 0 {
                            v___x_1489_ = v___x_1479_;
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1487_);
                            lean_dec(v___x_1479_);
                            v___x_1489_ = lean_box(0);
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
                    v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
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
    mut v___x_1495_: *mut LeanObject,
    mut v_ctx_x3f_1496_: *mut LeanObject,
    mut v_sz_1497_: *mut LeanObject,
    mut v_i_1498_: *mut LeanObject,
    mut v_bs_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
    mut v___y_1501_: *mut LeanObject,
    mut v___y_1502_: *mut LeanObject,
    mut v___y_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
    mut v___y_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1509_: usize = 0;
    let mut v_i_boxed_1510_: usize = 0;
    let mut v_res_1511_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1509_ = lean_unbox_usize(v_sz_1497_);
    lean_dec(v_sz_1497_);
    v_i_boxed_1510_ = lean_unbox_usize(v_i_1498_);
    lean_dec(v_i_1498_);
    v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_1495_, v_ctx_x3f_1496_, v_sz_boxed_1509_, v_i_boxed_1510_, v_bs_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
    lean_dec(v___y_1507_);
    lean_dec_ref(v___y_1506_);
    lean_dec(v___y_1505_);
    lean_dec_ref(v___y_1504_);
    lean_dec(v___y_1503_);
    lean_dec_ref(v___y_1502_);
    lean_dec(v___y_1501_);
    lean_dec_ref(v___y_1500_);
    lean_dec_ref(v___x_1495_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(
    mut v___x_1512_: *mut LeanObject,
    mut v_ctx_x3f_1513_: *mut LeanObject,
    mut v_x_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
    mut v___y_1516_: *mut LeanObject,
    mut v___y_1517_: *mut LeanObject,
    mut v___y_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
    mut v___y_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1524_: *mut LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1512_, v_ctx_x3f_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
    lean_dec(v___y_1522_);
    lean_dec_ref(v___y_1521_);
    lean_dec(v___y_1520_);
    lean_dec_ref(v___y_1519_);
    lean_dec(v___y_1518_);
    lean_dec_ref(v___y_1517_);
    lean_dec(v___y_1516_);
    lean_dec_ref(v___y_1515_);
    lean_dec_ref(v___x_1512_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(
    mut v___x_1525_: *mut LeanObject,
    mut v_ctx_x3f_1526_: *mut LeanObject,
    mut v_t_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
    mut v___y_1532_: *mut LeanObject,
    mut v___y_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shift_1540_: usize = 0;
    let mut v_tailOff_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_a_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_a_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1537_ = lean_ctor_get(v_t_1527_, 0);
                v_tail_1538_ = lean_ctor_get(v_t_1527_, 1);
                v_size_1539_ = lean_ctor_get(v_t_1527_, 2);
                v_shift_1540_ = lean_ctor_get_usize(v_t_1527_, 4);
                v_tailOff_1541_ = lean_ctor_get(v_t_1527_, 3);
                v_isSharedCheck_1577_ = (!lean_is_exclusive(v_t_1527_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1543_ = v_t_1527_;
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_tailOff_1541_);
                    lean_inc(v_size_1539_);
                    lean_inc(v_tail_1538_);
                    lean_inc(v_root_1537_);
                    lean_dec(v_t_1527_);
                    v___x_1543_ = lean_box(0);
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_ctx_x3f_1526_);
                v___x_1545_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1525_, v_ctx_x3f_1526_, v_root_1537_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                if lean_obj_tag(v___x_1545_) == 0 {
                    v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
                    lean_inc(v_a_1546_);
                    lean_dec_ref_known(v___x_1545_, 1);
                    v_sz_1547_ = lean_array_size(v_tail_1538_);
                    v___x_1548_ = 0usize;
                    v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1525_, v_ctx_x3f_1526_, v_sz_1547_, v___x_1548_, v_tail_1538_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                    if lean_obj_tag(v___x_1549_) == 0 {
                        v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1560_ = (!lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1560_ == 0 {
                            v___x_1552_ = v___x_1549_;
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1550_);
                            lean_dec(v___x_1549_);
                            v___x_1552_ = lean_box(0);
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1546_);
                        lean_del_object(v___x_1543_);
                        lean_dec(v_tailOff_1541_);
                        lean_dec(v_size_1539_);
                        v_a_1561_ = lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1568_ = (!lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1568_ == 0 {
                            v___x_1563_ = v___x_1549_;
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1561_);
                            lean_dec(v___x_1549_);
                            v___x_1563_ = lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1543_);
                    lean_dec(v_tailOff_1541_);
                    lean_dec(v_size_1539_);
                    lean_dec_ref(v_tail_1538_);
                    lean_dec_ref(v_ctx_x3f_1526_);
                    v_a_1569_ = lean_ctor_get(v___x_1545_, 0);
                    v_isSharedCheck_1576_ = (!lean_is_exclusive(v___x_1545_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1571_ = v___x_1545_;
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1569_);
                        lean_dec(v___x_1545_);
                        v___x_1571_ = lean_box(0);
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1544_ == 0 {
                    lean_ctor_set(v___x_1543_, 1, v_a_1550_);
                    lean_ctor_set(v___x_1543_, 0, v_a_1546_);
                    v___x_1555_ = v___x_1543_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ =
                        lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1546_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1550_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_size_1539_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_tailOff_1541_);
                    lean_ctor_set_usize(v_reuseFailAlloc_1559_, 4, v_shift_1540_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1553_ == 0 {
                    lean_ctor_set(v___x_1552_, 0, v___x_1555_);
                    v___x_1557_ = v___x_1552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
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
                    v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
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
                    v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
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
    mut v___x_1578_: *mut LeanObject,
    mut v_ctx_x3f_1579_: *mut LeanObject,
    mut v_t_1580_: *mut LeanObject,
    mut v___y_1581_: *mut LeanObject,
    mut v___y_1582_: *mut LeanObject,
    mut v___y_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_1578_, v_ctx_x3f_1579_, v_t_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
    lean_dec(v___y_1588_);
    lean_dec_ref(v___y_1587_);
    lean_dec(v___y_1586_);
    lean_dec_ref(v___y_1585_);
    lean_dec(v___y_1584_);
    lean_dec_ref(v___y_1583_);
    lean_dec(v___y_1582_);
    lean_dec_ref(v___y_1581_);
    lean_dec_ref(v___x_1578_);
    return v_res_1590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(
    mut v___y_1591_: *mut LeanObject,
    mut v_ctx_x3f_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
    mut v___y_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v_a_1600_: *mut LeanObject,
    mut v_a_x3f_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_enabled_1624_: u8 = 0;
    let mut v_assignment_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_st_ref_get(v___y_1591_);
                v_infoState_1604_ = lean_ctor_get(v___x_1603_, 7);
                lean_inc_ref(v_infoState_1604_);
                lean_dec(v___x_1603_);
                v_trees_1605_ = lean_ctor_get(v_infoState_1604_, 2);
                lean_inc_ref(v_trees_1605_);
                v___x_1606_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_1604_, v_ctx_x3f_1592_, v_trees_1605_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1591_);
                lean_dec_ref(v_infoState_1604_);
                if lean_obj_tag(v___x_1606_) == 0 {
                    v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1645_ = (!lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1609_ = v___x_1606_;
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1607_);
                        lean_dec(v___x_1606_);
                        v___x_1609_ = lean_box(0);
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_1600_);
                    v_a_1646_ = lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1653_ = (!lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1648_ = v___x_1606_;
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1646_);
                        lean_dec(v___x_1606_);
                        v___x_1648_ = lean_box(0);
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1611_ = lean_st_ref_take(v___y_1591_);
                v_infoState_1612_ = lean_ctor_get(v___x_1611_, 7);
                v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
                v_nextMacroScope_1614_ = lean_ctor_get(v___x_1611_, 1);
                v_ngen_1615_ = lean_ctor_get(v___x_1611_, 2);
                v_auxDeclNGen_1616_ = lean_ctor_get(v___x_1611_, 3);
                v_traceState_1617_ = lean_ctor_get(v___x_1611_, 4);
                v_cache_1618_ = lean_ctor_get(v___x_1611_, 5);
                v_messages_1619_ = lean_ctor_get(v___x_1611_, 6);
                v_snapshotTasks_1620_ = lean_ctor_get(v___x_1611_, 8);
                v_isSharedCheck_1644_ = (!lean_is_exclusive(v___x_1611_)) as u8;
                if v_isSharedCheck_1644_ == 0 {
                    v___x_1622_ = v___x_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1620_);
                    lean_inc(v_infoState_1612_);
                    lean_inc(v_messages_1619_);
                    lean_inc(v_cache_1618_);
                    lean_inc(v_traceState_1617_);
                    lean_inc(v_auxDeclNGen_1616_);
                    lean_inc(v_ngen_1615_);
                    lean_inc(v_nextMacroScope_1614_);
                    lean_inc(v_env_1613_);
                    lean_dec(v___x_1611_);
                    v___x_1622_ = lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1624_ = lean_ctor_get_uint8(
                    v_infoState_1612_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1625_ = lean_ctor_get(v_infoState_1612_, 0);
                v_lazyAssignment_1626_ = lean_ctor_get(v_infoState_1612_, 1);
                v_isSharedCheck_1642_ = (!lean_is_exclusive(v_infoState_1612_)) as u8;
                if v_isSharedCheck_1642_ == 0 {
                    v_unused_1643_ = lean_ctor_get(v_infoState_1612_, 2);
                    lean_dec(v_unused_1643_);
                    v___x_1628_ = v_infoState_1612_;
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1626_);
                    lean_inc(v_assignment_1625_);
                    lean_dec(v_infoState_1612_);
                    v___x_1628_ = lean_box(0);
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1630_ = l_Lean_PersistentArray_append___redArg(v_a_1600_, v_a_1607_);
                lean_dec(v_a_1607_);
                if v_isShared_1629_ == 0 {
                    lean_ctor_set(v___x_1628_, 2, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_assignment_1625_);
                    lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_lazyAssignment_1626_);
                    lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1630_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1641_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1624_,
                    );
                    v___x_1632_ = v_reuseFailAlloc_1641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1623_ == 0 {
                    lean_ctor_set(v___x_1622_, 7, v___x_1632_);
                    v___x_1634_ = v___x_1622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_env_1613_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_nextMacroScope_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_ngen_1615_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_auxDeclNGen_1616_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_traceState_1617_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 5, v_cache_1618_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 6, v_messages_1619_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 7, v___x_1632_);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 8, v_snapshotTasks_1620_);
                    v___x_1634_ = v_reuseFailAlloc_1640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1635_ = lean_st_ref_set(v___y_1591_, v___x_1634_);
                v___x_1636_ = lean_box(0);
                if v_isShared_1610_ == 0 {
                    lean_ctor_set(v___x_1609_, 0, v___x_1636_);
                    v___x_1638_ = v___x_1609_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
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
                    v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
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
    mut v___y_1654_: *mut LeanObject,
    mut v_ctx_x3f_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v_a_1663_: *mut LeanObject,
    mut v_a_x3f_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1666_: *mut LeanObject = core::ptr::null_mut();
    v_res_1666_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1654_, v_ctx_x3f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v_a_1663_, v_a_x3f_1664_);
    lean_dec(v_a_x3f_1664_);
    lean_dec_ref(v___y_1662_);
    lean_dec(v___y_1661_);
    lean_dec_ref(v___y_1660_);
    lean_dec(v___y_1659_);
    lean_dec_ref(v___y_1658_);
    lean_dec(v___y_1657_);
    lean_dec_ref(v___y_1656_);
    lean_dec(v___y_1654_);
    return v_res_1666_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    v___x_1667_ = lean_unsigned_to_nat(32);
    v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
    v___x_1669_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1669_, 0, v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = 5usize;
    v___x_1671_ = lean_unsigned_to_nat(0);
    v___x_1672_ = lean_unsigned_to_nat(32);
    v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
    v___x_1674_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_1675_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    lean_ctor_set(v___x_1675_, 2, v___x_1671_);
    lean_ctor_set(v___x_1675_, 3, v___x_1671_);
    lean_ctor_set_usize(v___x_1675_, 4, v___x_1670_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v_enabled_1694_: u8 = 0;
    let mut v_assignment_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_unused_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1678_ = lean_st_ref_get(v___y_1676_);
                v_infoState_1679_ = lean_ctor_get(v___x_1678_, 7);
                lean_inc_ref(v_infoState_1679_);
                lean_dec(v___x_1678_);
                v_trees_1680_ = lean_ctor_get(v_infoState_1679_, 2);
                lean_inc_ref(v_trees_1680_);
                lean_dec_ref(v_infoState_1679_);
                v___x_1681_ = lean_st_ref_take(v___y_1676_);
                v_infoState_1682_ = lean_ctor_get(v___x_1681_, 7);
                v_env_1683_ = lean_ctor_get(v___x_1681_, 0);
                v_nextMacroScope_1684_ = lean_ctor_get(v___x_1681_, 1);
                v_ngen_1685_ = lean_ctor_get(v___x_1681_, 2);
                v_auxDeclNGen_1686_ = lean_ctor_get(v___x_1681_, 3);
                v_traceState_1687_ = lean_ctor_get(v___x_1681_, 4);
                v_cache_1688_ = lean_ctor_get(v___x_1681_, 5);
                v_messages_1689_ = lean_ctor_get(v___x_1681_, 6);
                v_snapshotTasks_1690_ = lean_ctor_get(v___x_1681_, 8);
                v_isSharedCheck_1711_ = (!lean_is_exclusive(v___x_1681_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v___x_1692_ = v___x_1681_;
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1690_);
                    lean_inc(v_infoState_1682_);
                    lean_inc(v_messages_1689_);
                    lean_inc(v_cache_1688_);
                    lean_inc(v_traceState_1687_);
                    lean_inc(v_auxDeclNGen_1686_);
                    lean_inc(v_ngen_1685_);
                    lean_inc(v_nextMacroScope_1684_);
                    lean_inc(v_env_1683_);
                    lean_dec(v___x_1681_);
                    v___x_1692_ = lean_box(0);
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1694_ = lean_ctor_get_uint8(
                    v_infoState_1682_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_1695_ = lean_ctor_get(v_infoState_1682_, 0);
                v_lazyAssignment_1696_ = lean_ctor_get(v_infoState_1682_, 1);
                v_isSharedCheck_1709_ = (!lean_is_exclusive(v_infoState_1682_)) as u8;
                if v_isSharedCheck_1709_ == 0 {
                    v_unused_1710_ = lean_ctor_get(v_infoState_1682_, 2);
                    lean_dec(v_unused_1710_);
                    v___x_1698_ = v_infoState_1682_;
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_1696_);
                    lean_inc(v_assignment_1695_);
                    lean_dec(v_infoState_1682_);
                    v___x_1698_ = lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1700_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
                if v_isShared_1699_ == 0 {
                    lean_ctor_set(v___x_1698_, 2, v___x_1700_);
                    v___x_1702_ = v___x_1698_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_assignment_1695_);
                    lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_lazyAssignment_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1708_, 2, v___x_1700_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1708_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_1694_,
                    );
                    v___x_1702_ = v_reuseFailAlloc_1708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1693_ == 0 {
                    lean_ctor_set(v___x_1692_, 7, v___x_1702_);
                    v___x_1704_ = v___x_1692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_env_1683_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nextMacroScope_1684_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_ngen_1685_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_auxDeclNGen_1686_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_traceState_1687_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_cache_1688_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_messages_1689_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 7, v___x_1702_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_snapshotTasks_1690_);
                    v___x_1704_ = v_reuseFailAlloc_1707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1705_ = lean_st_ref_set(v___y_1676_, v___x_1704_);
                v___x_1706_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1706_, 0, v_trees_1680_);
                return v___x_1706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1712_);
    lean_dec(v___y_1712_);
    return v_res_1714_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(
    mut v_x_1715_: *mut LeanObject,
    mut v_ctx_x3f_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_1728_: u8 = 0;
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_unused_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_a_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_unused_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1726_ = lean_st_ref_get(v___y_1724_);
                v_infoState_1727_ = lean_ctor_get(v___x_1726_, 7);
                lean_inc_ref(v_infoState_1727_);
                lean_dec(v___x_1726_);
                v_enabled_1728_ = lean_ctor_get_uint8(
                    v_infoState_1727_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_1727_);
                if v_enabled_1728_ == 0 {
                    lean_dec_ref(v_ctx_x3f_1716_);
                    lean_inc(v___y_1724_);
                    lean_inc_ref(v___y_1723_);
                    lean_inc(v___y_1722_);
                    lean_inc_ref(v___y_1721_);
                    lean_inc(v___y_1720_);
                    lean_inc_ref(v___y_1719_);
                    lean_inc(v___y_1718_);
                    lean_inc_ref(v___y_1717_);
                    v___x_1729_ = lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        lean_box(0),
                    );
                    return v___x_1729_;
                } else {
                    v___x_1730_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1724_);
                    v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
                    lean_inc(v_a_1731_);
                    lean_dec_ref(v___x_1730_);
                    lean_inc(v___y_1724_);
                    lean_inc_ref(v___y_1723_);
                    lean_inc(v___y_1722_);
                    lean_inc_ref(v___y_1721_);
                    lean_inc(v___y_1720_);
                    lean_inc_ref(v___y_1719_);
                    lean_inc(v___y_1718_);
                    lean_inc_ref(v___y_1717_);
                    v_r_1732_ = lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_1732_) == 0 {
                        v_a_1733_ = lean_ctor_get(v_r_1732_, 0);
                        v_isSharedCheck_1757_ = (!lean_is_exclusive(v_r_1732_)) as u8;
                        if v_isSharedCheck_1757_ == 0 {
                            v___x_1735_ = v_r_1732_;
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1733_);
                            lean_dec(v_r_1732_);
                            v___x_1735_ = lean_box(0);
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1758_ = lean_ctor_get(v_r_1732_, 0);
                        lean_inc(v_a_1758_);
                        lean_dec_ref_known(v_r_1732_, 1);
                        v___x_1759_ = lean_box(0);
                        v___x_1760_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1759_);
                        if lean_obj_tag(v___x_1760_) == 0 {
                            v_isSharedCheck_1767_ = (!lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v_unused_1768_ = lean_ctor_get(v___x_1760_, 0);
                                lean_dec(v_unused_1768_);
                                v___x_1762_ = v___x_1760_;
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_1760_);
                                v___x_1762_ = lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1758_);
                            v_a_1769_ = lean_ctor_get(v___x_1760_, 0);
                            v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1776_ == 0 {
                                v___x_1771_ = v___x_1760_;
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1769_);
                                lean_dec(v___x_1760_);
                                v___x_1771_ = lean_box(0);
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1733_);
                if v_isShared_1736_ == 0 {
                    lean_ctor_set_tag(v___x_1735_, 1);
                    v___x_1738_ = v___x_1735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1739_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1738_);
                lean_dec_ref(v___x_1738_);
                if lean_obj_tag(v___x_1739_) == 0 {
                    v_isSharedCheck_1746_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v_unused_1747_ = lean_ctor_get(v___x_1739_, 0);
                        lean_dec(v_unused_1747_);
                        v___x_1741_ = v___x_1739_;
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_1739_);
                        v___x_1741_ = lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1733_);
                    v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1739_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1748_);
                        lean_dec(v___x_1739_);
                        v___x_1750_ = lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1742_ == 0 {
                    lean_ctor_set(v___x_1741_, 0, v_a_1733_);
                    v___x_1744_ = v___x_1741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1733_);
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
                    v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
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
                    lean_ctor_set_tag(v___x_1762_, 1);
                    lean_ctor_set(v___x_1762_, 0, v_a_1758_);
                    v___x_1765_ = v___x_1762_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1758_);
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
                    v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
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
    mut v_x_1777_: *mut LeanObject,
    mut v_ctx_x3f_1778_: *mut LeanObject,
    mut v___y_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1788_: *mut LeanObject = core::ptr::null_mut();
    v_res_1788_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1777_, v_ctx_x3f_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
    lean_dec(v___y_1786_);
    lean_dec_ref(v___y_1785_);
    lean_dec(v___y_1784_);
    lean_dec_ref(v___y_1783_);
    lean_dec(v___y_1782_);
    lean_dec_ref(v___y_1781_);
    lean_dec(v___y_1780_);
    lean_dec_ref(v___y_1779_);
    return v_res_1788_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    v___x_1793_ = lean_st_ref_get(v___y_1791_);
    v_env_1794_ = lean_ctor_get(v___x_1793_, 0);
    lean_inc_ref(v_env_1794_);
    lean_dec(v___x_1793_);
    v___x_1795_ = lean_st_ref_get(v___y_1789_);
    v_mctx_1796_ = lean_ctor_get(v___x_1795_, 0);
    lean_inc_ref(v_mctx_1796_);
    lean_dec(v___x_1795_);
    v_options_1797_ = lean_ctor_get(v___y_1790_, 2);
    v_currNamespace_1798_ = lean_ctor_get(v___y_1790_, 6);
    v_openDecls_1799_ = lean_ctor_get(v___y_1790_, 7);
    v___x_1800_ = lean_st_ref_get(v___y_1791_);
    v_ngen_1801_ = lean_ctor_get(v___x_1800_, 2);
    lean_inc_ref(v_ngen_1801_);
    lean_dec(v___x_1800_);
    v___x_1802_ = lean_box(0);
    v___x_1803_ = l_Lean_instInhabitedFileMap_default;
    lean_inc(v_openDecls_1799_);
    lean_inc(v_currNamespace_1798_);
    lean_inc_ref(v_options_1797_);
    v___x_1804_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_1804_, 0, v_env_1794_);
    lean_ctor_set(v___x_1804_, 1, v___x_1802_);
    lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    lean_ctor_set(v___x_1804_, 3, v_mctx_1796_);
    lean_ctor_set(v___x_1804_, 4, v_options_1797_);
    lean_ctor_set(v___x_1804_, 5, v_currNamespace_1798_);
    lean_ctor_set(v___x_1804_, 6, v_openDecls_1799_);
    lean_ctor_set(v___x_1804_, 7, v_ngen_1801_);
    v___x_1805_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(
    mut v___y_1806_: *mut LeanObject,
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1810_: *mut LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1806_, v___y_1807_, v___y_1808_);
    lean_dec(v___y_1808_);
    lean_dec_ref(v___y_1807_);
    lean_dec(v___y_1806_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v_fileMap_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut v_unused_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1820_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1816_, v___y_1817_, v___y_1818_);
                v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
                v_isSharedCheck_1845_ = (!lean_is_exclusive(v___x_1820_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1821_);
                    lean_dec(v___x_1820_);
                    v___x_1823_ = lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1825_ = lean_ctor_get(v___y_1817_, 1);
                v_env_1826_ = lean_ctor_get(v_a_1821_, 0);
                v_mctx_1827_ = lean_ctor_get(v_a_1821_, 3);
                v_options_1828_ = lean_ctor_get(v_a_1821_, 4);
                v_currNamespace_1829_ = lean_ctor_get(v_a_1821_, 5);
                v_openDecls_1830_ = lean_ctor_get(v_a_1821_, 6);
                v_ngen_1831_ = lean_ctor_get(v_a_1821_, 7);
                v_isSharedCheck_1842_ = (!lean_is_exclusive(v_a_1821_)) as u8;
                if v_isSharedCheck_1842_ == 0 {
                    v_unused_1843_ = lean_ctor_get(v_a_1821_, 2);
                    lean_dec(v_unused_1843_);
                    v_unused_1844_ = lean_ctor_get(v_a_1821_, 1);
                    lean_dec(v_unused_1844_);
                    v___x_1833_ = v_a_1821_;
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ngen_1831_);
                    lean_inc(v_openDecls_1830_);
                    lean_inc(v_currNamespace_1829_);
                    lean_inc(v_options_1828_);
                    lean_inc(v_mctx_1827_);
                    lean_inc(v_env_1826_);
                    lean_dec(v_a_1821_);
                    v___x_1833_ = lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1835_ = lean_box(0);
                lean_inc_ref(v_fileMap_1825_);
                if v_isShared_1834_ == 0 {
                    lean_ctor_set(v___x_1833_, 2, v_fileMap_1825_);
                    lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1835_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_fileMap_1825_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_mctx_1827_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_options_1828_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_currNamespace_1829_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_openDecls_1830_);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_ngen_1831_);
                    v___x_1837_ = v_reuseFailAlloc_1841_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    lean_ctor_set(v___x_1823_, 0, v___x_1837_);
                    v___x_1839_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
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
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    lean_dec(v___y_1853_);
    lean_dec_ref(v___y_1852_);
    lean_dec(v___y_1851_);
    lean_dec_ref(v___y_1850_);
    lean_dec(v___y_1849_);
    lean_dec_ref(v___y_1848_);
    lean_dec(v___y_1847_);
    lean_dec_ref(v___y_1846_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1865_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
                v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
                v_isSharedCheck_1875_ = (!lean_is_exclusive(v___x_1865_)) as u8;
                if v_isSharedCheck_1875_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1866_);
                    lean_dec(v___x_1865_);
                    v___x_1868_ = lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1870_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1870_, 0, v_a_1866_);
                v___x_1871_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1871_, 0, v___x_1870_);
                if v_isShared_1869_ == 0 {
                    lean_ctor_set(v___x_1868_, 0, v___x_1871_);
                    v___x_1873_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
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
    mut v___y_1876_: *mut LeanObject,
    mut v___y_1877_: *mut LeanObject,
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1885_: *mut LeanObject = core::ptr::null_mut();
    v_res_1885_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
    lean_dec(v___y_1883_);
    lean_dec_ref(v___y_1882_);
    lean_dec(v___y_1881_);
    lean_dec_ref(v___y_1880_);
    lean_dec(v___y_1879_);
    lean_dec_ref(v___y_1878_);
    lean_dec(v___y_1877_);
    lean_dec_ref(v___y_1876_);
    return v_res_1885_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(
    mut v_x_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    v___f_1897_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0;
    v___x_1898_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1887_, v___f_1897_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(
    mut v_x_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1907_);
    lean_dec_ref(v___y_1906_);
    lean_dec(v___y_1905_);
    lean_dec_ref(v___y_1904_);
    lean_dec(v___y_1903_);
    lean_dec_ref(v___y_1902_);
    lean_dec(v___y_1901_);
    lean_dec_ref(v___y_1900_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(
    mut v_00_u03b1_1910_: *mut LeanObject,
    mut v_x_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1922_: *mut LeanObject,
    mut v_x_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1931_);
    lean_dec_ref(v___y_1930_);
    lean_dec(v___y_1929_);
    lean_dec_ref(v___y_1928_);
    lean_dec(v___y_1927_);
    lean_dec_ref(v___y_1926_);
    lean_dec(v___y_1925_);
    lean_dec_ref(v___y_1924_);
    return v_res_1933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(
    mut v_atLocal_1934_: *mut LeanObject,
    mut v_as_1935_: *mut LeanObject,
    mut v_sz_1936_: usize,
    mut v_i_1937_: usize,
    mut v_b_1938_: u8,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1953_ = lean_usize_dec_lt(v_i_1937_, v_sz_1936_);
                if v___x_1953_ == 0 {
                    lean_dec_ref(v_atLocal_1934_);
                    v___x_1954_ = lean_box((v_b_1938_) as usize);
                    v___x_1955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1955_, 0, v___x_1954_);
                    return v___x_1955_;
                } else {
                    v_a_1956_ = lean_array_uget_borrowed(v_as_1935_, v_i_1937_);
                    lean_inc(v_a_1956_);
                    v___x_1957_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_1956_,
                        v___y_1943_,
                        v___y_1945_,
                        v___y_1946_,
                    );
                    if lean_obj_tag(v___x_1957_) == 0 {
                        v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
                        lean_inc(v_a_1958_);
                        lean_dec_ref_known(v___x_1957_, 1);
                        v___x_1959_ = l_Lean_LocalDecl_isImplementationDetail(v_a_1958_);
                        lean_dec(v_a_1958_);
                        if v___x_1959_ == 0 {
                            lean_inc_ref(v_atLocal_1934_);
                            lean_inc(v_a_1956_);
                            v___x_1960_ = lean_apply_1(v_atLocal_1934_, v_a_1956_);
                            v___x_1961_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_withMainContext___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            lean_closure_set(v___x_1961_, 0, lean_box(0));
                            lean_closure_set(v___x_1961_, 1, v___x_1960_);
                            v___x_1962_ = lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                            lean_closure_set(v___x_1962_, 0, lean_box(0));
                            lean_closure_set(v___x_1962_, 1, v___x_1961_);
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
                            if lean_obj_tag(v___x_1963_) == 0 {
                                if v_b_1938_ == 0 {
                                    v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
                                    lean_inc(v_a_1964_);
                                    lean_dec_ref_known(v___x_1963_, 1);
                                    v___x_1965_ = (lean_unbox(v_a_1964_) as u8);
                                    lean_dec(v_a_1964_);
                                    v_a_1949_ = v___x_1965_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v___x_1963_, 1);
                                    v_a_1949_ = v_b_1938_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_atLocal_1934_);
                                return v___x_1963_;
                            }
                        } else {
                            v_a_1949_ = v_b_1938_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_atLocal_1934_);
                        v_a_1966_ = lean_ctor_get(v___x_1957_, 0);
                        v_isSharedCheck_1973_ = (!lean_is_exclusive(v___x_1957_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1968_ = v___x_1957_;
                            v_isShared_1969_ = v_isSharedCheck_1973_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1966_);
                            lean_dec(v___x_1957_);
                            v___x_1968_ = lean_box(0);
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
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
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
    mut v_atLocal_1974_: *mut LeanObject,
    mut v_as_1975_: *mut LeanObject,
    mut v_sz_1976_: *mut LeanObject,
    mut v_i_1977_: *mut LeanObject,
    mut v_b_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1988_: usize = 0;
    let mut v_i_boxed_1989_: usize = 0;
    let mut v_b_boxed_1990_: u8 = 0;
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1976_);
    lean_dec(v_sz_1976_);
    v_i_boxed_1989_ = lean_unbox_usize(v_i_1977_);
    lean_dec(v_i_1977_);
    v_b_boxed_1990_ = (lean_unbox(v_b_1978_) as u8);
    v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1974_, v_as_1975_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_boxed_1990_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
    lean_dec(v___y_1986_);
    lean_dec_ref(v___y_1985_);
    lean_dec(v___y_1984_);
    lean_dec_ref(v___y_1983_);
    lean_dec(v___y_1982_);
    lean_dec_ref(v___y_1981_);
    lean_dec(v___y_1980_);
    lean_dec_ref(v___y_1979_);
    lean_dec_ref(v_as_1975_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___lam__0(
    mut v_atLocal_1992_: *mut LeanObject,
    mut v_a_1993_: u8,
    mut v_failed_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2007_: usize = 0;
    let mut v___x_2008_: usize = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2004_ = lean_ctor_get(v___y_1999_, 2);
                v___x_2005_ = l_Lean_LocalContext_getFVarIds(v_lctx_2004_);
                v___x_2006_ = l_Array_reverse___redArg(v___x_2005_);
                v_sz_2007_ = lean_array_size(v___x_2006_);
                v___x_2008_ = 0usize;
                v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1992_, v___x_2006_, v_sz_2007_, v___x_2008_, v_a_1993_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                lean_dec_ref(v___x_2006_);
                if lean_obj_tag(v___x_2009_) == 0 {
                    v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2030_ = (!lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2030_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2010_);
                        lean_dec(v___x_2009_);
                        v___x_2012_ = lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2002_);
                    lean_dec_ref(v___y_2001_);
                    lean_dec(v___y_2000_);
                    lean_dec_ref(v___y_1999_);
                    lean_dec(v___y_1998_);
                    lean_dec_ref(v___y_1997_);
                    lean_dec(v___y_1996_);
                    lean_dec_ref(v___y_1995_);
                    lean_dec_ref(v_failed_1994_);
                    v_a_2031_ = lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2033_ = v___x_2009_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2031_);
                        lean_dec(v___x_2009_);
                        v___x_2033_ = lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2014_ = (lean_unbox(v_a_2010_) as u8);
                lean_dec(v_a_2010_);
                if v___x_2014_ == 0 {
                    lean_del_object(v___x_2012_);
                    v___x_2015_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_1996_,
                        v___y_1999_,
                        v___y_2000_,
                        v___y_2001_,
                        v___y_2002_,
                    );
                    if lean_obj_tag(v___x_2015_) == 0 {
                        v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
                        lean_inc(v_a_2016_);
                        lean_dec_ref_known(v___x_2015_, 1);
                        v___x_2017_ = lean_apply_10(
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
                            lean_box(0),
                        );
                        return v___x_2017_;
                    } else {
                        lean_dec(v___y_2002_);
                        lean_dec_ref(v___y_2001_);
                        lean_dec(v___y_2000_);
                        lean_dec_ref(v___y_1999_);
                        lean_dec(v___y_1998_);
                        lean_dec_ref(v___y_1997_);
                        lean_dec(v___y_1996_);
                        lean_dec_ref(v___y_1995_);
                        lean_dec_ref(v_failed_1994_);
                        v_a_2018_ = lean_ctor_get(v___x_2015_, 0);
                        v_isSharedCheck_2025_ = (!lean_is_exclusive(v___x_2015_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_2015_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2018_);
                            lean_dec(v___x_2015_);
                            v___x_2020_ = lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2002_);
                    lean_dec_ref(v___y_2001_);
                    lean_dec(v___y_2000_);
                    lean_dec_ref(v___y_1999_);
                    lean_dec(v___y_1998_);
                    lean_dec_ref(v___y_1997_);
                    lean_dec(v___y_1996_);
                    lean_dec_ref(v___y_1995_);
                    lean_dec_ref(v_failed_1994_);
                    v___x_2026_ = lean_box(0);
                    if v_isShared_2013_ == 0 {
                        lean_ctor_set(v___x_2012_, 0, v___x_2026_);
                        v___x_2028_ = v___x_2012_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
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
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
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
                    v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
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
    mut v_atLocal_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
    mut v_failed_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_17057__boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v_a_17057__boxed_2051_ = (lean_unbox(v_a_2040_) as u8);
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
    mut v___x_2053_: *mut LeanObject,
    mut v_atLocal_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2064_) == 0 {
                    v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
                    lean_inc(v_a_2065_);
                    lean_dec_ref_known(v___x_2064_, 1);
                    v___x_2066_ = lean_apply_10(
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
                        lean_box(0),
                    );
                    return v___x_2066_;
                } else {
                    lean_dec(v___y_2062_);
                    lean_dec_ref(v___y_2061_);
                    lean_dec(v___y_2060_);
                    lean_dec_ref(v___y_2059_);
                    lean_dec(v___y_2058_);
                    lean_dec_ref(v___y_2057_);
                    lean_dec(v___y_2056_);
                    lean_dec_ref(v___y_2055_);
                    lean_dec_ref(v_atLocal_2054_);
                    v_a_2067_ = lean_ctor_get(v___x_2064_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2064_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2064_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2067_);
                        lean_dec(v___x_2064_);
                        v___x_2069_ = lean_box(0);
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
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
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
    mut v___x_2075_: *mut LeanObject,
    mut v_atLocal_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2086_: *mut LeanObject = core::ptr::null_mut();
    v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_2075_, v_atLocal_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
    return v_res_2086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(
    mut v_atLocal_2087_: *mut LeanObject,
    mut v_as_2088_: *mut LeanObject,
    mut v_i_2089_: usize,
    mut v_stop_2090_: usize,
    mut v_b_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: usize = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2101_ = lean_usize_dec_eq(v_i_2089_, v_stop_2090_);
                if v___x_2101_ == 0 {
                    v___x_2102_ = lean_array_uget_borrowed(v_as_2088_, v_i_2089_);
                    lean_inc_ref(v_atLocal_2087_);
                    lean_inc(v___x_2102_);
                    v___f_2103_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                    lean_closure_set(v___f_2103_, 0, v___x_2102_);
                    lean_closure_set(v___f_2103_, 1, v_atLocal_2087_);
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
                    if lean_obj_tag(v___x_2104_) == 0 {
                        v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
                        lean_inc(v_a_2105_);
                        lean_dec_ref_known(v___x_2104_, 1);
                        v___x_2106_ = 1usize;
                        v___x_2107_ = lean_usize_add(v_i_2089_, v___x_2106_);
                        v_i_2089_ = v___x_2107_;
                        v_b_2091_ = v_a_2105_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_atLocal_2087_);
                        return v___x_2104_;
                    }
                } else {
                    lean_dec_ref(v_atLocal_2087_);
                    v___x_2109_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2109_, 0, v_b_2091_);
                    return v___x_2109_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(
    mut v_atLocal_2110_: *mut LeanObject,
    mut v_as_2111_: *mut LeanObject,
    mut v_i_2112_: *mut LeanObject,
    mut v_stop_2113_: *mut LeanObject,
    mut v_b_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
    mut v___y_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
    mut v___y_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2124_: usize = 0;
    let mut v_stop_boxed_2125_: usize = 0;
    let mut v_res_2126_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2124_ = lean_unbox_usize(v_i_2112_);
    lean_dec(v_i_2112_);
    v_stop_boxed_2125_ = lean_unbox_usize(v_stop_2113_);
    lean_dec(v_stop_2113_);
    v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_2110_, v_as_2111_, v_i_boxed_2124_, v_stop_boxed_2125_, v_b_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    lean_dec(v___y_2122_);
    lean_dec_ref(v___y_2121_);
    lean_dec(v___y_2120_);
    lean_dec_ref(v___y_2119_);
    lean_dec(v___y_2118_);
    lean_dec_ref(v___y_2117_);
    lean_dec(v___y_2116_);
    lean_dec_ref(v___y_2115_);
    lean_dec_ref(v_as_2111_);
    return v_res_2126_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation(
    mut v_loc_2127_: *mut LeanObject,
    mut v_atLocal_2128_: *mut LeanObject,
    mut v_atTarget_2129_: *mut LeanObject,
    mut v_failed_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
    mut v_a_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___y_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_unused_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2170_: u8 = 0;
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_a_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_hypotheses_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2189_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_loc_2127_) == 0 {
                    v___x_2140_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_withMainContext___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    lean_closure_set(v___x_2140_, 0, lean_box(0));
                    lean_closure_set(v___x_2140_, 1, v_atTarget_2129_);
                    v___x_2141_ = lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                    lean_closure_set(v___x_2141_, 0, lean_box(0));
                    lean_closure_set(v___x_2141_, 1, v___x_2140_);
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
                    if lean_obj_tag(v___x_2142_) == 0 {
                        v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
                        lean_inc(v_a_2143_);
                        lean_dec_ref_known(v___x_2142_, 1);
                        v___x_2144_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_2132_, v_a_2134_, v_a_2136_, v_a_2138_,
                        );
                        if lean_obj_tag(v___x_2144_) == 0 {
                            v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
                            lean_inc(v_a_2145_);
                            lean_dec_ref_known(v___x_2144_, 1);
                            v___x_2146_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v_a_2132_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
                            );
                            if lean_obj_tag(v___x_2146_) == 0 {
                                lean_dec(v_a_2145_);
                                v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
                                lean_inc(v_a_2147_);
                                lean_dec_ref_known(v___x_2146_, 1);
                                v___f_2148_ = lean_alloc_closure(
                                    l_Lean_Elab_Tactic_withLocation___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                lean_closure_set(v___f_2148_, 0, v_atLocal_2128_);
                                lean_closure_set(v___f_2148_, 1, v_a_2143_);
                                lean_closure_set(v___f_2148_, 2, v_failed_2130_);
                                v___x_2149_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_2147_, v___f_2148_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
                                return v___x_2149_;
                            } else {
                                lean_dec(v_a_2143_);
                                lean_dec_ref(v_failed_2130_);
                                lean_dec_ref(v_atLocal_2128_);
                                v_a_2150_ = lean_ctor_get(v___x_2146_, 0);
                                v_isSharedCheck_2171_ = (!lean_is_exclusive(v___x_2146_)) as u8;
                                if v_isSharedCheck_2171_ == 0 {
                                    v___x_2152_ = v___x_2146_;
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2150_);
                                    lean_dec(v___x_2146_);
                                    v___x_2152_ = lean_box(0);
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2143_);
                            lean_dec_ref(v_failed_2130_);
                            lean_dec_ref(v_atLocal_2128_);
                            v_a_2172_ = lean_ctor_get(v___x_2144_, 0);
                            v_isSharedCheck_2179_ = (!lean_is_exclusive(v___x_2144_)) as u8;
                            if v_isSharedCheck_2179_ == 0 {
                                v___x_2174_ = v___x_2144_;
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2172_);
                                lean_dec(v___x_2144_);
                                v___x_2174_ = lean_box(0);
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_failed_2130_);
                        lean_dec_ref(v_atLocal_2128_);
                        v_a_2180_ = lean_ctor_get(v___x_2142_, 0);
                        v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2142_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2142_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2180_);
                            lean_dec(v___x_2142_);
                            v___x_2182_ = lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_failed_2130_);
                    v_hypotheses_2188_ = lean_ctor_get(v_loc_2127_, 0);
                    v_type_2189_ = lean_ctor_get_uint8(
                        v_loc_2127_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_2196_ = lean_unsigned_to_nat(0);
                    v___x_2197_ = lean_array_get_size(v_hypotheses_2188_);
                    v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
                    if v___x_2198_ == 0 {
                        lean_dec_ref(v_atLocal_2128_);
                        state = 10;
                        continue;
                    } else {
                        v___x_2199_ = lean_box(0);
                        v___x_2200_ = lean_nat_dec_le(v___x_2197_, v___x_2197_);
                        if v___x_2200_ == 0 {
                            if v___x_2198_ == 0 {
                                lean_dec_ref(v_atLocal_2128_);
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
                    lean_inc(v_a_2150_);
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
                    lean_del_object(v___x_2152_);
                    lean_dec(v_a_2150_);
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
                    if lean_obj_tag(v___x_2156_) == 0 {
                        v_isSharedCheck_2164_ = (!lean_is_exclusive(v___x_2156_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v_unused_2165_ = lean_ctor_get(v___x_2156_, 0);
                            lean_dec(v_unused_2165_);
                            v___x_2158_ = v___x_2156_;
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_2156_);
                            v___x_2158_ = lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_2156_;
                    }
                } else {
                    lean_dec(v_a_2145_);
                    if v_isShared_2153_ == 0 {
                        v___x_2167_ = v___x_2152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2150_);
                        v___x_2167_ = v_reuseFailAlloc_2168_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2160_ = lean_box(0);
                if v_isShared_2159_ == 0 {
                    lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
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
                    v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
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
                    lean_dec_ref(v_atTarget_2129_);
                    v___x_2191_ = lean_box(0);
                    v___x_2192_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2192_, 0, v___x_2191_);
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
                if lean_obj_tag(v___y_2195_) == 0 {
                    lean_dec_ref_known(v___y_2195_, 1);
                    state = 10;
                    continue;
                } else {
                    lean_dec_ref(v_atTarget_2129_);
                    return v___y_2195_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___boxed(
    mut v_loc_2207_: *mut LeanObject,
    mut v_atLocal_2208_: *mut LeanObject,
    mut v_atTarget_2209_: *mut LeanObject,
    mut v_failed_2210_: *mut LeanObject,
    mut v_a_2211_: *mut LeanObject,
    mut v_a_2212_: *mut LeanObject,
    mut v_a_2213_: *mut LeanObject,
    mut v_a_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2220_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2218_);
    lean_dec_ref(v_a_2217_);
    lean_dec(v_a_2216_);
    lean_dec_ref(v_a_2215_);
    lean_dec(v_a_2214_);
    lean_dec_ref(v_a_2213_);
    lean_dec(v_a_2212_);
    lean_dec_ref(v_a_2211_);
    lean_dec(v_loc_2207_);
    return v_res_2220_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_2226_, v___y_2227_, v___y_2228_);
    return v___x_2230_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
    lean_dec(v___y_2238_);
    lean_dec_ref(v___y_2237_);
    lean_dec(v___y_2236_);
    lean_dec_ref(v___y_2235_);
    lean_dec(v___y_2234_);
    lean_dec_ref(v___y_2233_);
    lean_dec(v___y_2232_);
    lean_dec_ref(v___y_2231_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_2248_);
    return v___x_2250_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2260_: *mut LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
    lean_dec(v___y_2258_);
    lean_dec_ref(v___y_2257_);
    lean_dec(v___y_2256_);
    lean_dec_ref(v___y_2255_);
    lean_dec(v___y_2254_);
    lean_dec_ref(v___y_2253_);
    lean_dec(v___y_2252_);
    lean_dec_ref(v___y_2251_);
    return v_res_2260_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(
    mut v_00_u03b1_2261_: *mut LeanObject,
    mut v_x_2262_: *mut LeanObject,
    mut v_ctx_x3f_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_2262_, v_ctx_x3f_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
    return v___x_2273_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(
    mut v_00_u03b1_2274_: *mut LeanObject,
    mut v_x_2275_: *mut LeanObject,
    mut v_ctx_x3f_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_2274_, v_x_2275_, v_ctx_x3f_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
    lean_dec(v___y_2284_);
    lean_dec_ref(v___y_2283_);
    lean_dec(v___y_2282_);
    lean_dec_ref(v___y_2281_);
    lean_dec(v___y_2280_);
    lean_dec_ref(v___y_2279_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    return v_res_2286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Location(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Location(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Location(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Location(builtin);
}
