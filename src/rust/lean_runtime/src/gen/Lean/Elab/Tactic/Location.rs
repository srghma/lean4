// Lean compiler output
// Module: Lean.Elab.Tactic.Location
// Imports: Lean.Elab.Tactic.ElabTerm
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
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 84, 121, 112, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__3_value) as *mut crate::leanh::LeanObject,5573707264546329628 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_expandLocation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_expandLocation___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1262264483427375750 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_expandLocation___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_expandLocation___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_expandLocation___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_expandLocation___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx(
    mut v_x_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1144_) == 0 {
        let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1145_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1145_;
    } else {
        let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1146_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1146_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorIdx___boxed(
    mut v_x_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Elab_Tactic_Location_ctorIdx(v_x_1147_);
    crate::leanh::lean_dec(v_x_1147_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___redArg(
    mut v_t_1149_: *mut crate::leanh::LeanObject,
    mut v_k_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1149_) == 0 {
        return v_k_1150_;
    } else {
        let mut v_hypotheses_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_1152_: u8 = 0;
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_hypotheses_1151_ = crate::leanh::lean_ctor_get(v_t_1149_, 0);
        crate::leanh::lean_inc_ref(v_hypotheses_1151_);
        v_type_1152_ = crate::leanh::lean_ctor_get_uint8(
            v_t_1149_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_t_1149_, 1);
        v___x_1153_ = crate::leanh::lean_box((v_type_1152_) as usize);
        v___x_1154_ = crate::leanh::lean_apply_2(v_k_1150_, v_hypotheses_1151_, v___x_1153_);
        return v___x_1154_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim(
    mut v_motive_1155_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1156_: *mut crate::leanh::LeanObject,
    mut v_t_1157_: *mut crate::leanh::LeanObject,
    mut v_h_1158_: *mut crate::leanh::LeanObject,
    mut v_k_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1157_, v_k_1159_);
    return v___x_1160_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_ctorElim___boxed(
    mut v_motive_1161_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1162_: *mut crate::leanh::LeanObject,
    mut v_t_1163_: *mut crate::leanh::LeanObject,
    mut v_h_1164_: *mut crate::leanh::LeanObject,
    mut v_k_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_Elab_Tactic_Location_ctorElim(
        v_motive_1161_,
        v_ctorIdx_1162_,
        v_t_1163_,
        v_h_1164_,
        v_k_1165_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1162_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim___redArg(
    mut v_t_1167_: *mut crate::leanh::LeanObject,
    mut v_wildcard_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1167_, v_wildcard_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_wildcard_elim(
    mut v_motive_1170_: *mut crate::leanh::LeanObject,
    mut v_t_1171_: *mut crate::leanh::LeanObject,
    mut v_h_1172_: *mut crate::leanh::LeanObject,
    mut v_wildcard_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1171_, v_wildcard_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim___redArg(
    mut v_t_1175_: *mut crate::leanh::LeanObject,
    mut v_targets_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1175_, v_targets_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_Location_targets_elim(
    mut v_motive_1178_: *mut crate::leanh::LeanObject,
    mut v_t_1179_: *mut crate::leanh::LeanObject,
    mut v_h_1180_: *mut crate::leanh::LeanObject,
    mut v_targets_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Tactic_Location_ctorElim___redArg(v_t_1179_, v_targets_1181_);
    return v___x_1182_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(
    mut v_as_1192_: *mut crate::leanh::LeanObject,
    mut v_i_1193_: usize,
    mut v_stop_1194_: usize,
    mut v_b_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1201_ = lean_usize_dec_eq(v_i_1193_, v_stop_1194_);
                if v___x_1201_ == 0 {
                    v___x_1202_ = lean_array_uget_borrowed(v_as_1192_, v_i_1193_);
                    crate::leanh::lean_inc(v___x_1202_);
                    v___x_1203_ = l_Lean_Syntax_getKind(v___x_1202_);
                    v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0___closed__4;
                    v___x_1205_ = lean_name_eq(v___x_1203_, v___x_1204_);
                    crate::leanh::lean_dec(v___x_1203_);
                    if v___x_1205_ == 0 {
                        crate::leanh::lean_inc(v___x_1202_);
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
    mut v_as_1207_: *mut crate::leanh::LeanObject,
    mut v_i_1208_: *mut crate::leanh::LeanObject,
    mut v_stop_1209_: *mut crate::leanh::LeanObject,
    mut v_b_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1211_: usize = 0;
    let mut v_stop_boxed_1212_: usize = 0;
    let mut v_res_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1211_ = crate::leanh::lean_unbox_usize(v_i_1208_);
    crate::leanh::lean_dec(v_i_1208_);
    v_stop_boxed_1212_ = crate::leanh::lean_unbox_usize(v_stop_1209_);
    crate::leanh::lean_dec(v_stop_1209_);
    v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_as_1207_, v_i_boxed_1211_, v_stop_boxed_1212_, v_b_1210_);
    crate::leanh::lean_dec_ref(v_as_1207_);
    return v_res_1213_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation(
    mut v_stx_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_locationHyps_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numTurnstiles_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___x_1240_: u8 = 0;
    let mut v___x_1241_: usize = 0;
    let mut v___x_1242_: usize = 0;
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1223_ = crate::leanh::lean_unsigned_to_nat(1);
                v_arg_1224_ = l_Lean_Syntax_getArg(v_stx_1222_, v___x_1223_);
                crate::leanh::lean_inc(v_arg_1224_);
                v___x_1225_ = l_Lean_Syntax_getKind(v_arg_1224_);
                v___x_1226_ = l_Lean_Elab_Tactic_expandLocation___closed__1;
                v___x_1227_ = lean_name_eq(v___x_1225_, v___x_1226_);
                crate::leanh::lean_dec(v___x_1225_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1229_ = l_Lean_Syntax_getArg(v_arg_1224_, v___x_1228_);
                    crate::leanh::lean_dec(v_arg_1224_);
                    v_locationHyps_1230_ = l_Lean_Syntax_getArgs(v___x_1229_);
                    crate::leanh::lean_dec(v___x_1229_);
                    v___x_1231_ = lean_array_get_size(v_locationHyps_1230_);
                    v___x_1238_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
                    v___x_1239_ = lean_nat_dec_lt(v___x_1228_, v___x_1231_);
                    if v___x_1239_ == 0 {
                        crate::leanh::lean_dec_ref(v_locationHyps_1230_);
                        v___y_1233_ = v___x_1238_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1240_ = lean_nat_dec_le(v___x_1231_, v___x_1231_);
                        if v___x_1240_ == 0 {
                            if v___x_1239_ == 0 {
                                crate::leanh::lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1238_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1241_ = 0usize;
                                v___x_1242_ = lean_usize_of_nat(v___x_1231_);
                                v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1241_, v___x_1242_, v___x_1238_);
                                crate::leanh::lean_dec_ref(v_locationHyps_1230_);
                                v___y_1233_ = v___x_1243_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1244_ = 0usize;
                            v___x_1245_ = lean_usize_of_nat(v___x_1231_);
                            v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_expandLocation_spec__0(v_locationHyps_1230_, v___x_1244_, v___x_1245_, v___x_1238_);
                            crate::leanh::lean_dec_ref(v_locationHyps_1230_);
                            v___y_1233_ = v___x_1246_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_arg_1224_);
                    v___x_1247_ = crate::leanh::lean_box(0);
                    return v___x_1247_;
                }
            }
            1 => {
                v___x_1234_ = lean_array_get_size(v___y_1233_);
                v_numTurnstiles_1235_ = lean_nat_sub(v___x_1231_, v___x_1234_);
                v___x_1236_ = lean_nat_dec_lt(v___x_1228_, v_numTurnstiles_1235_);
                crate::leanh::lean_dec(v_numTurnstiles_1235_);
                v___x_1237_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1237_, 0, v___y_1233_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1237_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1236_,
                );
                return v___x_1237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandLocation___boxed(
    mut v_stx_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_Elab_Tactic_expandLocation(v_stx_1248_);
    crate::leanh::lean_dec(v_stx_1248_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation(
    mut v_stx_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: u8 = 0;
    v___x_1251_ = l_Lean_Syntax_isNone(v_stx_1250_);
    if v___x_1251_ == 0 {
        let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1252_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1253_ = l_Lean_Syntax_getArg(v_stx_1250_, v___x_1252_);
        v___x_1254_ = l_Lean_Elab_Tactic_expandLocation(v___x_1253_);
        crate::leanh::lean_dec(v___x_1253_);
        return v___x_1254_;
    } else {
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1255_ = l_Lean_Elab_Tactic_expandLocation___closed__2;
        v___x_1256_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1255_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1256_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1251_,
        );
        return v___x_1256_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_expandOptLocation___boxed(
    mut v_stx_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_Elab_Tactic_expandOptLocation(v_stx_1257_);
    crate::leanh::lean_dec(v_stx_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0(
    mut v_x_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1263_);
    crate::leanh::lean_inc_ref(v___y_1262_);
    crate::leanh::lean_inc(v___y_1261_);
    crate::leanh::lean_inc_ref(v___y_1260_);
    v___x_1269_ = crate::leanh::lean_apply_9(
        v_x_1259_,
        v___y_1260_,
        v___y_1261_,
        v___y_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        crate::leanh::lean_box(0),
    );
    return v___x_1269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed(
    mut v_x_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1274_);
    crate::leanh::lean_dec_ref(v___y_1273_);
    crate::leanh::lean_dec(v___y_1272_);
    crate::leanh::lean_dec_ref(v___y_1271_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(
    mut v_mvarId_1281_: *mut crate::leanh::LeanObject,
    mut v_x_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
    mut v___y_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1286_);
                crate::leanh::lean_inc_ref(v___y_1285_);
                crate::leanh::lean_inc(v___y_1284_);
                crate::leanh::lean_inc_ref(v___y_1283_);
                v___f_1292_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1292_, 0, v_x_1282_);
                crate::leanh::lean_closure_set(v___f_1292_, 1, v___y_1283_);
                crate::leanh::lean_closure_set(v___f_1292_, 2, v___y_1284_);
                crate::leanh::lean_closure_set(v___f_1292_, 3, v___y_1285_);
                crate::leanh::lean_closure_set(v___f_1292_, 4, v___y_1286_);
                v___x_1293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1281_,
                    v___f_1292_,
                    v___y_1287_,
                    v___y_1288_,
                    v___y_1289_,
                    v___y_1290_,
                );
                if crate::leanh::lean_obj_tag(v___x_1293_) == 0 {
                    return v___x_1293_;
                } else {
                    v_a_1294_ = crate::leanh::lean_ctor_get(v___x_1293_, 0);
                    v_isSharedCheck_1301_ = (!crate::leanh::lean_is_exclusive(v___x_1293_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1296_ = v___x_1293_;
                        v_isShared_1297_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1294_);
                        crate::leanh::lean_dec(v___x_1293_);
                        v___x_1296_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
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
    mut v_mvarId_1302_: *mut crate::leanh::LeanObject,
    mut v_x_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1311_);
    crate::leanh::lean_dec_ref(v___y_1310_);
    crate::leanh::lean_dec(v___y_1309_);
    crate::leanh::lean_dec_ref(v___y_1308_);
    crate::leanh::lean_dec(v___y_1307_);
    crate::leanh::lean_dec_ref(v___y_1306_);
    crate::leanh::lean_dec(v___y_1305_);
    crate::leanh::lean_dec_ref(v___y_1304_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2(
    mut v_00_u03b1_1314_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1315_: *mut crate::leanh::LeanObject,
    mut v_x_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1327_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1328_: *mut crate::leanh::LeanObject,
    mut v_x_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1337_);
    crate::leanh::lean_dec_ref(v___y_1336_);
    crate::leanh::lean_dec(v___y_1335_);
    crate::leanh::lean_dec_ref(v___y_1334_);
    crate::leanh::lean_dec(v___y_1333_);
    crate::leanh::lean_dec_ref(v___y_1332_);
    crate::leanh::lean_dec(v___y_1331_);
    crate::leanh::lean_dec_ref(v___y_1330_);
    return v_res_1339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(
    mut v___x_1340_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1341_: *mut crate::leanh::LeanObject,
    mut v_sz_1342_: usize,
    mut v_i_1343_: usize,
    mut v_bs_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: usize = 0;
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
                if v___x_1354_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_1341_);
                    v___x_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1355_, 0, v_bs_1344_);
                    return v___x_1355_;
                } else {
                    v_assignment_1356_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_1341_);
                    crate::leanh::lean_inc(v___y_1352_);
                    crate::leanh::lean_inc_ref(v___y_1351_);
                    crate::leanh::lean_inc(v___y_1350_);
                    crate::leanh::lean_inc_ref(v___y_1349_);
                    crate::leanh::lean_inc(v___y_1348_);
                    crate::leanh::lean_inc_ref(v___y_1347_);
                    crate::leanh::lean_inc(v___y_1346_);
                    crate::leanh::lean_inc_ref(v___y_1345_);
                    v___x_1357_ = crate::leanh::lean_apply_9(
                        v_ctx_x3f_1341_,
                        v___y_1345_,
                        v___y_1346_,
                        v___y_1347_,
                        v___y_1348_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                        v___y_1352_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1357_) == 0 {
                        v_a_1358_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                        crate::leanh::lean_inc(v_a_1358_);
                        crate::leanh::lean_dec_ref_known(v___x_1357_, 1);
                        v_v_1359_ = lean_array_uget(v_bs_1344_, v_i_1343_);
                        v___x_1360_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1361_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1360_);
                        v_tree_1368_ =
                            l_Lean_Elab_InfoTree_substitute(v_v_1359_, v_assignment_1356_);
                        if crate::leanh::lean_obj_tag(v_a_1358_) == 0 {
                            v_a_1363_ = v_tree_1368_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1369_ = crate::leanh::lean_ctor_get(v_a_1358_, 0);
                            crate::leanh::lean_inc(v_val_1369_);
                            crate::leanh::lean_dec_ref_known(v_a_1358_, 1);
                            v___x_1370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1370_, 0, v_val_1369_);
                            crate::leanh::lean_ctor_set(v___x_1370_, 1, v_tree_1368_);
                            v_a_1363_ = v___x_1370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1344_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_1341_);
                        v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1357_, 0);
                        v_isSharedCheck_1378_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1357_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1357_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1371_);
                            crate::leanh::lean_dec(v___x_1357_);
                            v___x_1373_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
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
    mut v___x_1379_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1380_: *mut crate::leanh::LeanObject,
    mut v_sz_1381_: *mut crate::leanh::LeanObject,
    mut v_i_1382_: *mut crate::leanh::LeanObject,
    mut v_bs_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
    mut v___y_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1393_: usize = 0;
    let mut v_i_boxed_1394_: usize = 0;
    let mut v_res_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1393_ = crate::leanh::lean_unbox_usize(v_sz_1381_);
    crate::leanh::lean_dec(v_sz_1381_);
    v_i_boxed_1394_ = crate::leanh::lean_unbox_usize(v_i_1382_);
    crate::leanh::lean_dec(v_i_1382_);
    v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1379_, v_ctx_x3f_1380_, v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
    crate::leanh::lean_dec(v___y_1391_);
    crate::leanh::lean_dec_ref(v___y_1390_);
    crate::leanh::lean_dec(v___y_1389_);
    crate::leanh::lean_dec_ref(v___y_1388_);
    crate::leanh::lean_dec(v___y_1387_);
    crate::leanh::lean_dec_ref(v___y_1386_);
    crate::leanh::lean_dec(v___y_1385_);
    crate::leanh::lean_dec_ref(v___y_1384_);
    crate::leanh::lean_dec_ref(v___x_1379_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(
    mut v___x_1396_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1397_: *mut crate::leanh::LeanObject,
    mut v_x_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
    mut v___y_1403_: *mut crate::leanh::LeanObject,
    mut v___y_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v_sz_1412_: usize = 0;
    let mut v___x_1413_: usize = 0;
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1425_: u8 = 0;
    let mut v_a_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut v_vs_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v_sz_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1445_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1452_: u8 = 0;
    let mut v_a_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1460_: u8 = 0;
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1398_) == 0 {
                    v_cs_1408_ = crate::leanh::lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1434_ = (!crate::leanh::lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1410_ = v_x_1398_;
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_1408_);
                        crate::leanh::lean_dec(v_x_1398_);
                        v___x_1410_ = crate::leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1435_ = crate::leanh::lean_ctor_get(v_x_1398_, 0);
                    v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v_x_1398_)) as u8;
                    if v_isSharedCheck_1461_ == 0 {
                        v___x_1437_ = v_x_1398_;
                        v_isShared_1438_ = v_isSharedCheck_1461_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1435_);
                        crate::leanh::lean_dec(v_x_1398_);
                        v___x_1437_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_1414_) == 0 {
                    v_a_1415_ = crate::leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1425_ = (!crate::leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1425_ == 0 {
                        v___x_1417_ = v___x_1414_;
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1415_);
                        crate::leanh::lean_dec(v___x_1414_);
                        v___x_1417_ = crate::leanh::lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1425_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1410_);
                    v_a_1426_ = crate::leanh::lean_ctor_get(v___x_1414_, 0);
                    v_isSharedCheck_1433_ = (!crate::leanh::lean_is_exclusive(v___x_1414_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1428_ = v___x_1414_;
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1426_);
                        crate::leanh::lean_dec(v___x_1414_);
                        v___x_1428_ = crate::leanh::lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1410_, 0, v_a_1415_);
                    v___x_1420_ = v___x_1410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1417_, 0, v___x_1420_);
                    v___x_1422_ = v___x_1417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
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
                    v_reuseFailAlloc_1432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
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
                if crate::leanh::lean_obj_tag(v___x_1441_) == 0 {
                    v_a_1442_ = crate::leanh::lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1452_ = (!crate::leanh::lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1452_ == 0 {
                        v___x_1444_ = v___x_1441_;
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1442_);
                        crate::leanh::lean_dec(v___x_1441_);
                        v___x_1444_ = crate::leanh::lean_box(0);
                        v_isShared_1445_ = v_isSharedCheck_1452_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1437_);
                    v_a_1453_ = crate::leanh::lean_ctor_get(v___x_1441_, 0);
                    v_isSharedCheck_1460_ = (!crate::leanh::lean_is_exclusive(v___x_1441_)) as u8;
                    if v_isSharedCheck_1460_ == 0 {
                        v___x_1455_ = v___x_1441_;
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1453_);
                        crate::leanh::lean_dec(v___x_1441_);
                        v___x_1455_ = crate::leanh::lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1460_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1437_, 0, v_a_1442_);
                    v___x_1447_ = v___x_1437_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1442_);
                    v___x_1447_ = v_reuseFailAlloc_1451_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1445_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1447_);
                    v___x_1449_ = v___x_1444_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
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
                    v_reuseFailAlloc_1459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
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
    mut v___x_1462_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1463_: *mut crate::leanh::LeanObject,
    mut v_sz_1464_: usize,
    mut v_i_1465_: usize,
    mut v_bs_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: usize = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1476_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
                if v___x_1476_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_1463_);
                    v___x_1477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v_bs_1466_);
                    return v___x_1477_;
                } else {
                    v_v_1478_ = lean_array_uget_borrowed(v_bs_1466_, v_i_1465_);
                    crate::leanh::lean_inc(v_v_1478_);
                    crate::leanh::lean_inc_ref(v_ctx_x3f_1463_);
                    v___x_1479_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1462_, v_ctx_x3f_1463_, v_v_1478_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
                    if crate::leanh::lean_obj_tag(v___x_1479_) == 0 {
                        v_a_1480_ = crate::leanh::lean_ctor_get(v___x_1479_, 0);
                        crate::leanh::lean_inc(v_a_1480_);
                        crate::leanh::lean_dec_ref_known(v___x_1479_, 1);
                        v___x_1481_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1482_ = lean_array_uset(v_bs_1466_, v_i_1465_, v___x_1481_);
                        v___x_1483_ = 1usize;
                        v___x_1484_ = lean_usize_add(v_i_1465_, v___x_1483_);
                        v___x_1485_ = lean_array_uset(v_bs_x27_1482_, v_i_1465_, v_a_1480_);
                        v_i_1465_ = v___x_1484_;
                        v_bs_1466_ = v___x_1485_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1466_);
                        crate::leanh::lean_dec_ref(v_ctx_x3f_1463_);
                        v_a_1487_ = crate::leanh::lean_ctor_get(v___x_1479_, 0);
                        v_isSharedCheck_1494_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1479_)) as u8;
                        if v_isSharedCheck_1494_ == 0 {
                            v___x_1489_ = v___x_1479_;
                            v_isShared_1490_ = v_isSharedCheck_1494_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1487_);
                            crate::leanh::lean_dec(v___x_1479_);
                            v___x_1489_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
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
    mut v___x_1495_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1496_: *mut crate::leanh::LeanObject,
    mut v_sz_1497_: *mut crate::leanh::LeanObject,
    mut v_i_1498_: *mut crate::leanh::LeanObject,
    mut v_bs_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
    mut v___y_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1509_: usize = 0;
    let mut v_i_boxed_1510_: usize = 0;
    let mut v_res_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1509_ = crate::leanh::lean_unbox_usize(v_sz_1497_);
    crate::leanh::lean_dec(v_sz_1497_);
    v_i_boxed_1510_ = crate::leanh::lean_unbox_usize(v_i_1498_);
    crate::leanh::lean_dec(v_i_1498_);
    v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8_spec__9(v___x_1495_, v_ctx_x3f_1496_, v_sz_boxed_1509_, v_i_boxed_1510_, v_bs_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
    crate::leanh::lean_dec(v___y_1507_);
    crate::leanh::lean_dec_ref(v___y_1506_);
    crate::leanh::lean_dec(v___y_1505_);
    crate::leanh::lean_dec_ref(v___y_1504_);
    crate::leanh::lean_dec(v___y_1503_);
    crate::leanh::lean_dec_ref(v___y_1502_);
    crate::leanh::lean_dec(v___y_1501_);
    crate::leanh::lean_dec_ref(v___y_1500_);
    crate::leanh::lean_dec_ref(v___x_1495_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8___boxed(
    mut v___x_1512_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1513_: *mut crate::leanh::LeanObject,
    mut v_x_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1512_, v_ctx_x3f_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    crate::leanh::lean_dec(v___y_1520_);
    crate::leanh::lean_dec_ref(v___y_1519_);
    crate::leanh::lean_dec(v___y_1518_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    crate::leanh::lean_dec(v___y_1516_);
    crate::leanh::lean_dec_ref(v___y_1515_);
    crate::leanh::lean_dec_ref(v___x_1512_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(
    mut v___x_1525_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1526_: *mut crate::leanh::LeanObject,
    mut v_t_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_1540_: usize = 0;
    let mut v_tailOff_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1547_: usize = 0;
    let mut v___x_1548_: usize = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_a_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_a_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1537_ = crate::leanh::lean_ctor_get(v_t_1527_, 0);
                v_tail_1538_ = crate::leanh::lean_ctor_get(v_t_1527_, 1);
                v_size_1539_ = crate::leanh::lean_ctor_get(v_t_1527_, 2);
                v_shift_1540_ = crate::leanh::lean_ctor_get_usize(v_t_1527_, 4);
                v_tailOff_1541_ = crate::leanh::lean_ctor_get(v_t_1527_, 3);
                v_isSharedCheck_1577_ = (!crate::leanh::lean_is_exclusive(v_t_1527_)) as u8;
                if v_isSharedCheck_1577_ == 0 {
                    v___x_1543_ = v_t_1527_;
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_1541_);
                    crate::leanh::lean_inc(v_size_1539_);
                    crate::leanh::lean_inc(v_tail_1538_);
                    crate::leanh::lean_inc(v_root_1537_);
                    crate::leanh::lean_dec(v_t_1527_);
                    v___x_1543_ = crate::leanh::lean_box(0);
                    v_isShared_1544_ = v_isSharedCheck_1577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_ctx_x3f_1526_);
                v___x_1545_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__8(v___x_1525_, v_ctx_x3f_1526_, v_root_1537_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                if crate::leanh::lean_obj_tag(v___x_1545_) == 0 {
                    v_a_1546_ = crate::leanh::lean_ctor_get(v___x_1545_, 0);
                    crate::leanh::lean_inc(v_a_1546_);
                    crate::leanh::lean_dec_ref_known(v___x_1545_, 1);
                    v_sz_1547_ = lean_array_size(v_tail_1538_);
                    v___x_1548_ = 0usize;
                    v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5_spec__9(v___x_1525_, v_ctx_x3f_1526_, v_sz_1547_, v___x_1548_, v_tail_1538_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
                    if crate::leanh::lean_obj_tag(v___x_1549_) == 0 {
                        v_a_1550_ = crate::leanh::lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1560_ == 0 {
                            v___x_1552_ = v___x_1549_;
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1550_);
                            crate::leanh::lean_dec(v___x_1549_);
                            v___x_1552_ = crate::leanh::lean_box(0);
                            v_isShared_1553_ = v_isSharedCheck_1560_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1546_);
                        crate::leanh::lean_del_object(v___x_1543_);
                        crate::leanh::lean_dec(v_tailOff_1541_);
                        crate::leanh::lean_dec(v_size_1539_);
                        v_a_1561_ = crate::leanh::lean_ctor_get(v___x_1549_, 0);
                        v_isSharedCheck_1568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1549_)) as u8;
                        if v_isSharedCheck_1568_ == 0 {
                            v___x_1563_ = v___x_1549_;
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1561_);
                            crate::leanh::lean_dec(v___x_1549_);
                            v___x_1563_ = crate::leanh::lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1543_);
                    crate::leanh::lean_dec(v_tailOff_1541_);
                    crate::leanh::lean_dec(v_size_1539_);
                    crate::leanh::lean_dec_ref(v_tail_1538_);
                    crate::leanh::lean_dec_ref(v_ctx_x3f_1526_);
                    v_a_1569_ = crate::leanh::lean_ctor_get(v___x_1545_, 0);
                    v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v___x_1545_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1571_ = v___x_1545_;
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1569_);
                        crate::leanh::lean_dec(v___x_1545_);
                        v___x_1571_ = crate::leanh::lean_box(0);
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1543_, 1, v_a_1550_);
                    crate::leanh::lean_ctor_set(v___x_1543_, 0, v_a_1546_);
                    v___x_1555_ = v___x_1543_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_size_1539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_tailOff_1541_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_1559_, 4, v_shift_1540_);
                    v___x_1555_ = v_reuseFailAlloc_1559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1552_, 0, v___x_1555_);
                    v___x_1557_ = v___x_1552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
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
                    v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
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
                    v_reuseFailAlloc_1575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
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
    mut v___x_1578_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1579_: *mut crate::leanh::LeanObject,
    mut v_t_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v___x_1578_, v_ctx_x3f_1579_, v_t_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
    crate::leanh::lean_dec(v___y_1588_);
    crate::leanh::lean_dec_ref(v___y_1587_);
    crate::leanh::lean_dec(v___y_1586_);
    crate::leanh::lean_dec_ref(v___y_1585_);
    crate::leanh::lean_dec(v___y_1584_);
    crate::leanh::lean_dec_ref(v___y_1583_);
    crate::leanh::lean_dec(v___y_1582_);
    crate::leanh::lean_dec_ref(v___y_1581_);
    crate::leanh::lean_dec_ref(v___x_1578_);
    return v_res_1590_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v_enabled_1624_: u8 = 0;
    let mut v_assignment_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1644_: u8 = 0;
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v_a_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1603_ = lean_st_ref_get(v___y_1591_);
                v_infoState_1604_ = crate::leanh::lean_ctor_get(v___x_1603_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1604_);
                crate::leanh::lean_dec(v___x_1603_);
                v_trees_1605_ = crate::leanh::lean_ctor_get(v_infoState_1604_, 2);
                crate::leanh::lean_inc_ref(v_trees_1605_);
                v___x_1606_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__5(v_infoState_1604_, v_ctx_x3f_1592_, v_trees_1605_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1591_);
                crate::leanh::lean_dec_ref(v_infoState_1604_);
                if crate::leanh::lean_obj_tag(v___x_1606_) == 0 {
                    v_a_1607_ = crate::leanh::lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1645_ = (!crate::leanh::lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1609_ = v___x_1606_;
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1607_);
                        crate::leanh::lean_dec(v___x_1606_);
                        v___x_1609_ = crate::leanh::lean_box(0);
                        v_isShared_1610_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1600_);
                    v_a_1646_ = crate::leanh::lean_ctor_get(v___x_1606_, 0);
                    v_isSharedCheck_1653_ = (!crate::leanh::lean_is_exclusive(v___x_1606_)) as u8;
                    if v_isSharedCheck_1653_ == 0 {
                        v___x_1648_ = v___x_1606_;
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1646_);
                        crate::leanh::lean_dec(v___x_1606_);
                        v___x_1648_ = crate::leanh::lean_box(0);
                        v_isShared_1649_ = v_isSharedCheck_1653_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1611_ = lean_st_ref_take(v___y_1591_);
                v_infoState_1612_ = crate::leanh::lean_ctor_get(v___x_1611_, 7);
                v_env_1613_ = crate::leanh::lean_ctor_get(v___x_1611_, 0);
                v_nextMacroScope_1614_ = crate::leanh::lean_ctor_get(v___x_1611_, 1);
                v_ngen_1615_ = crate::leanh::lean_ctor_get(v___x_1611_, 2);
                v_auxDeclNGen_1616_ = crate::leanh::lean_ctor_get(v___x_1611_, 3);
                v_traceState_1617_ = crate::leanh::lean_ctor_get(v___x_1611_, 4);
                v_cache_1618_ = crate::leanh::lean_ctor_get(v___x_1611_, 5);
                v_messages_1619_ = crate::leanh::lean_ctor_get(v___x_1611_, 6);
                v_snapshotTasks_1620_ = crate::leanh::lean_ctor_get(v___x_1611_, 8);
                v_isSharedCheck_1644_ = (!crate::leanh::lean_is_exclusive(v___x_1611_)) as u8;
                if v_isSharedCheck_1644_ == 0 {
                    v___x_1622_ = v___x_1611_;
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1620_);
                    crate::leanh::lean_inc(v_infoState_1612_);
                    crate::leanh::lean_inc(v_messages_1619_);
                    crate::leanh::lean_inc(v_cache_1618_);
                    crate::leanh::lean_inc(v_traceState_1617_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1616_);
                    crate::leanh::lean_inc(v_ngen_1615_);
                    crate::leanh::lean_inc(v_nextMacroScope_1614_);
                    crate::leanh::lean_inc(v_env_1613_);
                    crate::leanh::lean_dec(v___x_1611_);
                    v___x_1622_ = crate::leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_1624_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1625_ = crate::leanh::lean_ctor_get(v_infoState_1612_, 0);
                v_lazyAssignment_1626_ = crate::leanh::lean_ctor_get(v_infoState_1612_, 1);
                v_isSharedCheck_1642_ = (!crate::leanh::lean_is_exclusive(v_infoState_1612_)) as u8;
                if v_isSharedCheck_1642_ == 0 {
                    v_unused_1643_ = crate::leanh::lean_ctor_get(v_infoState_1612_, 2);
                    crate::leanh::lean_dec(v_unused_1643_);
                    v___x_1628_ = v_infoState_1612_;
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1626_);
                    crate::leanh::lean_inc(v_assignment_1625_);
                    crate::leanh::lean_dec(v_infoState_1612_);
                    v___x_1628_ = crate::leanh::lean_box(0);
                    v_isShared_1629_ = v_isSharedCheck_1642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1630_ = l_Lean_PersistentArray_append___redArg(v_a_1600_, v_a_1607_);
                crate::leanh::lean_dec(v_a_1607_);
                if v_isShared_1629_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1628_, 2, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_assignment_1625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_lazyAssignment_1626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1630_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1641_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1624_,
                    );
                    v___x_1632_ = v_reuseFailAlloc_1641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1623_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1622_, 7, v___x_1632_);
                    v___x_1634_ = v___x_1622_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_env_1613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_nextMacroScope_1614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_ngen_1615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_auxDeclNGen_1616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_traceState_1617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 5, v_cache_1618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 6, v_messages_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 7, v___x_1632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 8, v_snapshotTasks_1620_);
                    v___x_1634_ = v_reuseFailAlloc_1640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1635_ = lean_st_ref_set(v___y_1591_, v___x_1634_);
                v___x_1636_ = crate::leanh::lean_box(0);
                if v_isShared_1610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1636_);
                    v___x_1638_ = v___x_1609_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
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
                    v_reuseFailAlloc_1652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
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
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1654_, v_ctx_x3f_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v_a_1663_, v_a_x3f_1664_);
    crate::leanh::lean_dec(v_a_x3f_1664_);
    crate::leanh::lean_dec_ref(v___y_1662_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    crate::leanh::lean_dec(v___y_1659_);
    crate::leanh::lean_dec_ref(v___y_1658_);
    crate::leanh::lean_dec(v___y_1657_);
    crate::leanh::lean_dec_ref(v___y_1656_);
    crate::leanh::lean_dec(v___y_1654_);
    return v_res_1666_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
    v___x_1669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: usize = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = 5usize;
    v___x_1671_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1672_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1673_ = lean_mk_empty_array_with_capacity(v___x_1672_);
    v___x_1674_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_1675_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    crate::leanh::lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    crate::leanh::lean_ctor_set(v___x_1675_, 2, v___x_1671_);
    crate::leanh::lean_ctor_set(v___x_1675_, 3, v___x_1671_);
    crate::leanh::lean_ctor_set_usize(v___x_1675_, 4, v___x_1670_);
    return v___x_1675_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v_enabled_1694_: u8 = 0;
    let mut v_assignment_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_unused_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1678_ = lean_st_ref_get(v___y_1676_);
                v_infoState_1679_ = crate::leanh::lean_ctor_get(v___x_1678_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1679_);
                crate::leanh::lean_dec(v___x_1678_);
                v_trees_1680_ = crate::leanh::lean_ctor_get(v_infoState_1679_, 2);
                crate::leanh::lean_inc_ref(v_trees_1680_);
                crate::leanh::lean_dec_ref(v_infoState_1679_);
                v___x_1681_ = lean_st_ref_take(v___y_1676_);
                v_infoState_1682_ = crate::leanh::lean_ctor_get(v___x_1681_, 7);
                v_env_1683_ = crate::leanh::lean_ctor_get(v___x_1681_, 0);
                v_nextMacroScope_1684_ = crate::leanh::lean_ctor_get(v___x_1681_, 1);
                v_ngen_1685_ = crate::leanh::lean_ctor_get(v___x_1681_, 2);
                v_auxDeclNGen_1686_ = crate::leanh::lean_ctor_get(v___x_1681_, 3);
                v_traceState_1687_ = crate::leanh::lean_ctor_get(v___x_1681_, 4);
                v_cache_1688_ = crate::leanh::lean_ctor_get(v___x_1681_, 5);
                v_messages_1689_ = crate::leanh::lean_ctor_get(v___x_1681_, 6);
                v_snapshotTasks_1690_ = crate::leanh::lean_ctor_get(v___x_1681_, 8);
                v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v___x_1681_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v___x_1692_ = v___x_1681_;
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1690_);
                    crate::leanh::lean_inc(v_infoState_1682_);
                    crate::leanh::lean_inc(v_messages_1689_);
                    crate::leanh::lean_inc(v_cache_1688_);
                    crate::leanh::lean_inc(v_traceState_1687_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1686_);
                    crate::leanh::lean_inc(v_ngen_1685_);
                    crate::leanh::lean_inc(v_nextMacroScope_1684_);
                    crate::leanh::lean_inc(v_env_1683_);
                    crate::leanh::lean_dec(v___x_1681_);
                    v___x_1692_ = crate::leanh::lean_box(0);
                    v_isShared_1693_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_1694_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1682_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_1695_ = crate::leanh::lean_ctor_get(v_infoState_1682_, 0);
                v_lazyAssignment_1696_ = crate::leanh::lean_ctor_get(v_infoState_1682_, 1);
                v_isSharedCheck_1709_ = (!crate::leanh::lean_is_exclusive(v_infoState_1682_)) as u8;
                if v_isSharedCheck_1709_ == 0 {
                    v_unused_1710_ = crate::leanh::lean_ctor_get(v_infoState_1682_, 2);
                    crate::leanh::lean_dec(v_unused_1710_);
                    v___x_1698_ = v_infoState_1682_;
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_1696_);
                    crate::leanh::lean_inc(v_assignment_1695_);
                    crate::leanh::lean_dec(v_infoState_1682_);
                    v___x_1698_ = crate::leanh::lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___closed__1);
                if v_isShared_1699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1698_, 2, v___x_1700_);
                    v___x_1702_ = v___x_1698_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1708_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_assignment_1695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_lazyAssignment_1696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 2, v___x_1700_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1708_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_1694_,
                    );
                    v___x_1702_ = v_reuseFailAlloc_1708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1692_, 7, v___x_1702_);
                    v___x_1704_ = v___x_1692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_env_1683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nextMacroScope_1684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_ngen_1685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_auxDeclNGen_1686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_traceState_1687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_cache_1688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_messages_1689_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 7, v___x_1702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_snapshotTasks_1690_);
                    v___x_1704_ = v_reuseFailAlloc_1707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1705_ = lean_st_ref_set(v___y_1676_, v___x_1704_);
                v___x_1706_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1706_, 0, v_trees_1680_);
                return v___x_1706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg___boxed(
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1712_);
    crate::leanh::lean_dec(v___y_1712_);
    return v_res_1714_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(
    mut v_x_1715_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_1728_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_unused_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_reuseFailAlloc_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_a_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_unused_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1726_ = lean_st_ref_get(v___y_1724_);
                v_infoState_1727_ = crate::leanh::lean_ctor_get(v___x_1726_, 7);
                crate::leanh::lean_inc_ref(v_infoState_1727_);
                crate::leanh::lean_dec(v___x_1726_);
                v_enabled_1728_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_1727_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_1727_);
                if v_enabled_1728_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_x3f_1716_);
                    crate::leanh::lean_inc(v___y_1724_);
                    crate::leanh::lean_inc_ref(v___y_1723_);
                    crate::leanh::lean_inc(v___y_1722_);
                    crate::leanh::lean_inc_ref(v___y_1721_);
                    crate::leanh::lean_inc(v___y_1720_);
                    crate::leanh::lean_inc_ref(v___y_1719_);
                    crate::leanh::lean_inc(v___y_1718_);
                    crate::leanh::lean_inc_ref(v___y_1717_);
                    v___x_1729_ = crate::leanh::lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1729_;
                } else {
                    v___x_1730_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_1724_);
                    v_a_1731_ = crate::leanh::lean_ctor_get(v___x_1730_, 0);
                    crate::leanh::lean_inc(v_a_1731_);
                    crate::leanh::lean_dec_ref(v___x_1730_);
                    crate::leanh::lean_inc(v___y_1724_);
                    crate::leanh::lean_inc_ref(v___y_1723_);
                    crate::leanh::lean_inc(v___y_1722_);
                    crate::leanh::lean_inc_ref(v___y_1721_);
                    crate::leanh::lean_inc(v___y_1720_);
                    crate::leanh::lean_inc_ref(v___y_1719_);
                    crate::leanh::lean_inc(v___y_1718_);
                    crate::leanh::lean_inc_ref(v___y_1717_);
                    v_r_1732_ = crate::leanh::lean_apply_9(
                        v_x_1715_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                        v___y_1721_,
                        v___y_1722_,
                        v___y_1723_,
                        v___y_1724_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_1732_) == 0 {
                        v_a_1733_ = crate::leanh::lean_ctor_get(v_r_1732_, 0);
                        v_isSharedCheck_1757_ = (!crate::leanh::lean_is_exclusive(v_r_1732_)) as u8;
                        if v_isSharedCheck_1757_ == 0 {
                            v___x_1735_ = v_r_1732_;
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1733_);
                            crate::leanh::lean_dec(v_r_1732_);
                            v___x_1735_ = crate::leanh::lean_box(0);
                            v_isShared_1736_ = v_isSharedCheck_1757_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1758_ = crate::leanh::lean_ctor_get(v_r_1732_, 0);
                        crate::leanh::lean_inc(v_a_1758_);
                        crate::leanh::lean_dec_ref_known(v_r_1732_, 1);
                        v___x_1759_ = crate::leanh::lean_box(0);
                        v___x_1760_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1759_);
                        if crate::leanh::lean_obj_tag(v___x_1760_) == 0 {
                            v_isSharedCheck_1767_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v_unused_1768_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                                crate::leanh::lean_dec(v_unused_1768_);
                                v___x_1762_ = v___x_1760_;
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1760_);
                                v___x_1762_ = crate::leanh::lean_box(0);
                                v_isShared_1763_ = v_isSharedCheck_1767_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1758_);
                            v_a_1769_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                            v_isSharedCheck_1776_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                            if v_isSharedCheck_1776_ == 0 {
                                v___x_1771_ = v___x_1760_;
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1769_);
                                crate::leanh::lean_dec(v___x_1760_);
                                v___x_1771_ = crate::leanh::lean_box(0);
                                v_isShared_1772_ = v_isSharedCheck_1776_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1733_);
                if v_isShared_1736_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1735_, 1);
                    v___x_1738_ = v___x_1735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1739_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg___lam__0(v___y_1724_, v_ctx_x3f_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v_a_1731_, v___x_1738_);
                crate::leanh::lean_dec_ref(v___x_1738_);
                if crate::leanh::lean_obj_tag(v___x_1739_) == 0 {
                    v_isSharedCheck_1746_ = (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v_unused_1747_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                        crate::leanh::lean_dec(v_unused_1747_);
                        v___x_1741_ = v___x_1739_;
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1739_);
                        v___x_1741_ = crate::leanh::lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1733_);
                    v_a_1748_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1755_ = (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1739_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1748_);
                        crate::leanh::lean_dec(v___x_1739_);
                        v___x_1750_ = crate::leanh::lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1741_, 0, v_a_1733_);
                    v___x_1744_ = v___x_1741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1733_);
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
                    v_reuseFailAlloc_1754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1762_, 1);
                    crate::leanh::lean_ctor_set(v___x_1762_, 0, v_a_1758_);
                    v___x_1765_ = v___x_1762_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1758_);
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
                    v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
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
    mut v_x_1777_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
    mut v___y_1785_: *mut crate::leanh::LeanObject,
    mut v___y_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1788_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1777_, v_ctx_x3f_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
    crate::leanh::lean_dec(v___y_1786_);
    crate::leanh::lean_dec_ref(v___y_1785_);
    crate::leanh::lean_dec(v___y_1784_);
    crate::leanh::lean_dec_ref(v___y_1783_);
    crate::leanh::lean_dec(v___y_1782_);
    crate::leanh::lean_dec_ref(v___y_1781_);
    crate::leanh::lean_dec(v___y_1780_);
    crate::leanh::lean_dec_ref(v___y_1779_);
    return v_res_1788_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1793_ = lean_st_ref_get(v___y_1791_);
    v_env_1794_ = crate::leanh::lean_ctor_get(v___x_1793_, 0);
    crate::leanh::lean_inc_ref(v_env_1794_);
    crate::leanh::lean_dec(v___x_1793_);
    v___x_1795_ = lean_st_ref_get(v___y_1789_);
    v_mctx_1796_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1796_);
    crate::leanh::lean_dec(v___x_1795_);
    v_options_1797_ = crate::leanh::lean_ctor_get(v___y_1790_, 2);
    v_currNamespace_1798_ = crate::leanh::lean_ctor_get(v___y_1790_, 6);
    v_openDecls_1799_ = crate::leanh::lean_ctor_get(v___y_1790_, 7);
    v___x_1800_ = lean_st_ref_get(v___y_1791_);
    v_ngen_1801_ = crate::leanh::lean_ctor_get(v___x_1800_, 2);
    crate::leanh::lean_inc_ref(v_ngen_1801_);
    crate::leanh::lean_dec(v___x_1800_);
    v___x_1802_ = crate::leanh::lean_box(0);
    v___x_1803_ = l_Lean_instInhabitedFileMap_default;
    crate::leanh::lean_inc(v_openDecls_1799_);
    crate::leanh::lean_inc(v_currNamespace_1798_);
    crate::leanh::lean_inc_ref(v_options_1797_);
    v___x_1804_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1804_, 0, v_env_1794_);
    crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1802_);
    crate::leanh::lean_ctor_set(v___x_1804_, 2, v___x_1803_);
    crate::leanh::lean_ctor_set(v___x_1804_, 3, v_mctx_1796_);
    crate::leanh::lean_ctor_set(v___x_1804_, 4, v_options_1797_);
    crate::leanh::lean_ctor_set(v___x_1804_, 5, v_currNamespace_1798_);
    crate::leanh::lean_ctor_set(v___x_1804_, 6, v_openDecls_1799_);
    crate::leanh::lean_ctor_set(v___x_1804_, 7, v_ngen_1801_);
    v___x_1805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg___boxed(
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1810_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1806_, v___y_1807_, v___y_1808_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    crate::leanh::lean_dec(v___y_1806_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v_fileMap_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut v_unused_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1820_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_1816_, v___y_1817_, v___y_1818_);
                v_a_1821_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                v_isSharedCheck_1845_ = (!crate::leanh::lean_is_exclusive(v___x_1820_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1821_);
                    crate::leanh::lean_dec(v___x_1820_);
                    v___x_1823_ = crate::leanh::lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_1825_ = crate::leanh::lean_ctor_get(v___y_1817_, 1);
                v_env_1826_ = crate::leanh::lean_ctor_get(v_a_1821_, 0);
                v_mctx_1827_ = crate::leanh::lean_ctor_get(v_a_1821_, 3);
                v_options_1828_ = crate::leanh::lean_ctor_get(v_a_1821_, 4);
                v_currNamespace_1829_ = crate::leanh::lean_ctor_get(v_a_1821_, 5);
                v_openDecls_1830_ = crate::leanh::lean_ctor_get(v_a_1821_, 6);
                v_ngen_1831_ = crate::leanh::lean_ctor_get(v_a_1821_, 7);
                v_isSharedCheck_1842_ = (!crate::leanh::lean_is_exclusive(v_a_1821_)) as u8;
                if v_isSharedCheck_1842_ == 0 {
                    v_unused_1843_ = crate::leanh::lean_ctor_get(v_a_1821_, 2);
                    crate::leanh::lean_dec(v_unused_1843_);
                    v_unused_1844_ = crate::leanh::lean_ctor_get(v_a_1821_, 1);
                    crate::leanh::lean_dec(v_unused_1844_);
                    v___x_1833_ = v_a_1821_;
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_1831_);
                    crate::leanh::lean_inc(v_openDecls_1830_);
                    crate::leanh::lean_inc(v_currNamespace_1829_);
                    crate::leanh::lean_inc(v_options_1828_);
                    crate::leanh::lean_inc(v_mctx_1827_);
                    crate::leanh::lean_inc(v_env_1826_);
                    crate::leanh::lean_dec(v_a_1821_);
                    v___x_1833_ = crate::leanh::lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1835_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_fileMap_1825_);
                if v_isShared_1834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1833_, 2, v_fileMap_1825_);
                    crate::leanh::lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_env_1826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_fileMap_1825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_mctx_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_options_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_currNamespace_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_openDecls_1830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_ngen_1831_);
                    v___x_1837_ = v_reuseFailAlloc_1841_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1823_, 0, v___x_1837_);
                    v___x_1839_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
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
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    crate::leanh::lean_dec(v___y_1849_);
    crate::leanh::lean_dec_ref(v___y_1848_);
    crate::leanh::lean_dec(v___y_1847_);
    crate::leanh::lean_dec_ref(v___y_1846_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1865_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0(v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
                v_a_1866_ = crate::leanh::lean_ctor_get(v___x_1865_, 0);
                v_isSharedCheck_1875_ = (!crate::leanh::lean_is_exclusive(v___x_1865_)) as u8;
                if v_isSharedCheck_1875_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1866_);
                    crate::leanh::lean_dec(v___x_1865_);
                    v___x_1868_ = crate::leanh::lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1875_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1870_, 0, v_a_1866_);
                v___x_1871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1870_);
                if v_isShared_1869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1871_);
                    v___x_1873_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
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
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1885_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___lam__0(v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
    crate::leanh::lean_dec(v___y_1883_);
    crate::leanh::lean_dec_ref(v___y_1882_);
    crate::leanh::lean_dec(v___y_1881_);
    crate::leanh::lean_dec_ref(v___y_1880_);
    crate::leanh::lean_dec(v___y_1879_);
    crate::leanh::lean_dec_ref(v___y_1878_);
    crate::leanh::lean_dec(v___y_1877_);
    crate::leanh::lean_dec_ref(v___y_1876_);
    return v_res_1885_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg(
    mut v_x_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1897_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___closed__0;
    v___x_1898_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_1887_, v___f_1897_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___redArg___boxed(
    mut v_x_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1907_);
    crate::leanh::lean_dec_ref(v___y_1906_);
    crate::leanh::lean_dec(v___y_1905_);
    crate::leanh::lean_dec_ref(v___y_1904_);
    crate::leanh::lean_dec(v___y_1903_);
    crate::leanh::lean_dec_ref(v___y_1902_);
    crate::leanh::lean_dec(v___y_1901_);
    crate::leanh::lean_dec_ref(v___y_1900_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0(
    mut v_00_u03b1_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1922_: *mut crate::leanh::LeanObject,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_1931_);
    crate::leanh::lean_dec_ref(v___y_1930_);
    crate::leanh::lean_dec(v___y_1929_);
    crate::leanh::lean_dec_ref(v___y_1928_);
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec(v___y_1925_);
    crate::leanh::lean_dec_ref(v___y_1924_);
    return v_res_1933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(
    mut v_atLocal_1934_: *mut crate::leanh::LeanObject,
    mut v_as_1935_: *mut crate::leanh::LeanObject,
    mut v_sz_1936_: usize,
    mut v_i_1937_: usize,
    mut v_b_1938_: u8,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1953_ = lean_usize_dec_lt(v_i_1937_, v_sz_1936_);
                if v___x_1953_ == 0 {
                    crate::leanh::lean_dec_ref(v_atLocal_1934_);
                    v___x_1954_ = crate::leanh::lean_box((v_b_1938_) as usize);
                    v___x_1955_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1955_, 0, v___x_1954_);
                    return v___x_1955_;
                } else {
                    v_a_1956_ = lean_array_uget_borrowed(v_as_1935_, v_i_1937_);
                    crate::leanh::lean_inc(v_a_1956_);
                    v___x_1957_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_1956_,
                        v___y_1943_,
                        v___y_1945_,
                        v___y_1946_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1957_) == 0 {
                        v_a_1958_ = crate::leanh::lean_ctor_get(v___x_1957_, 0);
                        crate::leanh::lean_inc(v_a_1958_);
                        crate::leanh::lean_dec_ref_known(v___x_1957_, 1);
                        v___x_1959_ = l_Lean_LocalDecl_isImplementationDetail(v_a_1958_);
                        crate::leanh::lean_dec(v_a_1958_);
                        if v___x_1959_ == 0 {
                            crate::leanh::lean_inc_ref(v_atLocal_1934_);
                            crate::leanh::lean_inc(v_a_1956_);
                            v___x_1960_ = crate::leanh::lean_apply_1(v_atLocal_1934_, v_a_1956_);
                            v___x_1961_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_withMainContext___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            crate::leanh::lean_closure_set(
                                v___x_1961_,
                                0,
                                crate::leanh::lean_box(0),
                            );
                            crate::leanh::lean_closure_set(v___x_1961_, 1, v___x_1960_);
                            v___x_1962_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                            crate::leanh::lean_closure_set(
                                v___x_1962_,
                                0,
                                crate::leanh::lean_box(0),
                            );
                            crate::leanh::lean_closure_set(v___x_1962_, 1, v___x_1961_);
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
                            if crate::leanh::lean_obj_tag(v___x_1963_) == 0 {
                                if v_b_1938_ == 0 {
                                    v_a_1964_ = crate::leanh::lean_ctor_get(v___x_1963_, 0);
                                    crate::leanh::lean_inc(v_a_1964_);
                                    crate::leanh::lean_dec_ref_known(v___x_1963_, 1);
                                    v___x_1965_ = (crate::leanh::lean_unbox(v_a_1964_) as u8);
                                    crate::leanh::lean_dec(v_a_1964_);
                                    v_a_1949_ = v___x_1965_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_1963_, 1);
                                    v_a_1949_ = v_b_1938_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_atLocal_1934_);
                                return v___x_1963_;
                            }
                        } else {
                            v_a_1949_ = v_b_1938_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_atLocal_1934_);
                        v_a_1966_ = crate::leanh::lean_ctor_get(v___x_1957_, 0);
                        v_isSharedCheck_1973_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1957_)) as u8;
                        if v_isSharedCheck_1973_ == 0 {
                            v___x_1968_ = v___x_1957_;
                            v_isShared_1969_ = v_isSharedCheck_1973_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1966_);
                            crate::leanh::lean_dec(v___x_1957_);
                            v___x_1968_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
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
    mut v_atLocal_1974_: *mut crate::leanh::LeanObject,
    mut v_as_1975_: *mut crate::leanh::LeanObject,
    mut v_sz_1976_: *mut crate::leanh::LeanObject,
    mut v_i_1977_: *mut crate::leanh::LeanObject,
    mut v_b_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1988_: usize = 0;
    let mut v_i_boxed_1989_: usize = 0;
    let mut v_b_boxed_1990_: u8 = 0;
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1988_ = crate::leanh::lean_unbox_usize(v_sz_1976_);
    crate::leanh::lean_dec(v_sz_1976_);
    v_i_boxed_1989_ = crate::leanh::lean_unbox_usize(v_i_1977_);
    crate::leanh::lean_dec(v_i_1977_);
    v_b_boxed_1990_ = (crate::leanh::lean_unbox(v_b_1978_) as u8);
    v_res_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1974_, v_as_1975_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_boxed_1990_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
    crate::leanh::lean_dec(v___y_1986_);
    crate::leanh::lean_dec_ref(v___y_1985_);
    crate::leanh::lean_dec(v___y_1984_);
    crate::leanh::lean_dec_ref(v___y_1983_);
    crate::leanh::lean_dec(v___y_1982_);
    crate::leanh::lean_dec_ref(v___y_1981_);
    crate::leanh::lean_dec(v___y_1980_);
    crate::leanh::lean_dec_ref(v___y_1979_);
    crate::leanh::lean_dec_ref(v_as_1975_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___lam__0(
    mut v_atLocal_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: u8,
    mut v_failed_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2007_: usize = 0;
    let mut v___x_2008_: usize = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2004_ = crate::leanh::lean_ctor_get(v___y_1999_, 2);
                v___x_2005_ = l_Lean_LocalContext_getFVarIds(v_lctx_2004_);
                v___x_2006_ = l_Array_reverse___redArg(v___x_2005_);
                v_sz_2007_ = lean_array_size(v___x_2006_);
                v___x_2008_ = 0usize;
                v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_withLocation_spec__1(v_atLocal_1992_, v___x_2006_, v_sz_2007_, v___x_2008_, v_a_1993_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                crate::leanh::lean_dec_ref(v___x_2006_);
                if crate::leanh::lean_obj_tag(v___x_2009_) == 0 {
                    v_a_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2030_ = (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2030_ == 0 {
                        v___x_2012_ = v___x_2009_;
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2010_);
                        crate::leanh::lean_dec(v___x_2009_);
                        v___x_2012_ = crate::leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2030_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2002_);
                    crate::leanh::lean_dec_ref(v___y_2001_);
                    crate::leanh::lean_dec(v___y_2000_);
                    crate::leanh::lean_dec_ref(v___y_1999_);
                    crate::leanh::lean_dec(v___y_1998_);
                    crate::leanh::lean_dec_ref(v___y_1997_);
                    crate::leanh::lean_dec(v___y_1996_);
                    crate::leanh::lean_dec_ref(v___y_1995_);
                    crate::leanh::lean_dec_ref(v_failed_1994_);
                    v_a_2031_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                    v_isSharedCheck_2038_ = (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2033_ = v___x_2009_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2031_);
                        crate::leanh::lean_dec(v___x_2009_);
                        v___x_2033_ = crate::leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2014_ = (crate::leanh::lean_unbox(v_a_2010_) as u8);
                crate::leanh::lean_dec(v_a_2010_);
                if v___x_2014_ == 0 {
                    crate::leanh::lean_del_object(v___x_2012_);
                    v___x_2015_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_1996_,
                        v___y_1999_,
                        v___y_2000_,
                        v___y_2001_,
                        v___y_2002_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2015_) == 0 {
                        v_a_2016_ = crate::leanh::lean_ctor_get(v___x_2015_, 0);
                        crate::leanh::lean_inc(v_a_2016_);
                        crate::leanh::lean_dec_ref_known(v___x_2015_, 1);
                        v___x_2017_ = crate::leanh::lean_apply_10(
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
                            crate::leanh::lean_box(0),
                        );
                        return v___x_2017_;
                    } else {
                        crate::leanh::lean_dec(v___y_2002_);
                        crate::leanh::lean_dec_ref(v___y_2001_);
                        crate::leanh::lean_dec(v___y_2000_);
                        crate::leanh::lean_dec_ref(v___y_1999_);
                        crate::leanh::lean_dec(v___y_1998_);
                        crate::leanh::lean_dec_ref(v___y_1997_);
                        crate::leanh::lean_dec(v___y_1996_);
                        crate::leanh::lean_dec_ref(v___y_1995_);
                        crate::leanh::lean_dec_ref(v_failed_1994_);
                        v_a_2018_ = crate::leanh::lean_ctor_get(v___x_2015_, 0);
                        v_isSharedCheck_2025_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2015_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_2015_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2018_);
                            crate::leanh::lean_dec(v___x_2015_);
                            v___x_2020_ = crate::leanh::lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2002_);
                    crate::leanh::lean_dec_ref(v___y_2001_);
                    crate::leanh::lean_dec(v___y_2000_);
                    crate::leanh::lean_dec_ref(v___y_1999_);
                    crate::leanh::lean_dec(v___y_1998_);
                    crate::leanh::lean_dec_ref(v___y_1997_);
                    crate::leanh::lean_dec(v___y_1996_);
                    crate::leanh::lean_dec_ref(v___y_1995_);
                    crate::leanh::lean_dec_ref(v_failed_1994_);
                    v___x_2026_ = crate::leanh::lean_box(0);
                    if v_isShared_2013_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2026_);
                        v___x_2028_ = v___x_2012_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
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
                    v_reuseFailAlloc_2024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
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
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
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
    mut v_atLocal_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_failed_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_17057__boxed_2051_: u8 = 0;
    let mut v_res_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_17057__boxed_2051_ = (crate::leanh::lean_unbox(v_a_2040_) as u8);
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
    mut v___x_2053_: *mut crate::leanh::LeanObject,
    mut v_atLocal_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_2064_) == 0 {
                    v_a_2065_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                    crate::leanh::lean_inc(v_a_2065_);
                    crate::leanh::lean_dec_ref_known(v___x_2064_, 1);
                    v___x_2066_ = crate::leanh::lean_apply_10(
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
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2066_;
                } else {
                    crate::leanh::lean_dec(v___y_2062_);
                    crate::leanh::lean_dec_ref(v___y_2061_);
                    crate::leanh::lean_dec(v___y_2060_);
                    crate::leanh::lean_dec_ref(v___y_2059_);
                    crate::leanh::lean_dec(v___y_2058_);
                    crate::leanh::lean_dec_ref(v___y_2057_);
                    crate::leanh::lean_dec(v___y_2056_);
                    crate::leanh::lean_dec_ref(v___y_2055_);
                    crate::leanh::lean_dec_ref(v_atLocal_2054_);
                    v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
                    v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_2064_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2064_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2067_);
                        crate::leanh::lean_dec(v___x_2064_);
                        v___x_2069_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
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
    mut v___x_2075_: *mut crate::leanh::LeanObject,
    mut v_atLocal_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0(v___x_2075_, v_atLocal_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
    return v_res_2086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(
    mut v_atLocal_2087_: *mut crate::leanh::LeanObject,
    mut v_as_2088_: *mut crate::leanh::LeanObject,
    mut v_i_2089_: usize,
    mut v_stop_2090_: usize,
    mut v_b_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: usize = 0;
    let mut v___x_2107_: usize = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2101_ = lean_usize_dec_eq(v_i_2089_, v_stop_2090_);
                if v___x_2101_ == 0 {
                    v___x_2102_ = lean_array_uget_borrowed(v_as_2088_, v_i_2089_);
                    crate::leanh::lean_inc_ref(v_atLocal_2087_);
                    crate::leanh::lean_inc(v___x_2102_);
                    v___f_2103_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                    crate::leanh::lean_closure_set(v___f_2103_, 0, v___x_2102_);
                    crate::leanh::lean_closure_set(v___f_2103_, 1, v_atLocal_2087_);
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
                    if crate::leanh::lean_obj_tag(v___x_2104_) == 0 {
                        v_a_2105_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
                        crate::leanh::lean_inc(v_a_2105_);
                        crate::leanh::lean_dec_ref_known(v___x_2104_, 1);
                        v___x_2106_ = 1usize;
                        v___x_2107_ = lean_usize_add(v_i_2089_, v___x_2106_);
                        v_i_2089_ = v___x_2107_;
                        v_b_2091_ = v_a_2105_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_atLocal_2087_);
                        return v___x_2104_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_atLocal_2087_);
                    v___x_2109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2109_, 0, v_b_2091_);
                    return v___x_2109_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3___boxed(
    mut v_atLocal_2110_: *mut crate::leanh::LeanObject,
    mut v_as_2111_: *mut crate::leanh::LeanObject,
    mut v_i_2112_: *mut crate::leanh::LeanObject,
    mut v_stop_2113_: *mut crate::leanh::LeanObject,
    mut v_b_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2124_: usize = 0;
    let mut v_stop_boxed_2125_: usize = 0;
    let mut v_res_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2124_ = crate::leanh::lean_unbox_usize(v_i_2112_);
    crate::leanh::lean_dec(v_i_2112_);
    v_stop_boxed_2125_ = crate::leanh::lean_unbox_usize(v_stop_2113_);
    crate::leanh::lean_dec(v_stop_2113_);
    v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_withLocation_spec__3(v_atLocal_2110_, v_as_2111_, v_i_boxed_2124_, v_stop_boxed_2125_, v_b_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    crate::leanh::lean_dec(v___y_2122_);
    crate::leanh::lean_dec_ref(v___y_2121_);
    crate::leanh::lean_dec(v___y_2120_);
    crate::leanh::lean_dec_ref(v___y_2119_);
    crate::leanh::lean_dec(v___y_2118_);
    crate::leanh::lean_dec_ref(v___y_2117_);
    crate::leanh::lean_dec(v___y_2116_);
    crate::leanh::lean_dec_ref(v___y_2115_);
    crate::leanh::lean_dec_ref(v_as_2111_);
    return v_res_2126_;
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation(
    mut v_loc_2127_: *mut crate::leanh::LeanObject,
    mut v_atLocal_2128_: *mut crate::leanh::LeanObject,
    mut v_atTarget_2129_: *mut crate::leanh::LeanObject,
    mut v_failed_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_a_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___y_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_unused_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2170_: u8 = 0;
    let mut v_isSharedCheck_2171_: u8 = 0;
    let mut v_a_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_hypotheses_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2189_: u8 = 0;
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_loc_2127_) == 0 {
                    v___x_2140_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_withMainContext___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_2140_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_2140_, 1, v_atTarget_2129_);
                    v___x_2141_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0___boxed as *mut core::ffi::c_void, 11, 2);
                    crate::leanh::lean_closure_set(v___x_2141_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_2141_, 1, v___x_2140_);
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
                    if crate::leanh::lean_obj_tag(v___x_2142_) == 0 {
                        v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2142_, 0);
                        crate::leanh::lean_inc(v_a_2143_);
                        crate::leanh::lean_dec_ref_known(v___x_2142_, 1);
                        v___x_2144_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_2132_, v_a_2134_, v_a_2136_, v_a_2138_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2144_) == 0 {
                            v_a_2145_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
                            crate::leanh::lean_inc(v_a_2145_);
                            crate::leanh::lean_dec_ref_known(v___x_2144_, 1);
                            v___x_2146_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v_a_2132_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2146_) == 0 {
                                crate::leanh::lean_dec(v_a_2145_);
                                v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                                crate::leanh::lean_inc(v_a_2147_);
                                crate::leanh::lean_dec_ref_known(v___x_2146_, 1);
                                v___f_2148_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_withLocation___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___f_2148_, 0, v_atLocal_2128_);
                                crate::leanh::lean_closure_set(v___f_2148_, 1, v_a_2143_);
                                crate::leanh::lean_closure_set(v___f_2148_, 2, v_failed_2130_);
                                v___x_2149_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withLocation_spec__2___redArg(v_a_2147_, v___f_2148_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
                                return v___x_2149_;
                            } else {
                                crate::leanh::lean_dec(v_a_2143_);
                                crate::leanh::lean_dec_ref(v_failed_2130_);
                                crate::leanh::lean_dec_ref(v_atLocal_2128_);
                                v_a_2150_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                                v_isSharedCheck_2171_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2146_)) as u8;
                                if v_isSharedCheck_2171_ == 0 {
                                    v___x_2152_ = v___x_2146_;
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2150_);
                                    crate::leanh::lean_dec(v___x_2146_);
                                    v___x_2152_ = crate::leanh::lean_box(0);
                                    v_isShared_2153_ = v_isSharedCheck_2171_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2143_);
                            crate::leanh::lean_dec_ref(v_failed_2130_);
                            crate::leanh::lean_dec_ref(v_atLocal_2128_);
                            v_a_2172_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
                            v_isSharedCheck_2179_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2144_)) as u8;
                            if v_isSharedCheck_2179_ == 0 {
                                v___x_2174_ = v___x_2144_;
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2172_);
                                crate::leanh::lean_dec(v___x_2144_);
                                v___x_2174_ = crate::leanh::lean_box(0);
                                v_isShared_2175_ = v_isSharedCheck_2179_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_failed_2130_);
                        crate::leanh::lean_dec_ref(v_atLocal_2128_);
                        v_a_2180_ = crate::leanh::lean_ctor_get(v___x_2142_, 0);
                        v_isSharedCheck_2187_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2142_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2142_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2180_);
                            crate::leanh::lean_dec(v___x_2142_);
                            v___x_2182_ = crate::leanh::lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_failed_2130_);
                    v_hypotheses_2188_ = crate::leanh::lean_ctor_get(v_loc_2127_, 0);
                    v_type_2189_ = crate::leanh::lean_ctor_get_uint8(
                        v_loc_2127_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_2196_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2197_ = lean_array_get_size(v_hypotheses_2188_);
                    v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
                    if v___x_2198_ == 0 {
                        crate::leanh::lean_dec_ref(v_atLocal_2128_);
                        state = 10;
                        continue;
                    } else {
                        v___x_2199_ = crate::leanh::lean_box(0);
                        v___x_2200_ = lean_nat_dec_le(v___x_2197_, v___x_2197_);
                        if v___x_2200_ == 0 {
                            if v___x_2198_ == 0 {
                                crate::leanh::lean_dec_ref(v_atLocal_2128_);
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
                    crate::leanh::lean_inc(v_a_2150_);
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
                    crate::leanh::lean_del_object(v___x_2152_);
                    crate::leanh::lean_dec(v_a_2150_);
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
                    if crate::leanh::lean_obj_tag(v___x_2156_) == 0 {
                        v_isSharedCheck_2164_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2156_)) as u8;
                        if v_isSharedCheck_2164_ == 0 {
                            v_unused_2165_ = crate::leanh::lean_ctor_get(v___x_2156_, 0);
                            crate::leanh::lean_dec(v_unused_2165_);
                            v___x_2158_ = v___x_2156_;
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2156_);
                            v___x_2158_ = crate::leanh::lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2164_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_2156_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2145_);
                    if v_isShared_2153_ == 0 {
                        v___x_2167_ = v___x_2152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2150_);
                        v___x_2167_ = v_reuseFailAlloc_2168_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2160_ = crate::leanh::lean_box(0);
                if v_isShared_2159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
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
                    v_reuseFailAlloc_2178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
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
                    crate::leanh::lean_dec_ref(v_atTarget_2129_);
                    v___x_2191_ = crate::leanh::lean_box(0);
                    v___x_2192_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
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
                if crate::leanh::lean_obj_tag(v___y_2195_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2195_, 1);
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_atTarget_2129_);
                    return v___y_2195_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withLocation___boxed(
    mut v_loc_2207_: *mut crate::leanh::LeanObject,
    mut v_atLocal_2208_: *mut crate::leanh::LeanObject,
    mut v_atTarget_2209_: *mut crate::leanh::LeanObject,
    mut v_failed_2210_: *mut crate::leanh::LeanObject,
    mut v_a_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_a_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2218_);
    crate::leanh::lean_dec_ref(v_a_2217_);
    crate::leanh::lean_dec(v_a_2216_);
    crate::leanh::lean_dec_ref(v_a_2215_);
    crate::leanh::lean_dec(v_a_2214_);
    crate::leanh::lean_dec_ref(v_a_2213_);
    crate::leanh::lean_dec(v_a_2212_);
    crate::leanh::lean_dec_ref(v_a_2211_);
    crate::leanh::lean_dec(v_loc_2207_);
    return v_res_2220_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___redArg(v___y_2226_, v___y_2227_, v___y_2228_);
    return v___x_2230_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2___boxed(
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__0_spec__2(v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
    crate::leanh::lean_dec(v___y_2238_);
    crate::leanh::lean_dec_ref(v___y_2237_);
    crate::leanh::lean_dec(v___y_2236_);
    crate::leanh::lean_dec_ref(v___y_2235_);
    crate::leanh::lean_dec(v___y_2234_);
    crate::leanh::lean_dec_ref(v___y_2233_);
    crate::leanh::lean_dec(v___y_2232_);
    crate::leanh::lean_dec_ref(v___y_2231_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___redArg(v___y_2248_);
    return v___x_2250_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4___boxed(
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1_spec__4(v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
    crate::leanh::lean_dec(v___y_2258_);
    crate::leanh::lean_dec_ref(v___y_2257_);
    crate::leanh::lean_dec(v___y_2256_);
    crate::leanh::lean_dec_ref(v___y_2255_);
    crate::leanh::lean_dec(v___y_2254_);
    crate::leanh::lean_dec_ref(v___y_2253_);
    crate::leanh::lean_dec(v___y_2252_);
    crate::leanh::lean_dec_ref(v___y_2251_);
    return v_res_2260_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(
    mut v_00_u03b1_2261_: *mut crate::leanh::LeanObject,
    mut v_x_2262_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___redArg(v_x_2262_, v_ctx_x3f_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
    return v___x_2273_;
}
pub unsafe fn l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1___boxed(
    mut v_00_u03b1_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_withLocation_spec__0_spec__1(v_00_u03b1_2274_, v_x_2275_, v_ctx_x3f_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
    crate::leanh::lean_dec(v___y_2284_);
    crate::leanh::lean_dec_ref(v___y_2283_);
    crate::leanh::lean_dec(v___y_2282_);
    crate::leanh::lean_dec_ref(v___y_2281_);
    crate::leanh::lean_dec(v___y_2280_);
    crate::leanh::lean_dec_ref(v___y_2279_);
    crate::leanh::lean_dec(v___y_2278_);
    crate::leanh::lean_dec_ref(v___y_2277_);
    return v_res_2286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Location(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Location(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Location(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Location(builtin);
}
