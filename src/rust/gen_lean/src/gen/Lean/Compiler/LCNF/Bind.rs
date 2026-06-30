// Lean compiler output
// Module: Lean.Compiler.LCNF.Bind
// Imports: Lean.Compiler.LCNF.InferType
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_expr_instantiate_rev,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_ptr_addr, lean_st_ref_get, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Lean::Compiler::BorrowedAnnotation::l_Lean_isMarkedBorrowed;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseCode___redArg, l_Lean_Compiler_LCNF_eraseParam___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg, l_Lean_Compiler_LCNF_mkAuxParam,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, l_Lean_Compiler_LCNF_Code_inferParamType,
    l_Lean_Compiler_LCNF_Code_inferType, l_Lean_Compiler_LCNF_mkAuxLetDecl,
    l_Lean_Compiler_LCNF_mkCasesResultType, runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_getArrowArity, l_Lean_Compiler_LCNF_instantiateForall,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_headBeta, l_Lean_FVarIdSet_insert, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value: leanh::LeanStringObject<58> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [96, 67, 111, 100, 101, 46, 98, 105, 110, 100, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32, 105, 116, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 97, 32, 111, 117, 116, 32, 111, 102, 32, 115, 99, 111, 112, 101, 32, 106, 111, 105, 110, 32, 112, 111, 105, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [96, 67, 111, 100, 101, 46, 98, 105, 110, 100, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32, 101, 109, 112, 116, 121, 32, 96, 99, 97, 115, 101, 115, 96, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        7699194985028780469 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Code_bind___redArg(
    mut v_pu_1127_: u8,
    mut v_inst_1128_: *mut leanh::LeanObject,
    mut v_c_1129_: *mut leanh::LeanObject,
    mut v_f_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = leanh::lean_box((v_pu_1127_) as usize);
    v___x_1132_ = leanh::lean_apply_3(v_inst_1128_, v___x_1131_, v_c_1129_, v_f_1130_);
    return v___x_1132_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(
    mut v_pu_1133_: *mut leanh::LeanObject,
    mut v_inst_1134_: *mut leanh::LeanObject,
    mut v_c_1135_: *mut leanh::LeanObject,
    mut v_f_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1137_: u8 = 0;
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1137_ = (leanh::lean_unbox(v_pu_1133_) as u8);
    v_res_1138_ = l_Lean_Compiler_LCNF_Code_bind___redArg(
        v_pu_boxed_1137_,
        v_inst_1134_,
        v_c_1135_,
        v_f_1136_,
    );
    return v_res_1138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_bind(
    mut v_m_1139_: *mut leanh::LeanObject,
    mut v_pu_1140_: u8,
    mut v_inst_1141_: *mut leanh::LeanObject,
    mut v_c_1142_: *mut leanh::LeanObject,
    mut v_f_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = leanh::lean_box((v_pu_1140_) as usize);
    v___x_1145_ = leanh::lean_apply_3(v_inst_1141_, v___x_1144_, v_c_1142_, v_f_1143_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_bind___boxed(
    mut v_m_1146_: *mut leanh::LeanObject,
    mut v_pu_1147_: *mut leanh::LeanObject,
    mut v_inst_1148_: *mut leanh::LeanObject,
    mut v_c_1149_: *mut leanh::LeanObject,
    mut v_f_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1151_: u8 = 0;
    let mut v_res_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1151_ = (leanh::lean_unbox(v_pu_1147_) as u8);
    v_res_1152_ = l_Lean_Compiler_LCNF_Code_bind(
        v_m_1146_,
        v_pu_boxed_1151_,
        v_inst_1148_,
        v_c_1149_,
        v_f_1150_,
    );
    return v_res_1152_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1153_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0);
    v___x_1155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1155_, 0, v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1);
    v___x_1157_ = leanh::lean_unsigned_to_nat(0);
    v___x_1158_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 1, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 2, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 3, v___x_1157_);
    leanh::lean_ctor_set(v___x_1158_, 4, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 5, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 6, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 7, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 8, v___x_1156_);
    leanh::lean_ctor_set(v___x_1158_, 9, v___x_1156_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(
    mut v_msg_1159_: *mut leanh::LeanObject,
    mut v___y_1160_: *mut leanh::LeanObject,
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1173_: u8 = 0;
    let mut v_env_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v___x_1179_: u8 = 0;
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1190_: u8 = 0;
    let mut v_unused_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1192_: u8 = 0;
    let mut v_a_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1165_ = leanh::lean_ctor_get(v___y_1162_, 2);
                v_ref_1166_ = leanh::lean_ctor_get(v___y_1162_, 5);
                v___x_1167_ = lean_st_ref_get(v___y_1163_);
                v___x_1168_ = lean_st_ref_get(v___y_1161_);
                v___x_1169_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1160_);
                if leanh::lean_obj_tag(v___x_1169_) == 0 {
                    v_a_1170_ = leanh::lean_ctor_get(v___x_1169_, 0);
                    v_isSharedCheck_1192_ = (!leanh::lean_is_exclusive(v___x_1169_)) as u8;
                    if v_isSharedCheck_1192_ == 0 {
                        v___x_1172_ = v___x_1169_;
                        v_isShared_1173_ = v_isSharedCheck_1192_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1170_);
                        leanh::lean_dec(v___x_1169_);
                        v___x_1172_ = leanh::lean_box(0);
                        v_isShared_1173_ = v_isSharedCheck_1192_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1168_);
                    leanh::lean_dec(v___x_1167_);
                    leanh::lean_dec_ref(v_msg_1159_);
                    v_a_1193_ = leanh::lean_ctor_get(v___x_1169_, 0);
                    v_isSharedCheck_1200_ = (!leanh::lean_is_exclusive(v___x_1169_)) as u8;
                    if v_isSharedCheck_1200_ == 0 {
                        v___x_1195_ = v___x_1169_;
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1193_);
                        leanh::lean_dec(v___x_1169_);
                        v___x_1195_ = leanh::lean_box(0);
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_1174_ = leanh::lean_ctor_get(v___x_1167_, 0);
                leanh::lean_inc_ref(v_env_1174_);
                leanh::lean_dec(v___x_1167_);
                v_lctx_1175_ = leanh::lean_ctor_get(v___x_1168_, 0);
                v_isSharedCheck_1190_ = (!leanh::lean_is_exclusive(v___x_1168_)) as u8;
                if v_isSharedCheck_1190_ == 0 {
                    v_unused_1191_ = leanh::lean_ctor_get(v___x_1168_, 1);
                    leanh::lean_dec(v_unused_1191_);
                    v___x_1177_ = v___x_1168_;
                    v_isShared_1178_ = v_isSharedCheck_1190_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_1175_);
                    leanh::lean_dec(v___x_1168_);
                    v___x_1177_ = leanh::lean_box(0);
                    v_isShared_1178_ = v_isSharedCheck_1190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1179_ = (leanh::lean_unbox(v_a_1170_) as u8);
                leanh::lean_dec(v_a_1170_);
                v___x_1180_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1175_, v___x_1179_);
                leanh::lean_dec_ref(v_lctx_1175_);
                v___x_1181_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2);
                leanh::lean_inc_ref(v_options_1165_);
                v___x_1182_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1182_, 0, v_env_1174_);
                leanh::lean_ctor_set(v___x_1182_, 1, v___x_1181_);
                leanh::lean_ctor_set(v___x_1182_, 2, v___x_1180_);
                leanh::lean_ctor_set(v___x_1182_, 3, v_options_1165_);
                if v_isShared_1178_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1177_, 3);
                    leanh::lean_ctor_set(v___x_1177_, 1, v_msg_1159_);
                    leanh::lean_ctor_set(v___x_1177_, 0, v___x_1182_);
                    v___x_1184_ = v___x_1177_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1189_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_msg_1159_);
                    v___x_1184_ = v_reuseFailAlloc_1189_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_1166_);
                v___x_1185_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1185_, 0, v_ref_1166_);
                leanh::lean_ctor_set(v___x_1185_, 1, v___x_1184_);
                if v_isShared_1173_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1172_, 1);
                    leanh::lean_ctor_set(v___x_1172_, 0, v___x_1185_);
                    v___x_1187_ = v___x_1172_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
                    v___x_1187_ = v_reuseFailAlloc_1188_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1187_;
            }
            5 => {
                if v_isShared_1196_ == 0 {
                    v___x_1198_ = v___x_1195_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
                    v___x_1198_ = v_reuseFailAlloc_1199_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(
    mut v_msg_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
    mut v___y_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
    leanh::lean_dec(v___y_1205_);
    leanh::lean_dec_ref(v___y_1204_);
    leanh::lean_dec(v___y_1203_);
    leanh::lean_dec_ref(v___y_1202_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(
    mut v_00_u03b1_1208_: *mut leanh::LeanObject,
    mut v_msg_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v___y_1213_: *mut leanh::LeanObject,
    mut v___y_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_1209_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(
    mut v_00_u03b1_1217_: *mut leanh::LeanObject,
    mut v_msg_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(v_00_u03b1_1217_, v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
    leanh::lean_dec(v___y_1223_);
    leanh::lean_dec_ref(v___y_1222_);
    leanh::lean_dec(v___y_1221_);
    leanh::lean_dec_ref(v___y_1220_);
    leanh::lean_dec(v___y_1219_);
    return v_res_1225_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(
    mut v_k_1226_: *mut leanh::LeanObject,
    mut v_t_1227_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: u8 = 0;
    let mut v___x_1233_: u8 = 0;
    let mut v___x_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1227_) == 0 {
                    v_k_1228_ = leanh::lean_ctor_get(v_t_1227_, 1);
                    v_l_1229_ = leanh::lean_ctor_get(v_t_1227_, 3);
                    v_r_1230_ = leanh::lean_ctor_get(v_t_1227_, 4);
                    v___x_1231_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1226_, v_k_1228_);
                    match v___x_1231_ {
                        0 => {
                            v_t_1227_ = v_l_1229_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_1233_ = 1;
                            return v___x_1233_;
                        }
                        _ => {
                            v_t_1227_ = v_r_1230_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1235_ = 0;
                    return v___x_1235_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(
    mut v_k_1236_: *mut leanh::LeanObject,
    mut v_t_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1238_: u8 = 0;
    let mut v_r_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_1236_, v_t_1237_);
    leanh::lean_dec(v_t_1237_);
    leanh::lean_dec(v_k_1236_);
    v_r_1239_ = leanh::lean_box((v_res_1238_) as usize);
    return v_r_1239_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ =
        l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0;
    v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
    return v___x_1242_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1244_ =
        l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2;
    v___x_1245_ = l_Lean_stringToMessageData(v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
    mut v_pu_1246_: u8,
    mut v_f_1247_: *mut leanh::LeanObject,
    mut v_c_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1264_: u8 = 0;
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_decl_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_decl_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1295_: u8 = 0;
    let mut v_params_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1317_: u8 = 0;
    let mut v_a_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1325_: u8 = 0;
    let mut v_a_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v_fvarId_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_unused_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v_typeName_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v_sz_1366_: usize = 0;
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_a_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_unused_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_fvarId_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1440_: u8 = 0;
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_unused_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v_a_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_a_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1472_: u8 = 0;
    let mut v_a_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1476_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut v_fvarId_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: usize = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v_unused_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_fvarId_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_unused_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_fvarId_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1553_: usize = 0;
    let mut v___x_1554_: usize = 0;
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_unused_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_fvarId_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: usize = 0;
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1596_: u8 = 0;
    let mut v_unused_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_fvarId_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1606_: u8 = 0;
    let mut v_persistent_1607_: u8 = 0;
    let mut v_k_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: usize = 0;
    let mut v___x_1615_: usize = 0;
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_fvarId_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_1636_: u8 = 0;
    let mut v_persistent_1637_: u8 = 0;
    let mut v_objs_x3f_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1644_: u8 = 0;
    let mut v___x_1645_: usize = 0;
    let mut v___x_1646_: usize = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1650_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut v_unused_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_fvarId_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1673_: usize = 0;
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_unused_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_c_1248_) {
                0 => {
                    v_decl_1255_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_k_1256_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_isSharedCheck_1272_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1258_ = v_c_1248_;
                        v_isShared_1259_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_1256_);
                        leanh::lean_inc(v_decl_1255_);
                        leanh::lean_dec(v_c_1248_);
                        v___x_1258_ = leanh::lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_decl_1273_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_k_1274_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_isSharedCheck_1290_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v___x_1276_ = v_c_1248_;
                        v_isShared_1277_ = v_isSharedCheck_1290_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_1274_);
                        leanh::lean_inc(v_decl_1273_);
                        leanh::lean_dec(v_c_1248_);
                        v___x_1276_ = leanh::lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1290_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_decl_1291_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_k_1292_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_isSharedCheck_1334_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1334_ == 0 {
                        v___x_1294_ = v_c_1248_;
                        v_isShared_1295_ = v_isSharedCheck_1334_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_1292_);
                        leanh::lean_inc(v_decl_1291_);
                        leanh::lean_dec(v_c_1248_);
                        v___x_1294_ = leanh::lean_box(0);
                        v_isShared_1295_ = v_isSharedCheck_1334_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    leanh::lean_dec_ref(v_f_1247_);
                    v_fvarId_1335_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v___x_1336_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_fvarId_1335_, v_a_1249_);
                    if v___x_1336_ == 0 {
                        v___x_1337_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1);
                        v___x_1338_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_1337_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                        if leanh::lean_obj_tag(v___x_1338_) == 0 {
                            v_isSharedCheck_1345_ =
                                (!leanh::lean_is_exclusive(v___x_1338_)) as u8;
                            if v_isSharedCheck_1345_ == 0 {
                                v_unused_1346_ = leanh::lean_ctor_get(v___x_1338_, 0);
                                leanh::lean_dec(v_unused_1346_);
                                v___x_1340_ = v___x_1338_;
                                v_isShared_1341_ = v_isSharedCheck_1345_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1338_);
                                v___x_1340_ = leanh::lean_box(0);
                                v_isShared_1341_ = v_isSharedCheck_1345_;
                                state = 17;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_c_1248_, 2);
                            v_a_1347_ = leanh::lean_ctor_get(v___x_1338_, 0);
                            v_isSharedCheck_1354_ =
                                (!leanh::lean_is_exclusive(v___x_1338_)) as u8;
                            if v_isSharedCheck_1354_ == 0 {
                                v___x_1349_ = v___x_1338_;
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1347_);
                                leanh::lean_dec(v___x_1338_);
                                v___x_1349_ = leanh::lean_box(0);
                                v_isShared_1350_ = v_isSharedCheck_1354_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        v___x_1355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1355_, 0, v_c_1248_);
                        return v___x_1355_;
                    }
                }
                4 => {
                    v_cases_1356_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_isSharedCheck_1421_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v___x_1358_ = v_c_1248_;
                        v_isShared_1359_ = v_isSharedCheck_1421_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_cases_1356_);
                        leanh::lean_dec(v_c_1248_);
                        v___x_1358_ = leanh::lean_box(0);
                        v_isShared_1359_ = v_isSharedCheck_1421_;
                        state = 21;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_1422_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    leanh::lean_inc(v_fvarId_1422_);
                    leanh::lean_dec_ref_known(v_c_1248_, 1);
                    leanh::lean_inc(v_a_1253_);
                    leanh::lean_inc_ref(v_a_1252_);
                    leanh::lean_inc(v_a_1251_);
                    leanh::lean_inc_ref(v_a_1250_);
                    v___x_1423_ = leanh::lean_apply_6(
                        v_f_1247_,
                        v_fvarId_1422_,
                        v_a_1250_,
                        v_a_1251_,
                        v_a_1252_,
                        v_a_1253_,
                        leanh::lean_box(0),
                    );
                    return v___x_1423_;
                }
                6 => {
                    v_type_1424_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_isSharedCheck_1481_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1481_ == 0 {
                        v___x_1426_ = v_c_1248_;
                        v_isShared_1427_ = v_isSharedCheck_1481_;
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_inc(v_type_1424_);
                        leanh::lean_dec(v_c_1248_);
                        v___x_1426_ = leanh::lean_box(0);
                        v_isShared_1427_ = v_isSharedCheck_1481_;
                        state = 34;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_1482_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_i_1483_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_y_1484_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    v_k_1485_ = leanh::lean_ctor_get(v_c_1248_, 3);
                    leanh::lean_inc_ref(v_k_1485_);
                    v___x_1486_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1485_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1486_) == 0 {
                        v_a_1487_ = leanh::lean_ctor_get(v___x_1486_, 0);
                        v_isSharedCheck_1511_ =
                            (!leanh::lean_is_exclusive(v___x_1486_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v___x_1489_ = v___x_1486_;
                            v_isShared_1490_ = v_isSharedCheck_1511_;
                            state = 46;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1487_);
                            leanh::lean_dec(v___x_1486_);
                            v___x_1489_ = leanh::lean_box(0);
                            v_isShared_1490_ = v_isSharedCheck_1511_;
                            state = 46;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 4);
                        return v___x_1486_;
                    }
                }
                8 => {
                    v_fvarId_1512_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_i_1513_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_y_1514_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    v_k_1515_ = leanh::lean_ctor_get(v_c_1248_, 3);
                    leanh::lean_inc_ref(v_k_1515_);
                    v___x_1516_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1515_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1516_) == 0 {
                        v_a_1517_ = leanh::lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1541_ =
                            (!leanh::lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1541_ == 0 {
                            v___x_1519_ = v___x_1516_;
                            v_isShared_1520_ = v_isSharedCheck_1541_;
                            state = 51;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1517_);
                            leanh::lean_dec(v___x_1516_);
                            v___x_1519_ = leanh::lean_box(0);
                            v_isShared_1520_ = v_isSharedCheck_1541_;
                            state = 51;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 4);
                        return v___x_1516_;
                    }
                }
                9 => {
                    v_fvarId_1542_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_i_1543_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_offset_1544_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    v_y_1545_ = leanh::lean_ctor_get(v_c_1248_, 3);
                    v_ty_1546_ = leanh::lean_ctor_get(v_c_1248_, 4);
                    v_k_1547_ = leanh::lean_ctor_get(v_c_1248_, 5);
                    leanh::lean_inc_ref(v_k_1547_);
                    v___x_1548_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1547_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1548_) == 0 {
                        v_a_1549_ = leanh::lean_ctor_get(v___x_1548_, 0);
                        v_isSharedCheck_1575_ =
                            (!leanh::lean_is_exclusive(v___x_1548_)) as u8;
                        if v_isSharedCheck_1575_ == 0 {
                            v___x_1551_ = v___x_1548_;
                            v_isShared_1552_ = v_isSharedCheck_1575_;
                            state = 56;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1549_);
                            leanh::lean_dec(v___x_1548_);
                            v___x_1551_ = leanh::lean_box(0);
                            v_isShared_1552_ = v_isSharedCheck_1575_;
                            state = 56;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 6);
                        return v___x_1548_;
                    }
                }
                10 => {
                    v_fvarId_1576_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_cidx_1577_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_k_1578_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    leanh::lean_inc_ref(v_k_1578_);
                    v___x_1579_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1578_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1579_) == 0 {
                        v_a_1580_ = leanh::lean_ctor_get(v___x_1579_, 0);
                        v_isSharedCheck_1603_ =
                            (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                        if v_isSharedCheck_1603_ == 0 {
                            v___x_1582_ = v___x_1579_;
                            v_isShared_1583_ = v_isSharedCheck_1603_;
                            state = 61;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1580_);
                            leanh::lean_dec(v___x_1579_);
                            v___x_1582_ = leanh::lean_box(0);
                            v_isShared_1583_ = v_isSharedCheck_1603_;
                            state = 61;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 3);
                        return v___x_1579_;
                    }
                }
                11 => {
                    v_fvarId_1604_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_n_1605_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_check_1606_ = leanh::lean_ctor_get_uint8(
                        v_c_1248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_1607_ = leanh::lean_ctor_get_uint8(
                        v_c_1248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_1608_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    leanh::lean_inc_ref(v_k_1608_);
                    v___x_1609_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1608_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1609_) == 0 {
                        v_a_1610_ = leanh::lean_ctor_get(v___x_1609_, 0);
                        v_isSharedCheck_1633_ =
                            (!leanh::lean_is_exclusive(v___x_1609_)) as u8;
                        if v_isSharedCheck_1633_ == 0 {
                            v___x_1612_ = v___x_1609_;
                            v_isShared_1613_ = v_isSharedCheck_1633_;
                            state = 66;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1610_);
                            leanh::lean_dec(v___x_1609_);
                            v___x_1612_ = leanh::lean_box(0);
                            v_isShared_1613_ = v_isSharedCheck_1633_;
                            state = 66;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 3);
                        return v___x_1609_;
                    }
                }
                12 => {
                    v_fvarId_1634_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_n_1635_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    v_check_1636_ = leanh::lean_ctor_get_uint8(
                        v_c_1248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_1637_ = leanh::lean_ctor_get_uint8(
                        v_c_1248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_1638_ = leanh::lean_ctor_get(v_c_1248_, 2);
                    v_k_1639_ = leanh::lean_ctor_get(v_c_1248_, 3);
                    leanh::lean_inc_ref(v_k_1639_);
                    v___x_1640_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1639_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1640_) == 0 {
                        v_a_1641_ = leanh::lean_ctor_get(v___x_1640_, 0);
                        v_isSharedCheck_1665_ =
                            (!leanh::lean_is_exclusive(v___x_1640_)) as u8;
                        if v_isSharedCheck_1665_ == 0 {
                            v___x_1643_ = v___x_1640_;
                            v_isShared_1644_ = v_isSharedCheck_1665_;
                            state = 71;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1641_);
                            leanh::lean_dec(v___x_1640_);
                            v___x_1643_ = leanh::lean_box(0);
                            v_isShared_1644_ = v_isSharedCheck_1665_;
                            state = 71;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 4);
                        return v___x_1640_;
                    }
                }
                _ => {
                    v_fvarId_1666_ = leanh::lean_ctor_get(v_c_1248_, 0);
                    v_k_1667_ = leanh::lean_ctor_get(v_c_1248_, 1);
                    leanh::lean_inc_ref(v_k_1667_);
                    v___x_1668_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1667_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                    if leanh::lean_obj_tag(v___x_1668_) == 0 {
                        v_a_1669_ = leanh::lean_ctor_get(v___x_1668_, 0);
                        v_isSharedCheck_1691_ =
                            (!leanh::lean_is_exclusive(v___x_1668_)) as u8;
                        if v_isSharedCheck_1691_ == 0 {
                            v___x_1671_ = v___x_1668_;
                            v_isShared_1672_ = v_isSharedCheck_1691_;
                            state = 76;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1669_);
                            leanh::lean_dec(v___x_1668_);
                            v___x_1671_ = leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1691_;
                            state = 76;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_c_1248_, 2);
                        return v___x_1668_;
                    }
                }
            },
            1 => {
                v___x_1260_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1246_, v_f_1247_, v_k_1256_, v_a_1249_, v_a_1250_, v_a_1251_,
                        v_a_1252_, v_a_1253_,
                    );
                if leanh::lean_obj_tag(v___x_1260_) == 0 {
                    v_a_1261_ = leanh::lean_ctor_get(v___x_1260_, 0);
                    v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v___x_1260_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1263_ = v___x_1260_;
                        v_isShared_1264_ = v_isSharedCheck_1271_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1261_);
                        leanh::lean_dec(v___x_1260_);
                        v___x_1263_ = leanh::lean_box(0);
                        v_isShared_1264_ = v_isSharedCheck_1271_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1258_);
                    leanh::lean_dec_ref(v_decl_1255_);
                    return v___x_1260_;
                }
            }
            2 => {
                if v_isShared_1259_ == 0 {
                    leanh::lean_ctor_set(v___x_1258_, 1, v_a_1261_);
                    v___x_1266_ = v___x_1258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_decl_1255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_a_1261_);
                    v___x_1266_ = v_reuseFailAlloc_1270_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1264_ == 0 {
                    leanh::lean_ctor_set(v___x_1263_, 0, v___x_1266_);
                    v___x_1268_ = v___x_1263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
                    v___x_1268_ = v_reuseFailAlloc_1269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1268_;
            }
            5 => {
                v___x_1278_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1246_, v_f_1247_, v_k_1274_, v_a_1249_, v_a_1250_, v_a_1251_,
                        v_a_1252_, v_a_1253_,
                    );
                if leanh::lean_obj_tag(v___x_1278_) == 0 {
                    v_a_1279_ = leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1289_ = (!leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1289_ == 0 {
                        v___x_1281_ = v___x_1278_;
                        v_isShared_1282_ = v_isSharedCheck_1289_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1279_);
                        leanh::lean_dec(v___x_1278_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1289_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1276_);
                    leanh::lean_dec_ref(v_decl_1273_);
                    return v___x_1278_;
                }
            }
            6 => {
                if v_isShared_1277_ == 0 {
                    leanh::lean_ctor_set(v___x_1276_, 1, v_a_1279_);
                    v___x_1284_ = v___x_1276_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1288_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_decl_1273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1288_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1282_ == 0 {
                    leanh::lean_ctor_set(v___x_1281_, 0, v___x_1284_);
                    v___x_1286_ = v___x_1281_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
                    v___x_1286_ = v_reuseFailAlloc_1287_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1286_;
            }
            9 => {
                v_params_1296_ = leanh::lean_ctor_get(v_decl_1291_, 2);
                leanh::lean_inc_ref(v_params_1296_);
                v_value_1297_ = leanh::lean_ctor_get(v_decl_1291_, 4);
                leanh::lean_inc_ref(v_value_1297_);
                leanh::lean_inc_ref(v_f_1247_);
                v___x_1298_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1246_,
                        v_f_1247_,
                        v_value_1297_,
                        v_a_1249_,
                        v_a_1250_,
                        v_a_1251_,
                        v_a_1252_,
                        v_a_1253_,
                    );
                if leanh::lean_obj_tag(v___x_1298_) == 0 {
                    v_a_1299_ = leanh::lean_ctor_get(v___x_1298_, 0);
                    leanh::lean_inc_n(v_a_1299_, 2);
                    leanh::lean_dec_ref_known(v___x_1298_, 1);
                    leanh::lean_inc_ref(v_params_1296_);
                    v___x_1300_ = l_Lean_Compiler_LCNF_Code_inferParamType(
                        v_pu_1246_,
                        v_params_1296_,
                        v_a_1299_,
                        v_a_1250_,
                        v_a_1251_,
                        v_a_1252_,
                        v_a_1253_,
                    );
                    if leanh::lean_obj_tag(v___x_1300_) == 0 {
                        v_a_1301_ = leanh::lean_ctor_get(v___x_1300_, 0);
                        leanh::lean_inc(v_a_1301_);
                        leanh::lean_dec_ref_known(v___x_1300_, 1);
                        v___x_1302_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_1246_, v_decl_1291_, v_a_1301_, v_params_1296_, v_a_1299_, v_a_1251_);
                        if leanh::lean_obj_tag(v___x_1302_) == 0 {
                            v_a_1303_ = leanh::lean_ctor_get(v___x_1302_, 0);
                            leanh::lean_inc(v_a_1303_);
                            leanh::lean_dec_ref_known(v___x_1302_, 1);
                            v_fvarId_1304_ = leanh::lean_ctor_get(v_a_1303_, 0);
                            leanh::lean_inc(v_fvarId_1304_);
                            leanh::lean_inc(v_a_1249_);
                            v___x_1305_ = l_Lean_FVarIdSet_insert(v_a_1249_, v_fvarId_1304_);
                            v___x_1306_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_1246_, v_f_1247_, v_k_1292_, v___x_1305_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                            leanh::lean_dec(v___x_1305_);
                            if leanh::lean_obj_tag(v___x_1306_) == 0 {
                                v_a_1307_ = leanh::lean_ctor_get(v___x_1306_, 0);
                                v_isSharedCheck_1317_ =
                                    (!leanh::lean_is_exclusive(v___x_1306_)) as u8;
                                if v_isSharedCheck_1317_ == 0 {
                                    v___x_1309_ = v___x_1306_;
                                    v_isShared_1310_ = v_isSharedCheck_1317_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1307_);
                                    leanh::lean_dec(v___x_1306_);
                                    v___x_1309_ = leanh::lean_box(0);
                                    v_isShared_1310_ = v_isSharedCheck_1317_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1303_);
                                leanh::lean_del_object(v___x_1294_);
                                return v___x_1306_;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1294_);
                            leanh::lean_dec_ref(v_k_1292_);
                            leanh::lean_dec_ref(v_f_1247_);
                            v_a_1318_ = leanh::lean_ctor_get(v___x_1302_, 0);
                            v_isSharedCheck_1325_ =
                                (!leanh::lean_is_exclusive(v___x_1302_)) as u8;
                            if v_isSharedCheck_1325_ == 0 {
                                v___x_1320_ = v___x_1302_;
                                v_isShared_1321_ = v_isSharedCheck_1325_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1318_);
                                leanh::lean_dec(v___x_1302_);
                                v___x_1320_ = leanh::lean_box(0);
                                v_isShared_1321_ = v_isSharedCheck_1325_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1299_);
                        leanh::lean_dec_ref(v_params_1296_);
                        leanh::lean_del_object(v___x_1294_);
                        leanh::lean_dec_ref(v_k_1292_);
                        leanh::lean_dec_ref(v_decl_1291_);
                        leanh::lean_dec_ref(v_f_1247_);
                        v_a_1326_ = leanh::lean_ctor_get(v___x_1300_, 0);
                        v_isSharedCheck_1333_ =
                            (!leanh::lean_is_exclusive(v___x_1300_)) as u8;
                        if v_isSharedCheck_1333_ == 0 {
                            v___x_1328_ = v___x_1300_;
                            v_isShared_1329_ = v_isSharedCheck_1333_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1326_);
                            leanh::lean_dec(v___x_1300_);
                            v___x_1328_ = leanh::lean_box(0);
                            v_isShared_1329_ = v_isSharedCheck_1333_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_params_1296_);
                    leanh::lean_del_object(v___x_1294_);
                    leanh::lean_dec_ref(v_k_1292_);
                    leanh::lean_dec_ref(v_decl_1291_);
                    leanh::lean_dec_ref(v_f_1247_);
                    return v___x_1298_;
                }
            }
            10 => {
                if v_isShared_1295_ == 0 {
                    leanh::lean_ctor_set(v___x_1294_, 1, v_a_1307_);
                    leanh::lean_ctor_set(v___x_1294_, 0, v_a_1303_);
                    v___x_1312_ = v___x_1294_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1316_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_a_1307_);
                    v___x_1312_ = v_reuseFailAlloc_1316_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1310_ == 0 {
                    leanh::lean_ctor_set(v___x_1309_, 0, v___x_1312_);
                    v___x_1314_ = v___x_1309_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
                    v___x_1314_ = v_reuseFailAlloc_1315_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1314_;
            }
            13 => {
                if v_isShared_1321_ == 0 {
                    v___x_1323_ = v___x_1320_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
                    v___x_1323_ = v_reuseFailAlloc_1324_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1323_;
            }
            15 => {
                if v_isShared_1329_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
                    v___x_1331_ = v_reuseFailAlloc_1332_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1331_;
            }
            17 => {
                if v_isShared_1341_ == 0 {
                    leanh::lean_ctor_set(v___x_1340_, 0, v_c_1248_);
                    v___x_1343_ = v___x_1340_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_c_1248_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1343_;
            }
            19 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1352_;
            }
            21 => {
                v_typeName_1360_ = leanh::lean_ctor_get(v_cases_1356_, 0);
                v_discr_1361_ = leanh::lean_ctor_get(v_cases_1356_, 2);
                v_alts_1362_ = leanh::lean_ctor_get(v_cases_1356_, 3);
                v_isSharedCheck_1419_ = (!leanh::lean_is_exclusive(v_cases_1356_)) as u8;
                if v_isSharedCheck_1419_ == 0 {
                    v_unused_1420_ = leanh::lean_ctor_get(v_cases_1356_, 1);
                    leanh::lean_dec(v_unused_1420_);
                    v___x_1364_ = v_cases_1356_;
                    v_isShared_1365_ = v_isSharedCheck_1419_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_inc(v_alts_1362_);
                    leanh::lean_inc(v_discr_1361_);
                    leanh::lean_inc(v_typeName_1360_);
                    leanh::lean_dec(v_cases_1356_);
                    v___x_1364_ = leanh::lean_box(0);
                    v_isShared_1365_ = v_isSharedCheck_1419_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_sz_1366_ = lean_array_size(v_alts_1362_);
                v___x_1367_ = 0usize;
                v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_1246_, v_f_1247_, v_sz_1366_, v___x_1367_, v_alts_1362_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                if leanh::lean_obj_tag(v___x_1368_) == 0 {
                    v_a_1369_ = leanh::lean_ctor_get(v___x_1368_, 0);
                    leanh::lean_inc(v_a_1369_);
                    leanh::lean_dec_ref_known(v___x_1368_, 1);
                    v___x_1398_ = lean_array_get_size(v_a_1369_);
                    v___x_1399_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
                    if v___x_1400_ == 0 {
                        v___y_1371_ = v_a_1250_;
                        v___y_1372_ = v_a_1251_;
                        v___y_1373_ = v_a_1252_;
                        v___y_1374_ = v_a_1253_;
                        state = 23;
                        continue;
                    } else {
                        v___x_1401_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3);
                        v___x_1402_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_1401_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
                        if leanh::lean_obj_tag(v___x_1402_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1402_, 1);
                            v___y_1371_ = v_a_1250_;
                            v___y_1372_ = v_a_1251_;
                            v___y_1373_ = v_a_1252_;
                            v___y_1374_ = v_a_1253_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1369_);
                            leanh::lean_del_object(v___x_1364_);
                            leanh::lean_dec(v_discr_1361_);
                            leanh::lean_dec(v_typeName_1360_);
                            leanh::lean_del_object(v___x_1358_);
                            v_a_1403_ = leanh::lean_ctor_get(v___x_1402_, 0);
                            v_isSharedCheck_1410_ =
                                (!leanh::lean_is_exclusive(v___x_1402_)) as u8;
                            if v_isSharedCheck_1410_ == 0 {
                                v___x_1405_ = v___x_1402_;
                                v_isShared_1406_ = v_isSharedCheck_1410_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1403_);
                                leanh::lean_dec(v___x_1402_);
                                v___x_1405_ = leanh::lean_box(0);
                                v_isShared_1406_ = v_isSharedCheck_1410_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1364_);
                    leanh::lean_dec(v_discr_1361_);
                    leanh::lean_dec(v_typeName_1360_);
                    leanh::lean_del_object(v___x_1358_);
                    v_a_1411_ = leanh::lean_ctor_get(v___x_1368_, 0);
                    v_isSharedCheck_1418_ = (!leanh::lean_is_exclusive(v___x_1368_)) as u8;
                    if v_isSharedCheck_1418_ == 0 {
                        v___x_1413_ = v___x_1368_;
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1411_);
                        leanh::lean_dec(v___x_1368_);
                        v___x_1413_ = leanh::lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1418_;
                        state = 32;
                        continue;
                    }
                }
            }
            23 => {
                leanh::lean_inc(v_a_1369_);
                v___x_1375_ = l_Lean_Compiler_LCNF_mkCasesResultType(
                    v_pu_1246_,
                    v_a_1369_,
                    v___y_1371_,
                    v___y_1372_,
                    v___y_1373_,
                    v___y_1374_,
                );
                if leanh::lean_obj_tag(v___x_1375_) == 0 {
                    v_a_1376_ = leanh::lean_ctor_get(v___x_1375_, 0);
                    v_isSharedCheck_1389_ = (!leanh::lean_is_exclusive(v___x_1375_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1378_ = v___x_1375_;
                        v_isShared_1379_ = v_isSharedCheck_1389_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1376_);
                        leanh::lean_dec(v___x_1375_);
                        v___x_1378_ = leanh::lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1389_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1369_);
                    leanh::lean_del_object(v___x_1364_);
                    leanh::lean_dec(v_discr_1361_);
                    leanh::lean_dec(v_typeName_1360_);
                    leanh::lean_del_object(v___x_1358_);
                    v_a_1390_ = leanh::lean_ctor_get(v___x_1375_, 0);
                    v_isSharedCheck_1397_ = (!leanh::lean_is_exclusive(v___x_1375_)) as u8;
                    if v_isSharedCheck_1397_ == 0 {
                        v___x_1392_ = v___x_1375_;
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1390_);
                        leanh::lean_dec(v___x_1375_);
                        v___x_1392_ = leanh::lean_box(0);
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 28;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_1365_ == 0 {
                    leanh::lean_ctor_set(v___x_1364_, 3, v_a_1369_);
                    leanh::lean_ctor_set(v___x_1364_, 1, v_a_1376_);
                    v___x_1381_ = v___x_1364_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_typeName_1360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_a_1376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_discr_1361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_a_1369_);
                    v___x_1381_ = v_reuseFailAlloc_1388_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1359_ == 0 {
                    leanh::lean_ctor_set(v___x_1358_, 0, v___x_1381_);
                    v___x_1383_ = v___x_1358_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1387_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1381_);
                    v___x_1383_ = v_reuseFailAlloc_1387_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_1379_ == 0 {
                    leanh::lean_ctor_set(v___x_1378_, 0, v___x_1383_);
                    v___x_1385_ = v___x_1378_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1385_;
            }
            28 => {
                if v_isShared_1393_ == 0 {
                    v___x_1395_ = v___x_1392_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
                    v___x_1395_ = v_reuseFailAlloc_1396_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1395_;
            }
            30 => {
                if v_isShared_1406_ == 0 {
                    v___x_1408_ = v___x_1405_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1408_;
            }
            32 => {
                if v_isShared_1414_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
                    v___x_1416_ = v_reuseFailAlloc_1417_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1416_;
            }
            34 => {
                v___x_1428_ = 0;
                v___x_1429_ = l_Lean_Compiler_LCNF_mkAuxParam(
                    v_pu_1246_,
                    v_type_1424_,
                    v___x_1428_,
                    v_a_1250_,
                    v_a_1251_,
                    v_a_1252_,
                    v_a_1253_,
                );
                if leanh::lean_obj_tag(v___x_1429_) == 0 {
                    v_a_1430_ = leanh::lean_ctor_get(v___x_1429_, 0);
                    leanh::lean_inc(v_a_1430_);
                    leanh::lean_dec_ref_known(v___x_1429_, 1);
                    v_fvarId_1431_ = leanh::lean_ctor_get(v_a_1430_, 0);
                    leanh::lean_inc(v_a_1253_);
                    leanh::lean_inc_ref(v_a_1252_);
                    leanh::lean_inc(v_a_1251_);
                    leanh::lean_inc_ref(v_a_1250_);
                    leanh::lean_inc(v_fvarId_1431_);
                    v___x_1432_ = leanh::lean_apply_6(
                        v_f_1247_,
                        v_fvarId_1431_,
                        v_a_1250_,
                        v_a_1251_,
                        v_a_1252_,
                        v_a_1253_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1432_) == 0 {
                        v_a_1433_ = leanh::lean_ctor_get(v___x_1432_, 0);
                        leanh::lean_inc_n(v_a_1433_, 2);
                        leanh::lean_dec_ref_known(v___x_1432_, 1);
                        v___x_1434_ = l_Lean_Compiler_LCNF_Code_inferType(
                            v_pu_1246_, v_a_1433_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_,
                        );
                        if leanh::lean_obj_tag(v___x_1434_) == 0 {
                            v_a_1435_ = leanh::lean_ctor_get(v___x_1434_, 0);
                            leanh::lean_inc(v_a_1435_);
                            leanh::lean_dec_ref_known(v___x_1434_, 1);
                            v___x_1436_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                v_pu_1246_, v_a_1433_, v_a_1251_,
                            );
                            leanh::lean_dec(v_a_1433_);
                            if leanh::lean_obj_tag(v___x_1436_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1436_, 1);
                                v___x_1437_ = l_Lean_Compiler_LCNF_eraseParam___redArg(
                                    v_pu_1246_, v_a_1430_, v_a_1251_,
                                );
                                leanh::lean_dec(v_a_1430_);
                                if leanh::lean_obj_tag(v___x_1437_) == 0 {
                                    v_isSharedCheck_1447_ =
                                        (!leanh::lean_is_exclusive(v___x_1437_)) as u8;
                                    if v_isSharedCheck_1447_ == 0 {
                                        v_unused_1448_ =
                                            leanh::lean_ctor_get(v___x_1437_, 0);
                                        leanh::lean_dec(v_unused_1448_);
                                        v___x_1439_ = v___x_1437_;
                                        v_isShared_1440_ = v_isSharedCheck_1447_;
                                        state = 35;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1437_);
                                        v___x_1439_ = leanh::lean_box(0);
                                        v_isShared_1440_ = v_isSharedCheck_1447_;
                                        state = 35;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1435_);
                                    leanh::lean_del_object(v___x_1426_);
                                    v_a_1449_ = leanh::lean_ctor_get(v___x_1437_, 0);
                                    v_isSharedCheck_1456_ =
                                        (!leanh::lean_is_exclusive(v___x_1437_)) as u8;
                                    if v_isSharedCheck_1456_ == 0 {
                                        v___x_1451_ = v___x_1437_;
                                        v_isShared_1452_ = v_isSharedCheck_1456_;
                                        state = 38;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1449_);
                                        leanh::lean_dec(v___x_1437_);
                                        v___x_1451_ = leanh::lean_box(0);
                                        v_isShared_1452_ = v_isSharedCheck_1456_;
                                        state = 38;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_1435_);
                                leanh::lean_dec(v_a_1430_);
                                leanh::lean_del_object(v___x_1426_);
                                v_a_1457_ = leanh::lean_ctor_get(v___x_1436_, 0);
                                v_isSharedCheck_1464_ =
                                    (!leanh::lean_is_exclusive(v___x_1436_)) as u8;
                                if v_isSharedCheck_1464_ == 0 {
                                    v___x_1459_ = v___x_1436_;
                                    v_isShared_1460_ = v_isSharedCheck_1464_;
                                    state = 40;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1457_);
                                    leanh::lean_dec(v___x_1436_);
                                    v___x_1459_ = leanh::lean_box(0);
                                    v_isShared_1460_ = v_isSharedCheck_1464_;
                                    state = 40;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1433_);
                            leanh::lean_dec(v_a_1430_);
                            leanh::lean_del_object(v___x_1426_);
                            v_a_1465_ = leanh::lean_ctor_get(v___x_1434_, 0);
                            v_isSharedCheck_1472_ =
                                (!leanh::lean_is_exclusive(v___x_1434_)) as u8;
                            if v_isSharedCheck_1472_ == 0 {
                                v___x_1467_ = v___x_1434_;
                                v_isShared_1468_ = v_isSharedCheck_1472_;
                                state = 42;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1465_);
                                leanh::lean_dec(v___x_1434_);
                                v___x_1467_ = leanh::lean_box(0);
                                v_isShared_1468_ = v_isSharedCheck_1472_;
                                state = 42;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1430_);
                        leanh::lean_del_object(v___x_1426_);
                        return v___x_1432_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1426_);
                    leanh::lean_dec_ref(v_f_1247_);
                    v_a_1473_ = leanh::lean_ctor_get(v___x_1429_, 0);
                    v_isSharedCheck_1480_ = (!leanh::lean_is_exclusive(v___x_1429_)) as u8;
                    if v_isSharedCheck_1480_ == 0 {
                        v___x_1475_ = v___x_1429_;
                        v_isShared_1476_ = v_isSharedCheck_1480_;
                        state = 44;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1473_);
                        leanh::lean_dec(v___x_1429_);
                        v___x_1475_ = leanh::lean_box(0);
                        v_isShared_1476_ = v_isSharedCheck_1480_;
                        state = 44;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_1427_ == 0 {
                    leanh::lean_ctor_set(v___x_1426_, 0, v_a_1435_);
                    v___x_1442_ = v___x_1426_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1446_ = leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1435_);
                    v___x_1442_ = v_reuseFailAlloc_1446_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_1440_ == 0 {
                    leanh::lean_ctor_set(v___x_1439_, 0, v___x_1442_);
                    v___x_1444_ = v___x_1439_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1444_;
            }
            38 => {
                if v_isShared_1452_ == 0 {
                    v___x_1454_ = v___x_1451_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
                    v___x_1454_ = v_reuseFailAlloc_1455_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1454_;
            }
            40 => {
                if v_isShared_1460_ == 0 {
                    v___x_1462_ = v___x_1459_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1462_;
            }
            42 => {
                if v_isShared_1468_ == 0 {
                    v___x_1470_ = v___x_1467_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_1471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
                    v___x_1470_ = v_reuseFailAlloc_1471_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_1470_;
            }
            44 => {
                if v_isShared_1476_ == 0 {
                    v___x_1478_ = v___x_1475_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
                    v___x_1478_ = v_reuseFailAlloc_1479_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_1478_;
            }
            46 => {
                v___x_1491_ = lean_ptr_addr(v_k_1485_);
                v___x_1492_ = lean_ptr_addr(v_a_1487_);
                v___x_1493_ = lean_usize_dec_eq(v___x_1491_, v___x_1492_);
                if v___x_1493_ == 0 {
                    leanh::lean_inc(v_y_1484_);
                    leanh::lean_inc(v_i_1483_);
                    leanh::lean_inc(v_fvarId_1482_);
                    v_isSharedCheck_1503_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1503_ == 0 {
                        v_unused_1504_ = leanh::lean_ctor_get(v_c_1248_, 3);
                        leanh::lean_dec(v_unused_1504_);
                        v_unused_1505_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1505_);
                        v_unused_1506_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1506_);
                        v_unused_1507_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1507_);
                        v___x_1495_ = v_c_1248_;
                        v_isShared_1496_ = v_isSharedCheck_1503_;
                        state = 47;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1495_ = leanh::lean_box(0);
                        v_isShared_1496_ = v_isSharedCheck_1503_;
                        state = 47;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1487_);
                    if v_isShared_1490_ == 0 {
                        leanh::lean_ctor_set(v___x_1489_, 0, v_c_1248_);
                        v___x_1509_ = v___x_1489_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_c_1248_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 50;
                        continue;
                    }
                }
            }
            47 => {
                if v_isShared_1496_ == 0 {
                    leanh::lean_ctor_set(v___x_1495_, 3, v_a_1487_);
                    v___x_1498_ = v___x_1495_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = leanh::lean_alloc_ctor(7, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_fvarId_1482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_i_1483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_y_1484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_a_1487_);
                    v___x_1498_ = v_reuseFailAlloc_1502_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                if v_isShared_1490_ == 0 {
                    leanh::lean_ctor_set(v___x_1489_, 0, v___x_1498_);
                    v___x_1500_ = v___x_1489_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
                    v___x_1500_ = v_reuseFailAlloc_1501_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_1500_;
            }
            50 => {
                return v___x_1509_;
            }
            51 => {
                v___x_1521_ = lean_ptr_addr(v_k_1515_);
                v___x_1522_ = lean_ptr_addr(v_a_1517_);
                v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
                if v___x_1523_ == 0 {
                    leanh::lean_inc(v_y_1514_);
                    leanh::lean_inc(v_i_1513_);
                    leanh::lean_inc(v_fvarId_1512_);
                    v_isSharedCheck_1533_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v_unused_1534_ = leanh::lean_ctor_get(v_c_1248_, 3);
                        leanh::lean_dec(v_unused_1534_);
                        v_unused_1535_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1535_);
                        v_unused_1536_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1536_);
                        v_unused_1537_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1537_);
                        v___x_1525_ = v_c_1248_;
                        v_isShared_1526_ = v_isSharedCheck_1533_;
                        state = 52;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1525_ = leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1533_;
                        state = 52;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1517_);
                    if v_isShared_1520_ == 0 {
                        leanh::lean_ctor_set(v___x_1519_, 0, v_c_1248_);
                        v___x_1539_ = v___x_1519_;
                        state = 55;
                        continue;
                    } else {
                        v_reuseFailAlloc_1540_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_c_1248_);
                        v___x_1539_ = v_reuseFailAlloc_1540_;
                        state = 55;
                        continue;
                    }
                }
            }
            52 => {
                if v_isShared_1526_ == 0 {
                    leanh::lean_ctor_set(v___x_1525_, 3, v_a_1517_);
                    v___x_1528_ = v___x_1525_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = leanh::lean_alloc_ctor(8, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_fvarId_1512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_i_1513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_y_1514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_a_1517_);
                    v___x_1528_ = v_reuseFailAlloc_1532_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_1520_ == 0 {
                    leanh::lean_ctor_set(v___x_1519_, 0, v___x_1528_);
                    v___x_1530_ = v___x_1519_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
                    v___x_1530_ = v_reuseFailAlloc_1531_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_1530_;
            }
            55 => {
                return v___x_1539_;
            }
            56 => {
                v___x_1553_ = lean_ptr_addr(v_k_1547_);
                v___x_1554_ = lean_ptr_addr(v_a_1549_);
                v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
                if v___x_1555_ == 0 {
                    leanh::lean_inc_ref(v_ty_1546_);
                    leanh::lean_inc(v_y_1545_);
                    leanh::lean_inc(v_offset_1544_);
                    leanh::lean_inc(v_i_1543_);
                    leanh::lean_inc(v_fvarId_1542_);
                    v_isSharedCheck_1565_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v_unused_1566_ = leanh::lean_ctor_get(v_c_1248_, 5);
                        leanh::lean_dec(v_unused_1566_);
                        v_unused_1567_ = leanh::lean_ctor_get(v_c_1248_, 4);
                        leanh::lean_dec(v_unused_1567_);
                        v_unused_1568_ = leanh::lean_ctor_get(v_c_1248_, 3);
                        leanh::lean_dec(v_unused_1568_);
                        v_unused_1569_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1569_);
                        v_unused_1570_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1570_);
                        v_unused_1571_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1571_);
                        v___x_1557_ = v_c_1248_;
                        v_isShared_1558_ = v_isSharedCheck_1565_;
                        state = 57;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1557_ = leanh::lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1565_;
                        state = 57;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1549_);
                    if v_isShared_1552_ == 0 {
                        leanh::lean_ctor_set(v___x_1551_, 0, v_c_1248_);
                        v___x_1573_ = v___x_1551_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_1574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_c_1248_);
                        v___x_1573_ = v_reuseFailAlloc_1574_;
                        state = 60;
                        continue;
                    }
                }
            }
            57 => {
                if v_isShared_1558_ == 0 {
                    leanh::lean_ctor_set(v___x_1557_, 5, v_a_1549_);
                    v___x_1560_ = v___x_1557_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = leanh::lean_alloc_ctor(9, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_fvarId_1542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_i_1543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_offset_1544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_y_1545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_ty_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 5, v_a_1549_);
                    v___x_1560_ = v_reuseFailAlloc_1564_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                if v_isShared_1552_ == 0 {
                    leanh::lean_ctor_set(v___x_1551_, 0, v___x_1560_);
                    v___x_1562_ = v___x_1551_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_1563_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
                    v___x_1562_ = v_reuseFailAlloc_1563_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_1562_;
            }
            60 => {
                return v___x_1573_;
            }
            61 => {
                v___x_1584_ = lean_ptr_addr(v_k_1578_);
                v___x_1585_ = lean_ptr_addr(v_a_1580_);
                v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
                if v___x_1586_ == 0 {
                    leanh::lean_inc(v_cidx_1577_);
                    leanh::lean_inc(v_fvarId_1576_);
                    v_isSharedCheck_1596_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1596_ == 0 {
                        v_unused_1597_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1597_);
                        v_unused_1598_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1598_);
                        v_unused_1599_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1599_);
                        v___x_1588_ = v_c_1248_;
                        v_isShared_1589_ = v_isSharedCheck_1596_;
                        state = 62;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1588_ = leanh::lean_box(0);
                        v_isShared_1589_ = v_isSharedCheck_1596_;
                        state = 62;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1580_);
                    if v_isShared_1583_ == 0 {
                        leanh::lean_ctor_set(v___x_1582_, 0, v_c_1248_);
                        v___x_1601_ = v___x_1582_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_c_1248_);
                        v___x_1601_ = v_reuseFailAlloc_1602_;
                        state = 65;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_1589_ == 0 {
                    leanh::lean_ctor_set(v___x_1588_, 2, v_a_1580_);
                    v___x_1591_ = v___x_1588_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(10, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_fvarId_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_cidx_1577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_a_1580_);
                    v___x_1591_ = v_reuseFailAlloc_1595_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_1583_ == 0 {
                    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1582_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_1593_;
            }
            65 => {
                return v___x_1601_;
            }
            66 => {
                v___x_1614_ = lean_ptr_addr(v_k_1608_);
                v___x_1615_ = lean_ptr_addr(v_a_1610_);
                v___x_1616_ = lean_usize_dec_eq(v___x_1614_, v___x_1615_);
                if v___x_1616_ == 0 {
                    leanh::lean_inc(v_n_1605_);
                    leanh::lean_inc(v_fvarId_1604_);
                    v_isSharedCheck_1626_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1626_ == 0 {
                        v_unused_1627_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1627_);
                        v_unused_1628_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1628_);
                        v_unused_1629_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1629_);
                        v___x_1618_ = v_c_1248_;
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 67;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1618_ = leanh::lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 67;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1610_);
                    if v_isShared_1613_ == 0 {
                        leanh::lean_ctor_set(v___x_1612_, 0, v_c_1248_);
                        v___x_1631_ = v___x_1612_;
                        state = 70;
                        continue;
                    } else {
                        v_reuseFailAlloc_1632_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_c_1248_);
                        v___x_1631_ = v_reuseFailAlloc_1632_;
                        state = 70;
                        continue;
                    }
                }
            }
            67 => {
                if v_isShared_1619_ == 0 {
                    leanh::lean_ctor_set(v___x_1618_, 2, v_a_1610_);
                    v___x_1621_ = v___x_1618_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = leanh::lean_alloc_ctor(11, 3, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_fvarId_1604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_n_1605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_a_1610_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1625_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_check_1606_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1625_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_persistent_1607_,
                    );
                    v___x_1621_ = v_reuseFailAlloc_1625_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_1613_ == 0 {
                    leanh::lean_ctor_set(v___x_1612_, 0, v___x_1621_);
                    v___x_1623_ = v___x_1612_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
                    v___x_1623_ = v_reuseFailAlloc_1624_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_1623_;
            }
            70 => {
                return v___x_1631_;
            }
            71 => {
                v___x_1645_ = lean_ptr_addr(v_k_1639_);
                v___x_1646_ = lean_ptr_addr(v_a_1641_);
                v___x_1647_ = lean_usize_dec_eq(v___x_1645_, v___x_1646_);
                if v___x_1647_ == 0 {
                    leanh::lean_inc(v_objs_x3f_1638_);
                    leanh::lean_inc(v_n_1635_);
                    leanh::lean_inc(v_fvarId_1634_);
                    v_isSharedCheck_1657_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v_unused_1658_ = leanh::lean_ctor_get(v_c_1248_, 3);
                        leanh::lean_dec(v_unused_1658_);
                        v_unused_1659_ = leanh::lean_ctor_get(v_c_1248_, 2);
                        leanh::lean_dec(v_unused_1659_);
                        v_unused_1660_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1660_);
                        v_unused_1661_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1661_);
                        v___x_1649_ = v_c_1248_;
                        v_isShared_1650_ = v_isSharedCheck_1657_;
                        state = 72;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1649_ = leanh::lean_box(0);
                        v_isShared_1650_ = v_isSharedCheck_1657_;
                        state = 72;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1641_);
                    if v_isShared_1644_ == 0 {
                        leanh::lean_ctor_set(v___x_1643_, 0, v_c_1248_);
                        v___x_1663_ = v___x_1643_;
                        state = 75;
                        continue;
                    } else {
                        v_reuseFailAlloc_1664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_c_1248_);
                        v___x_1663_ = v_reuseFailAlloc_1664_;
                        state = 75;
                        continue;
                    }
                }
            }
            72 => {
                if v_isShared_1650_ == 0 {
                    leanh::lean_ctor_set(v___x_1649_, 3, v_a_1641_);
                    v___x_1652_ = v___x_1649_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_1656_ = leanh::lean_alloc_ctor(12, 4, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_fvarId_1634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_n_1635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_objs_x3f_1638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_a_1641_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1656_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_check_1636_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1656_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                        v_persistent_1637_,
                    );
                    v___x_1652_ = v_reuseFailAlloc_1656_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                if v_isShared_1644_ == 0 {
                    leanh::lean_ctor_set(v___x_1643_, 0, v___x_1652_);
                    v___x_1654_ = v___x_1643_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_1655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
                    v___x_1654_ = v_reuseFailAlloc_1655_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_1654_;
            }
            75 => {
                return v___x_1663_;
            }
            76 => {
                v___x_1673_ = lean_ptr_addr(v_k_1667_);
                v___x_1674_ = lean_ptr_addr(v_a_1669_);
                v___x_1675_ = lean_usize_dec_eq(v___x_1673_, v___x_1674_);
                if v___x_1675_ == 0 {
                    leanh::lean_inc(v_fvarId_1666_);
                    v_isSharedCheck_1685_ = (!leanh::lean_is_exclusive(v_c_1248_)) as u8;
                    if v_isSharedCheck_1685_ == 0 {
                        v_unused_1686_ = leanh::lean_ctor_get(v_c_1248_, 1);
                        leanh::lean_dec(v_unused_1686_);
                        v_unused_1687_ = leanh::lean_ctor_get(v_c_1248_, 0);
                        leanh::lean_dec(v_unused_1687_);
                        v___x_1677_ = v_c_1248_;
                        v_isShared_1678_ = v_isSharedCheck_1685_;
                        state = 77;
                        continue;
                    } else {
                        leanh::lean_dec(v_c_1248_);
                        v___x_1677_ = leanh::lean_box(0);
                        v_isShared_1678_ = v_isSharedCheck_1685_;
                        state = 77;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1669_);
                    if v_isShared_1672_ == 0 {
                        leanh::lean_ctor_set(v___x_1671_, 0, v_c_1248_);
                        v___x_1689_ = v___x_1671_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_1690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_c_1248_);
                        v___x_1689_ = v_reuseFailAlloc_1690_;
                        state = 80;
                        continue;
                    }
                }
            }
            77 => {
                if v_isShared_1678_ == 0 {
                    leanh::lean_ctor_set(v___x_1677_, 1, v_a_1669_);
                    v___x_1680_ = v___x_1677_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = leanh::lean_alloc_ctor(13, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_fvarId_1666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_a_1669_);
                    v___x_1680_ = v_reuseFailAlloc_1684_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_1672_ == 0 {
                    leanh::lean_ctor_set(v___x_1671_, 0, v___x_1680_);
                    v___x_1682_ = v___x_1671_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
                    v___x_1682_ = v_reuseFailAlloc_1683_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_1682_;
            }
            80 => {
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(
    mut v_pu_1692_: u8,
    mut v_f_1693_: *mut leanh::LeanObject,
    mut v_sz_1694_: usize,
    mut v_i_1695_: usize,
    mut v_bs_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: usize = 0;
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v_info_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v_code_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1703_ = lean_usize_dec_lt(v_i_1695_, v_sz_1694_);
                if v___x_1703_ == 0 {
                    leanh::lean_dec_ref(v_f_1693_);
                    v___x_1704_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1704_, 0, v_bs_1696_);
                    return v___x_1704_;
                } else {
                    v_v_1705_ = lean_array_uget(v_bs_1696_, v_i_1695_);
                    v___x_1706_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1707_ = lean_array_uset(v_bs_1696_, v_i_1695_, v___x_1706_);
                    match leanh::lean_obj_tag(v_v_1705_) {
                        0 => {
                            v_ctorName_1714_ = leanh::lean_ctor_get(v_v_1705_, 0);
                            v_params_1715_ = leanh::lean_ctor_get(v_v_1705_, 1);
                            v_code_1716_ = leanh::lean_ctor_get(v_v_1705_, 2);
                            v_isSharedCheck_1733_ =
                                (!leanh::lean_is_exclusive(v_v_1705_)) as u8;
                            if v_isSharedCheck_1733_ == 0 {
                                v___x_1718_ = v_v_1705_;
                                v_isShared_1719_ = v_isSharedCheck_1733_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_code_1716_);
                                leanh::lean_inc(v_params_1715_);
                                leanh::lean_inc(v_ctorName_1714_);
                                leanh::lean_dec(v_v_1705_);
                                v___x_1718_ = leanh::lean_box(0);
                                v_isShared_1719_ = v_isSharedCheck_1733_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_info_1734_ = leanh::lean_ctor_get(v_v_1705_, 0);
                            v_code_1735_ = leanh::lean_ctor_get(v_v_1705_, 1);
                            v_isSharedCheck_1752_ =
                                (!leanh::lean_is_exclusive(v_v_1705_)) as u8;
                            if v_isSharedCheck_1752_ == 0 {
                                v___x_1737_ = v_v_1705_;
                                v_isShared_1738_ = v_isSharedCheck_1752_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_code_1735_);
                                leanh::lean_inc(v_info_1734_);
                                leanh::lean_dec(v_v_1705_);
                                v___x_1737_ = leanh::lean_box(0);
                                v_isShared_1738_ = v_isSharedCheck_1752_;
                                state = 6;
                                continue;
                            }
                        }
                        _ => {
                            v_code_1753_ = leanh::lean_ctor_get(v_v_1705_, 0);
                            v_isSharedCheck_1770_ =
                                (!leanh::lean_is_exclusive(v_v_1705_)) as u8;
                            if v_isSharedCheck_1770_ == 0 {
                                v___x_1755_ = v_v_1705_;
                                v_isShared_1756_ = v_isSharedCheck_1770_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_code_1753_);
                                leanh::lean_dec(v_v_1705_);
                                v___x_1755_ = leanh::lean_box(0);
                                v_isShared_1756_ = v_isSharedCheck_1770_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1710_ = 1usize;
                v___x_1711_ = lean_usize_add(v_i_1695_, v___x_1710_);
                v___x_1712_ = lean_array_uset(v_bs_x27_1707_, v_i_1695_, v_a_1709_);
                v_i_1695_ = v___x_1711_;
                v_bs_1696_ = v___x_1712_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc_ref(v_f_1693_);
                v___x_1720_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1692_,
                        v_f_1693_,
                        v_code_1716_,
                        v___y_1697_,
                        v___y_1698_,
                        v___y_1699_,
                        v___y_1700_,
                        v___y_1701_,
                    );
                if leanh::lean_obj_tag(v___x_1720_) == 0 {
                    v_a_1721_ = leanh::lean_ctor_get(v___x_1720_, 0);
                    leanh::lean_inc(v_a_1721_);
                    leanh::lean_dec_ref_known(v___x_1720_, 1);
                    if v_isShared_1719_ == 0 {
                        leanh::lean_ctor_set(v___x_1718_, 2, v_a_1721_);
                        v___x_1723_ = v___x_1718_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1724_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_ctorName_1714_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_params_1715_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_a_1721_);
                        v___x_1723_ = v_reuseFailAlloc_1724_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1718_);
                    leanh::lean_dec_ref(v_params_1715_);
                    leanh::lean_dec(v_ctorName_1714_);
                    leanh::lean_dec_ref(v_bs_x27_1707_);
                    leanh::lean_dec_ref(v_f_1693_);
                    v_a_1725_ = leanh::lean_ctor_get(v___x_1720_, 0);
                    v_isSharedCheck_1732_ = (!leanh::lean_is_exclusive(v___x_1720_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1727_ = v___x_1720_;
                        v_isShared_1728_ = v_isSharedCheck_1732_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1725_);
                        leanh::lean_dec(v___x_1720_);
                        v___x_1727_ = leanh::lean_box(0);
                        v_isShared_1728_ = v_isSharedCheck_1732_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1709_ = v___x_1723_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1728_ == 0 {
                    v___x_1730_ = v___x_1727_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1730_;
            }
            6 => {
                leanh::lean_inc_ref(v_f_1693_);
                v___x_1739_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1692_,
                        v_f_1693_,
                        v_code_1735_,
                        v___y_1697_,
                        v___y_1698_,
                        v___y_1699_,
                        v___y_1700_,
                        v___y_1701_,
                    );
                if leanh::lean_obj_tag(v___x_1739_) == 0 {
                    v_a_1740_ = leanh::lean_ctor_get(v___x_1739_, 0);
                    leanh::lean_inc(v_a_1740_);
                    leanh::lean_dec_ref_known(v___x_1739_, 1);
                    if v_isShared_1738_ == 0 {
                        leanh::lean_ctor_set(v___x_1737_, 1, v_a_1740_);
                        v___x_1742_ = v___x_1737_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1743_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_info_1734_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_a_1740_);
                        v___x_1742_ = v_reuseFailAlloc_1743_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1737_);
                    leanh::lean_dec_ref(v_info_1734_);
                    leanh::lean_dec_ref(v_bs_x27_1707_);
                    leanh::lean_dec_ref(v_f_1693_);
                    v_a_1744_ = leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1751_ = (!leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1746_ = v___x_1739_;
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1744_);
                        leanh::lean_dec(v___x_1739_);
                        v___x_1746_ = leanh::lean_box(0);
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v_a_1709_ = v___x_1742_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_1747_ == 0 {
                    v___x_1749_ = v___x_1746_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
                    v___x_1749_ = v_reuseFailAlloc_1750_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1749_;
            }
            10 => {
                leanh::lean_inc_ref(v_f_1693_);
                v___x_1757_ =
                    l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
                        v_pu_1692_,
                        v_f_1693_,
                        v_code_1753_,
                        v___y_1697_,
                        v___y_1698_,
                        v___y_1699_,
                        v___y_1700_,
                        v___y_1701_,
                    );
                if leanh::lean_obj_tag(v___x_1757_) == 0 {
                    v_a_1758_ = leanh::lean_ctor_get(v___x_1757_, 0);
                    leanh::lean_inc(v_a_1758_);
                    leanh::lean_dec_ref_known(v___x_1757_, 1);
                    if v_isShared_1756_ == 0 {
                        leanh::lean_ctor_set(v___x_1755_, 0, v_a_1758_);
                        v___x_1760_ = v___x_1755_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1761_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1758_);
                        v___x_1760_ = v_reuseFailAlloc_1761_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1755_);
                    leanh::lean_dec_ref(v_bs_x27_1707_);
                    leanh::lean_dec_ref(v_f_1693_);
                    v_a_1762_ = leanh::lean_ctor_get(v___x_1757_, 0);
                    v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v___x_1757_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1757_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1762_);
                        leanh::lean_dec(v___x_1757_);
                        v___x_1764_ = leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                v_a_1709_ = v___x_1760_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_1765_ == 0 {
                    v___x_1767_ = v___x_1764_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(
    mut v_pu_1771_: *mut leanh::LeanObject,
    mut v_f_1772_: *mut leanh::LeanObject,
    mut v_sz_1773_: *mut leanh::LeanObject,
    mut v_i_1774_: *mut leanh::LeanObject,
    mut v_bs_1775_: *mut leanh::LeanObject,
    mut v___y_1776_: *mut leanh::LeanObject,
    mut v___y_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1782_: u8 = 0;
    let mut v_sz_boxed_1783_: usize = 0;
    let mut v_i_boxed_1784_: usize = 0;
    let mut v_res_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1782_ = (leanh::lean_unbox(v_pu_1771_) as u8);
    v_sz_boxed_1783_ = leanh::lean_unbox_usize(v_sz_1773_);
    leanh::lean_dec(v_sz_1773_);
    v_i_boxed_1784_ = leanh::lean_unbox_usize(v_i_1774_);
    leanh::lean_dec(v_i_1774_);
    v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_boxed_1782_, v_f_1772_, v_sz_boxed_1783_, v_i_boxed_1784_, v_bs_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
    leanh::lean_dec(v___y_1780_);
    leanh::lean_dec_ref(v___y_1779_);
    leanh::lean_dec(v___y_1778_);
    leanh::lean_dec_ref(v___y_1777_);
    leanh::lean_dec(v___y_1776_);
    return v_res_1785_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(
    mut v_pu_1786_: *mut leanh::LeanObject,
    mut v_f_1787_: *mut leanh::LeanObject,
    mut v_c_1788_: *mut leanh::LeanObject,
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
    mut v_a_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1795_: u8 = 0;
    let mut v_res_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1795_ = (leanh::lean_unbox(v_pu_1786_) as u8);
    v_res_1796_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
        v_pu_boxed_1795_,
        v_f_1787_,
        v_c_1788_,
        v_a_1789_,
        v_a_1790_,
        v_a_1791_,
        v_a_1792_,
        v_a_1793_,
    );
    leanh::lean_dec(v_a_1793_);
    leanh::lean_dec_ref(v_a_1792_);
    leanh::lean_dec(v_a_1791_);
    leanh::lean_dec_ref(v_a_1790_);
    leanh::lean_dec(v_a_1789_);
    return v_res_1796_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(
    mut v_00_u03b2_1797_: *mut leanh::LeanObject,
    mut v_k_1798_: *mut leanh::LeanObject,
    mut v_t_1799_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1800_: u8 = 0;
    v___x_1800_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_1798_, v_t_1799_);
    return v___x_1800_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(
    mut v_00_u03b2_1801_: *mut leanh::LeanObject,
    mut v_k_1802_: *mut leanh::LeanObject,
    mut v_t_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1804_: u8 = 0;
    let mut v_r_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(v_00_u03b2_1801_, v_k_1802_, v_t_1803_);
    leanh::lean_dec(v_t_1803_);
    leanh::lean_dec(v_k_1802_);
    v_r_1805_ = leanh::lean_box((v_res_1804_) as usize);
    return v_r_1805_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_codeBind(
    mut v_pu_1806_: u8,
    mut v_c_1807_: *mut leanh::LeanObject,
    mut v_f_1808_: *mut leanh::LeanObject,
    mut v_a_1809_: *mut leanh::LeanObject,
    mut v_a_1810_: *mut leanh::LeanObject,
    mut v_a_1811_: *mut leanh::LeanObject,
    mut v_a_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = leanh::lean_box(1);
    v___x_1815_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(
        v_pu_1806_,
        v_f_1808_,
        v_c_1807_,
        v___x_1814_,
        v_a_1809_,
        v_a_1810_,
        v_a_1811_,
        v_a_1812_,
    );
    return v___x_1815_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(
    mut v_pu_1816_: *mut leanh::LeanObject,
    mut v_c_1817_: *mut leanh::LeanObject,
    mut v_f_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
    mut v_a_1823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1824_: u8 = 0;
    let mut v_res_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1824_ = (leanh::lean_unbox(v_pu_1816_) as u8);
    v_res_1825_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(
        v_pu_boxed_1824_,
        v_c_1817_,
        v_f_1818_,
        v_a_1819_,
        v_a_1820_,
        v_a_1821_,
        v_a_1822_,
    );
    leanh::lean_dec(v_a_1822_);
    leanh::lean_dec_ref(v_a_1821_);
    leanh::lean_dec(v_a_1820_);
    leanh::lean_dec_ref(v_a_1819_);
    return v_res_1825_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(
    mut v_f_1828_: *mut leanh::LeanObject,
    mut v_ctx_1829_: *mut leanh::LeanObject,
    mut v_fvarId_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = leanh::lean_apply_2(v_f_1828_, v_fvarId_1830_, v_ctx_1829_);
    return v___x_1831_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(
    mut v_inst_1832_: *mut leanh::LeanObject,
    mut v_pu_1833_: u8,
    mut v_c_1834_: *mut leanh::LeanObject,
    mut v_f_1835_: *mut leanh::LeanObject,
    mut v_ctx_1836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1837_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1837_, 0, v_f_1835_);
    leanh::lean_closure_set(v___f_1837_, 1, v_ctx_1836_);
    v___x_1838_ = leanh::lean_box((v_pu_1833_) as usize);
    v___x_1839_ = leanh::lean_apply_3(v_inst_1832_, v___x_1838_, v_c_1834_, v___f_1837_);
    return v___x_1839_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(
    mut v_inst_1840_: *mut leanh::LeanObject,
    mut v_pu_1841_: *mut leanh::LeanObject,
    mut v_c_1842_: *mut leanh::LeanObject,
    mut v_f_1843_: *mut leanh::LeanObject,
    mut v_ctx_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_21__boxed_1845_: u8 = 0;
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_21__boxed_1845_ = (leanh::lean_unbox(v_pu_1841_) as u8);
    v_res_1846_ = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(
        v_inst_1840_,
        v_pu_21__boxed_1845_,
        v_c_1842_,
        v_f_1843_,
        v_ctx_1844_,
    );
    return v_res_1846_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(
    mut v_inst_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1848_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1848_, 0, v_inst_1847_);
    return v___f_1848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(
    mut v_m_1849_: *mut leanh::LeanObject,
    mut v_00_u03c1_1850_: *mut leanh::LeanObject,
    mut v_inst_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1852_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1852_, 0, v_inst_1851_);
    return v___f_1852_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(
    mut v_f_1853_: *mut leanh::LeanObject,
    mut v_sref_1854_: *mut leanh::LeanObject,
    mut v_fvarId_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = leanh::lean_apply_2(v_f_1853_, v_fvarId_1855_, v_sref_1854_);
    return v___x_1856_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(
    mut v_inst_1857_: *mut leanh::LeanObject,
    mut v_pu_1858_: u8,
    mut v_c_1859_: *mut leanh::LeanObject,
    mut v_f_1860_: *mut leanh::LeanObject,
    mut v_sref_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1862_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1862_, 0, v_f_1860_);
    leanh::lean_closure_set(v___f_1862_, 1, v_sref_1861_);
    v___x_1863_ = leanh::lean_box((v_pu_1858_) as usize);
    v___x_1864_ = leanh::lean_apply_3(v_inst_1857_, v___x_1863_, v_c_1859_, v___f_1862_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(
    mut v_inst_1865_: *mut leanh::LeanObject,
    mut v_pu_1866_: *mut leanh::LeanObject,
    mut v_c_1867_: *mut leanh::LeanObject,
    mut v_f_1868_: *mut leanh::LeanObject,
    mut v_sref_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_23__boxed_1870_: u8 = 0;
    let mut v_res_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_23__boxed_1870_ = (leanh::lean_unbox(v_pu_1866_) as u8);
    v_res_1871_ = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(
        v_inst_1865_,
        v_pu_23__boxed_1870_,
        v_c_1867_,
        v_f_1868_,
        v_sref_1869_,
    );
    return v_res_1871_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(
    mut v_inst_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1873_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1873_, 0, v_inst_1872_);
    return v___f_1873_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(
    mut v_00_u03c9_1874_: *mut leanh::LeanObject,
    mut v_m_1875_: *mut leanh::LeanObject,
    mut v_00_u03c3_1876_: *mut leanh::LeanObject,
    mut v_inst_1877_: *mut leanh::LeanObject,
    mut v_inst_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1879_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1879_, 0, v_inst_1878_);
    return v___f_1879_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(
    mut v_pu_1882_: u8,
    mut v_type_1883_: *mut leanh::LeanObject,
    mut v_xs_1884_: *mut leanh::LeanObject,
    mut v_ps_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderType_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_type_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_x27_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_type_1883_) == 7 {
                    v_binderType_1891_ = leanh::lean_ctor_get(v_type_1883_, 1);
                    leanh::lean_inc_ref(v_binderType_1891_);
                    v_body_1892_ = leanh::lean_ctor_get(v_type_1883_, 2);
                    leanh::lean_inc_ref(v_body_1892_);
                    leanh::lean_dec_ref_known(v_type_1883_, 3);
                    v_d_1893_ = lean_expr_instantiate_rev(v_binderType_1891_, v_xs_1884_);
                    leanh::lean_dec_ref(v_binderType_1891_);
                    v___x_1894_ = l_Lean_isMarkedBorrowed(v_d_1893_);
                    v___x_1895_ = l_Lean_Compiler_LCNF_mkAuxParam(
                        v_pu_1882_,
                        v_d_1893_,
                        v___x_1894_,
                        v_a_1886_,
                        v_a_1887_,
                        v_a_1888_,
                        v_a_1889_,
                    );
                    if leanh::lean_obj_tag(v___x_1895_) == 0 {
                        v_a_1896_ = leanh::lean_ctor_get(v___x_1895_, 0);
                        leanh::lean_inc(v_a_1896_);
                        leanh::lean_dec_ref_known(v___x_1895_, 1);
                        v_fvarId_1897_ = leanh::lean_ctor_get(v_a_1896_, 0);
                        leanh::lean_inc(v_fvarId_1897_);
                        v___x_1898_ = l_Lean_Expr_fvar___override(v_fvarId_1897_);
                        v___x_1899_ = lean_array_push(v_xs_1884_, v___x_1898_);
                        v___x_1900_ = lean_array_push(v_ps_1885_, v_a_1896_);
                        v_type_1883_ = v_body_1892_;
                        v_xs_1884_ = v___x_1899_;
                        v_ps_1885_ = v___x_1900_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_body_1892_);
                        leanh::lean_dec_ref(v_ps_1885_);
                        leanh::lean_dec_ref(v_xs_1884_);
                        v_a_1902_ = leanh::lean_ctor_get(v___x_1895_, 0);
                        v_isSharedCheck_1909_ =
                            (!leanh::lean_is_exclusive(v___x_1895_)) as u8;
                        if v_isSharedCheck_1909_ == 0 {
                            v___x_1904_ = v___x_1895_;
                            v_isShared_1905_ = v_isSharedCheck_1909_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1902_);
                            leanh::lean_dec(v___x_1895_);
                            v___x_1904_ = leanh::lean_box(0);
                            v_isShared_1905_ = v_isSharedCheck_1909_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_type_1910_ = lean_expr_instantiate_rev(v_type_1883_, v_xs_1884_);
                    leanh::lean_dec_ref(v_xs_1884_);
                    leanh::lean_dec_ref(v_type_1883_);
                    leanh::lean_inc_ref(v_type_1910_);
                    v_type_x27_1911_ = l_Lean_Expr_headBeta(v_type_1910_);
                    v___x_1912_ = lean_expr_eqv(v_type_x27_1911_, v_type_1910_);
                    leanh::lean_dec_ref(v_type_1910_);
                    if v___x_1912_ == 0 {
                        v___x_1913_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0;
                        v_type_1883_ = v_type_x27_1911_;
                        v_xs_1884_ = v___x_1913_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_type_x27_1911_);
                        v___x_1915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1915_, 0, v_ps_1885_);
                        return v___x_1915_;
                    }
                }
            }
            1 => {
                if v_isShared_1905_ == 0 {
                    v___x_1907_ = v___x_1904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
                    v___x_1907_ = v_reuseFailAlloc_1908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(
    mut v_pu_1916_: *mut leanh::LeanObject,
    mut v_type_1917_: *mut leanh::LeanObject,
    mut v_xs_1918_: *mut leanh::LeanObject,
    mut v_ps_1919_: *mut leanh::LeanObject,
    mut v_a_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1925_: u8 = 0;
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1925_ = (leanh::lean_unbox(v_pu_1916_) as u8);
    v_res_1926_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(
        v_pu_boxed_1925_,
        v_type_1917_,
        v_xs_1918_,
        v_ps_1919_,
        v_a_1920_,
        v_a_1921_,
        v_a_1922_,
        v_a_1923_,
    );
    leanh::lean_dec(v_a_1923_);
    leanh::lean_dec_ref(v_a_1922_);
    leanh::lean_dec(v_a_1921_);
    leanh::lean_dec_ref(v_a_1920_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkNewParams(
    mut v_pu_1927_: u8,
    mut v_type_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_a_1931_: *mut leanh::LeanObject,
    mut v_a_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ =
        l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0;
    v___x_1935_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(
        v_pu_1927_,
        v_type_1928_,
        v___x_1934_,
        v___x_1934_,
        v_a_1929_,
        v_a_1930_,
        v_a_1931_,
        v_a_1932_,
    );
    return v___x_1935_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkNewParams___boxed(
    mut v_pu_1936_: *mut leanh::LeanObject,
    mut v_type_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_1943_: u8 = 0;
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_1943_ = (leanh::lean_unbox(v_pu_1936_) as u8);
    v_res_1944_ = l_Lean_Compiler_LCNF_mkNewParams(
        v_pu_boxed_1943_,
        v_type_1937_,
        v_a_1938_,
        v_a_1939_,
        v_a_1940_,
        v_a_1941_,
    );
    leanh::lean_dec(v_a_1941_);
    leanh::lean_dec_ref(v_a_1940_);
    leanh::lean_dec(v_a_1939_);
    leanh::lean_dec_ref(v_a_1938_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(
    mut v_type_1945_: *mut leanh::LeanObject,
    mut v_params_1946_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_typeArity_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueArity_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    v_typeArity_1947_ = l_Lean_Compiler_LCNF_getArrowArity(v_type_1945_);
    v_valueArity_1948_ = lean_array_get_size(v_params_1946_);
    v___x_1949_ = lean_nat_dec_lt(v_valueArity_1948_, v_typeArity_1947_);
    leanh::lean_dec(v_typeArity_1947_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(
    mut v_type_1950_: *mut leanh::LeanObject,
    mut v_params_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1952_: u8 = 0;
    let mut v_r_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_1950_, v_params_1951_);
    leanh::lean_dec_ref(v_params_1951_);
    v_r_1953_ = leanh::lean_box((v_res_1952_) as usize);
    return v_r_1953_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(
    mut v_decl_1954_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_params_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    v_params_1955_ = leanh::lean_ctor_get(v_decl_1954_, 2);
    leanh::lean_inc_ref(v_params_1955_);
    v_type_1956_ = leanh::lean_ctor_get(v_decl_1954_, 3);
    leanh::lean_inc_ref(v_type_1956_);
    leanh::lean_dec_ref(v_decl_1954_);
    v___x_1957_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_1956_, v_params_1955_);
    leanh::lean_dec_ref(v_params_1955_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(
    mut v_decl_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1959_: u8 = 0;
    let mut v_r_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(v_decl_1958_);
    v_r_1960_ = leanh::lean_box((v_res_1959_) as usize);
    return v_r_1960_;
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore___lam__0(
    mut v___x_1964_: *mut leanh::LeanObject,
    mut v___x_1965_: u8,
    mut v_fvarId_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_fvarId_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1985_: u8 = 0;
    let mut v_a_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1989_: u8 = 0;
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1972_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1972_, 0, v_fvarId_1966_);
                leanh::lean_ctor_set(v___x_1972_, 1, v___x_1964_);
                v___x_1973_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1;
                v___x_1974_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___x_1965_,
                    v___x_1972_,
                    v___x_1973_,
                    v___y_1967_,
                    v___y_1968_,
                    v___y_1969_,
                    v___y_1970_,
                );
                if leanh::lean_obj_tag(v___x_1974_) == 0 {
                    v_a_1975_ = leanh::lean_ctor_get(v___x_1974_, 0);
                    v_isSharedCheck_1985_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
                    if v_isSharedCheck_1985_ == 0 {
                        v___x_1977_ = v___x_1974_;
                        v_isShared_1978_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1975_);
                        leanh::lean_dec(v___x_1974_);
                        v___x_1977_ = leanh::lean_box(0);
                        v_isShared_1978_ = v_isSharedCheck_1985_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1986_ = leanh::lean_ctor_get(v___x_1974_, 0);
                    v_isSharedCheck_1993_ = (!leanh::lean_is_exclusive(v___x_1974_)) as u8;
                    if v_isSharedCheck_1993_ == 0 {
                        v___x_1988_ = v___x_1974_;
                        v_isShared_1989_ = v_isSharedCheck_1993_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1986_);
                        leanh::lean_dec(v___x_1974_);
                        v___x_1988_ = leanh::lean_box(0);
                        v_isShared_1989_ = v_isSharedCheck_1993_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fvarId_1979_ = leanh::lean_ctor_get(v_a_1975_, 0);
                leanh::lean_inc(v_fvarId_1979_);
                v___x_1980_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1980_, 0, v_fvarId_1979_);
                v___x_1981_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1981_, 0, v_a_1975_);
                leanh::lean_ctor_set(v___x_1981_, 1, v___x_1980_);
                if v_isShared_1978_ == 0 {
                    leanh::lean_ctor_set(v___x_1977_, 0, v___x_1981_);
                    v___x_1983_ = v___x_1977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1984_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
                    v___x_1983_ = v_reuseFailAlloc_1984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1983_;
            }
            3 => {
                if v_isShared_1989_ == 0 {
                    v___x_1991_ = v___x_1988_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1992_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
                    v___x_1991_ = v_reuseFailAlloc_1992_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(
    mut v___x_1994_: *mut leanh::LeanObject,
    mut v___x_1995_: *mut leanh::LeanObject,
    mut v_fvarId_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_903__boxed_2002_: u8 = 0;
    let mut v_res_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903__boxed_2002_ = (leanh::lean_unbox(v___x_1995_) as u8);
    v_res_2003_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(
        v___x_1994_,
        v___x_903__boxed_2002_,
        v_fvarId_1996_,
        v___y_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
    );
    leanh::lean_dec(v___y_2000_);
    leanh::lean_dec_ref(v___y_1999_);
    leanh::lean_dec(v___y_1998_);
    leanh::lean_dec_ref(v___y_1997_);
    return v_res_2003_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(
    mut v_sz_2004_: usize,
    mut v_i_2005_: usize,
    mut v_bs_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: u8 = 0;
    let mut v_v_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: usize = 0;
    let mut v___x_2014_: usize = 0;
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2007_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
                if v___x_2007_ == 0 {
                    return v_bs_2006_;
                } else {
                    v_v_2008_ = lean_array_uget_borrowed(v_bs_2006_, v_i_2005_);
                    v_fvarId_2009_ = leanh::lean_ctor_get(v_v_2008_, 0);
                    leanh::lean_inc(v_fvarId_2009_);
                    v___x_2010_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2011_ = lean_array_uset(v_bs_2006_, v_i_2005_, v___x_2010_);
                    v___x_2012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2012_, 0, v_fvarId_2009_);
                    v___x_2013_ = 1usize;
                    v___x_2014_ = lean_usize_add(v_i_2005_, v___x_2013_);
                    v___x_2015_ = lean_array_uset(v_bs_x27_2011_, v_i_2005_, v___x_2012_);
                    v_i_2005_ = v___x_2014_;
                    v_bs_2006_ = v___x_2015_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(
    mut v_sz_2017_: *mut leanh::LeanObject,
    mut v_i_2018_: *mut leanh::LeanObject,
    mut v_bs_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2020_: usize = 0;
    let mut v_i_boxed_2021_: usize = 0;
    let mut v_res_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2020_ = leanh::lean_unbox_usize(v_sz_2017_);
    leanh::lean_dec(v_sz_2017_);
    v_i_boxed_2021_ = leanh::lean_unbox_usize(v_i_2018_);
    leanh::lean_dec(v_i_2018_);
    v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_boxed_2020_, v_i_boxed_2021_, v_bs_2019_);
    return v_res_2022_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(
    mut v_sz_2023_: usize,
    mut v_i_2024_: usize,
    mut v_bs_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2026_: u8 = 0;
    let mut v_v_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: usize = 0;
    let mut v___x_2033_: usize = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2026_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
                if v___x_2026_ == 0 {
                    return v_bs_2025_;
                } else {
                    v_v_2027_ = lean_array_uget_borrowed(v_bs_2025_, v_i_2024_);
                    v_fvarId_2028_ = leanh::lean_ctor_get(v_v_2027_, 0);
                    leanh::lean_inc(v_fvarId_2028_);
                    v___x_2029_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2030_ = lean_array_uset(v_bs_2025_, v_i_2024_, v___x_2029_);
                    v___x_2031_ = l_Lean_mkFVar(v_fvarId_2028_);
                    v___x_2032_ = 1usize;
                    v___x_2033_ = lean_usize_add(v_i_2024_, v___x_2032_);
                    v___x_2034_ = lean_array_uset(v_bs_x27_2030_, v_i_2024_, v___x_2031_);
                    v_i_2024_ = v___x_2033_;
                    v_bs_2025_ = v___x_2034_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(
    mut v_sz_2036_: *mut leanh::LeanObject,
    mut v_i_2037_: *mut leanh::LeanObject,
    mut v_bs_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2039_: usize = 0;
    let mut v_i_boxed_2040_: usize = 0;
    let mut v_res_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2039_ = leanh::lean_unbox_usize(v_sz_2036_);
    leanh::lean_dec(v_sz_2036_);
    v_i_boxed_2040_ = leanh::lean_unbox_usize(v_i_2037_);
    leanh::lean_dec(v_i_2037_);
    v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_boxed_2039_, v_i_boxed_2040_, v_bs_2038_);
    return v_res_2041_;
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore(
    mut v_type_2042_: *mut leanh::LeanObject,
    mut v_params_2043_: *mut leanh::LeanObject,
    mut v_value_2044_: *mut leanh::LeanObject,
    mut v_a_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_a_2047_: *mut leanh::LeanObject,
    mut v_a_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_2050_: usize = 0;
    let mut v___x_2051_: usize = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2059_: usize = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_a_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_a_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_a_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2050_ = lean_array_size(v_params_2043_);
                v___x_2051_ = 0usize;
                leanh::lean_inc_ref(v_params_2043_);
                v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_2050_, v___x_2051_, v_params_2043_);
                v___x_2053_ = l_Lean_Compiler_LCNF_instantiateForall(
                    v_type_2042_,
                    v___x_2052_,
                    v_a_2047_,
                    v_a_2048_,
                );
                leanh::lean_dec_ref(v___x_2052_);
                if leanh::lean_obj_tag(v___x_2053_) == 0 {
                    v_a_2054_ = leanh::lean_ctor_get(v___x_2053_, 0);
                    leanh::lean_inc(v_a_2054_);
                    leanh::lean_dec_ref_known(v___x_2053_, 1);
                    v___x_2055_ = 0;
                    v___x_2056_ = l_Lean_Compiler_LCNF_mkNewParams(
                        v___x_2055_,
                        v_a_2054_,
                        v_a_2045_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                    );
                    if leanh::lean_obj_tag(v___x_2056_) == 0 {
                        v_a_2057_ = leanh::lean_ctor_get(v___x_2056_, 0);
                        leanh::lean_inc(v_a_2057_);
                        leanh::lean_dec_ref_known(v___x_2056_, 1);
                        v___x_2058_ = l_Array_append___redArg(v_params_2043_, v_a_2057_);
                        v_sz_2059_ = lean_array_size(v_a_2057_);
                        v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_2059_, v___x_2051_, v_a_2057_);
                        v___x_2061_ = leanh::lean_box((v___x_2055_) as usize);
                        v___f_2062_ = leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed
                                as *mut core::ffi::c_void,
                            8,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2062_, 0, v___x_2060_);
                        leanh::lean_closure_set(v___f_2062_, 1, v___x_2061_);
                        v___x_2063_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(
                            v___x_2055_,
                            v_value_2044_,
                            v___f_2062_,
                            v_a_2045_,
                            v_a_2046_,
                            v_a_2047_,
                            v_a_2048_,
                        );
                        if leanh::lean_obj_tag(v___x_2063_) == 0 {
                            v_a_2064_ = leanh::lean_ctor_get(v___x_2063_, 0);
                            v_isSharedCheck_2072_ =
                                (!leanh::lean_is_exclusive(v___x_2063_)) as u8;
                            if v_isSharedCheck_2072_ == 0 {
                                v___x_2066_ = v___x_2063_;
                                v_isShared_2067_ = v_isSharedCheck_2072_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2064_);
                                leanh::lean_dec(v___x_2063_);
                                v___x_2066_ = leanh::lean_box(0);
                                v_isShared_2067_ = v_isSharedCheck_2072_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2058_);
                            v_a_2073_ = leanh::lean_ctor_get(v___x_2063_, 0);
                            v_isSharedCheck_2080_ =
                                (!leanh::lean_is_exclusive(v___x_2063_)) as u8;
                            if v_isSharedCheck_2080_ == 0 {
                                v___x_2075_ = v___x_2063_;
                                v_isShared_2076_ = v_isSharedCheck_2080_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2073_);
                                leanh::lean_dec(v___x_2063_);
                                v___x_2075_ = leanh::lean_box(0);
                                v_isShared_2076_ = v_isSharedCheck_2080_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_value_2044_);
                        leanh::lean_dec_ref(v_params_2043_);
                        v_a_2081_ = leanh::lean_ctor_get(v___x_2056_, 0);
                        v_isSharedCheck_2088_ =
                            (!leanh::lean_is_exclusive(v___x_2056_)) as u8;
                        if v_isSharedCheck_2088_ == 0 {
                            v___x_2083_ = v___x_2056_;
                            v_isShared_2084_ = v_isSharedCheck_2088_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2081_);
                            leanh::lean_dec(v___x_2056_);
                            v___x_2083_ = leanh::lean_box(0);
                            v_isShared_2084_ = v_isSharedCheck_2088_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_value_2044_);
                    leanh::lean_dec_ref(v_params_2043_);
                    v_a_2089_ = leanh::lean_ctor_get(v___x_2053_, 0);
                    v_isSharedCheck_2096_ = (!leanh::lean_is_exclusive(v___x_2053_)) as u8;
                    if v_isSharedCheck_2096_ == 0 {
                        v___x_2091_ = v___x_2053_;
                        v_isShared_2092_ = v_isSharedCheck_2096_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2089_);
                        leanh::lean_dec(v___x_2053_);
                        v___x_2091_ = leanh::lean_box(0);
                        v_isShared_2092_ = v_isSharedCheck_2096_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2068_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2068_, 0, v___x_2058_);
                leanh::lean_ctor_set(v___x_2068_, 1, v_a_2064_);
                if v_isShared_2067_ == 0 {
                    leanh::lean_ctor_set(v___x_2066_, 0, v___x_2068_);
                    v___x_2070_ = v___x_2066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
                    v___x_2070_ = v_reuseFailAlloc_2071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2070_;
            }
            3 => {
                if v_isShared_2076_ == 0 {
                    v___x_2078_ = v___x_2075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
                    v___x_2078_ = v_reuseFailAlloc_2079_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2078_;
            }
            5 => {
                if v_isShared_2084_ == 0 {
                    v___x_2086_ = v___x_2083_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2086_;
            }
            7 => {
                if v_isShared_2092_ == 0 {
                    v___x_2094_ = v___x_2091_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore___boxed(
    mut v_type_2097_: *mut leanh::LeanObject,
    mut v_params_2098_: *mut leanh::LeanObject,
    mut v_value_2099_: *mut leanh::LeanObject,
    mut v_a_2100_: *mut leanh::LeanObject,
    mut v_a_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
    mut v_a_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2105_ = l_Lean_Compiler_LCNF_etaExpandCore(
        v_type_2097_,
        v_params_2098_,
        v_value_2099_,
        v_a_2100_,
        v_a_2101_,
        v_a_2102_,
        v_a_2103_,
    );
    leanh::lean_dec(v_a_2103_);
    leanh::lean_dec_ref(v_a_2102_);
    leanh::lean_dec(v_a_2101_);
    leanh::lean_dec_ref(v_a_2100_);
    return v_res_2105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore_x3f(
    mut v_type_2106_: *mut leanh::LeanObject,
    mut v_params_2107_: *mut leanh::LeanObject,
    mut v_value_2108_: *mut leanh::LeanObject,
    mut v_a_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
    mut v_a_2112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_a_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_2106_);
                v___x_2114_ =
                    l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_2106_, v_params_2107_);
                if v___x_2114_ == 0 {
                    leanh::lean_dec_ref(v_value_2108_);
                    leanh::lean_dec_ref(v_params_2107_);
                    leanh::lean_dec_ref(v_type_2106_);
                    v___x_2115_ = leanh::lean_box(0);
                    v___x_2116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2116_, 0, v___x_2115_);
                    return v___x_2116_;
                } else {
                    v___x_2117_ = l_Lean_Compiler_LCNF_etaExpandCore(
                        v_type_2106_,
                        v_params_2107_,
                        v_value_2108_,
                        v_a_2109_,
                        v_a_2110_,
                        v_a_2111_,
                        v_a_2112_,
                    );
                    if leanh::lean_obj_tag(v___x_2117_) == 0 {
                        v_a_2118_ = leanh::lean_ctor_get(v___x_2117_, 0);
                        v_isSharedCheck_2126_ =
                            (!leanh::lean_is_exclusive(v___x_2117_)) as u8;
                        if v_isSharedCheck_2126_ == 0 {
                            v___x_2120_ = v___x_2117_;
                            v_isShared_2121_ = v_isSharedCheck_2126_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2118_);
                            leanh::lean_dec(v___x_2117_);
                            v___x_2120_ = leanh::lean_box(0);
                            v_isShared_2121_ = v_isSharedCheck_2126_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2127_ = leanh::lean_ctor_get(v___x_2117_, 0);
                        v_isSharedCheck_2134_ =
                            (!leanh::lean_is_exclusive(v___x_2117_)) as u8;
                        if v_isSharedCheck_2134_ == 0 {
                            v___x_2129_ = v___x_2117_;
                            v_isShared_2130_ = v_isSharedCheck_2134_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2127_);
                            leanh::lean_dec(v___x_2117_);
                            v___x_2129_ = leanh::lean_box(0);
                            v_isShared_2130_ = v_isSharedCheck_2134_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2122_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2122_, 0, v_a_2118_);
                if v_isShared_2121_ == 0 {
                    leanh::lean_ctor_set(v___x_2120_, 0, v___x_2122_);
                    v___x_2124_ = v___x_2120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
                    v___x_2124_ = v_reuseFailAlloc_2125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2124_;
            }
            3 => {
                if v_isShared_2130_ == 0 {
                    v___x_2132_ = v___x_2129_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
                    v___x_2132_ = v_reuseFailAlloc_2133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(
    mut v_type_2135_: *mut leanh::LeanObject,
    mut v_params_2136_: *mut leanh::LeanObject,
    mut v_value_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
    mut v_a_2140_: *mut leanh::LeanObject,
    mut v_a_2141_: *mut leanh::LeanObject,
    mut v_a_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(
        v_type_2135_,
        v_params_2136_,
        v_value_2137_,
        v_a_2138_,
        v_a_2139_,
        v_a_2140_,
        v_a_2141_,
    );
    leanh::lean_dec(v_a_2141_);
    leanh::lean_dec_ref(v_a_2140_);
    leanh::lean_dec(v_a_2139_);
    leanh::lean_dec_ref(v_a_2138_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_etaExpand(
    mut v_decl_2144_: *mut leanh::LeanObject,
    mut v_a_2145_: *mut leanh::LeanObject,
    mut v_a_2146_: *mut leanh::LeanObject,
    mut v_a_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_params_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v_val_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_a_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_2150_ = leanh::lean_ctor_get(v_decl_2144_, 2);
                v_type_2151_ = leanh::lean_ctor_get(v_decl_2144_, 3);
                v_value_2152_ = leanh::lean_ctor_get(v_decl_2144_, 4);
                leanh::lean_inc_ref(v_value_2152_);
                leanh::lean_inc_ref(v_params_2150_);
                leanh::lean_inc_ref(v_type_2151_);
                v___x_2153_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(
                    v_type_2151_,
                    v_params_2150_,
                    v_value_2152_,
                    v_a_2145_,
                    v_a_2146_,
                    v_a_2147_,
                    v_a_2148_,
                );
                if leanh::lean_obj_tag(v___x_2153_) == 0 {
                    v_a_2154_ = leanh::lean_ctor_get(v___x_2153_, 0);
                    v_isSharedCheck_2166_ = (!leanh::lean_is_exclusive(v___x_2153_)) as u8;
                    if v_isSharedCheck_2166_ == 0 {
                        v___x_2156_ = v___x_2153_;
                        v_isShared_2157_ = v_isSharedCheck_2166_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2154_);
                        leanh::lean_dec(v___x_2153_);
                        v___x_2156_ = leanh::lean_box(0);
                        v_isShared_2157_ = v_isSharedCheck_2166_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decl_2144_);
                    v_a_2167_ = leanh::lean_ctor_get(v___x_2153_, 0);
                    v_isSharedCheck_2174_ = (!leanh::lean_is_exclusive(v___x_2153_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v___x_2169_ = v___x_2153_;
                        v_isShared_2170_ = v_isSharedCheck_2174_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2167_);
                        leanh::lean_dec(v___x_2153_);
                        v___x_2169_ = leanh::lean_box(0);
                        v_isShared_2170_ = v_isSharedCheck_2174_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2154_) == 1 {
                    leanh::lean_inc_ref(v_type_2151_);
                    leanh::lean_del_object(v___x_2156_);
                    v_val_2158_ = leanh::lean_ctor_get(v_a_2154_, 0);
                    leanh::lean_inc(v_val_2158_);
                    leanh::lean_dec_ref_known(v_a_2154_, 1);
                    v_fst_2159_ = leanh::lean_ctor_get(v_val_2158_, 0);
                    leanh::lean_inc(v_fst_2159_);
                    v_snd_2160_ = leanh::lean_ctor_get(v_val_2158_, 1);
                    leanh::lean_inc(v_snd_2160_);
                    leanh::lean_dec(v_val_2158_);
                    v___x_2161_ = 0;
                    v___x_2162_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2161_, v_decl_2144_, v_type_2151_, v_fst_2159_, v_snd_2160_, v_a_2146_);
                    return v___x_2162_;
                } else {
                    leanh::lean_dec(v_a_2154_);
                    if v_isShared_2157_ == 0 {
                        leanh::lean_ctor_set(v___x_2156_, 0, v_decl_2144_);
                        v___x_2164_ = v___x_2156_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2165_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_decl_2144_);
                        v___x_2164_ = v_reuseFailAlloc_2165_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2164_;
            }
            3 => {
                if v_isShared_2170_ == 0 {
                    v___x_2172_ = v___x_2169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
                    v___x_2172_ = v_reuseFailAlloc_2173_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(
    mut v_decl_2175_: *mut leanh::LeanObject,
    mut v_a_2176_: *mut leanh::LeanObject,
    mut v_a_2177_: *mut leanh::LeanObject,
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_a_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2181_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(
        v_decl_2175_,
        v_a_2176_,
        v_a_2177_,
        v_a_2178_,
        v_a_2179_,
    );
    leanh::lean_dec(v_a_2179_);
    leanh::lean_dec_ref(v_a_2178_);
    leanh::lean_dec(v_a_2177_);
    leanh::lean_dec_ref(v_a_2176_);
    return v_res_2181_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_etaExpand(
    mut v_decl_2182_: *mut leanh::LeanObject,
    mut v_a_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_2190_: u8 = 0;
    let mut v_inlineAttr_x3f_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v_name_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_2200_: u8 = 0;
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v_val_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_unused_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2234_: u8 = 0;
    let mut v_a_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_2188_ = leanh::lean_ctor_get(v_decl_2182_, 1);
                leanh::lean_inc_ref(v_value_2188_);
                if leanh::lean_obj_tag(v_value_2188_) == 0 {
                    v_toSignature_2189_ = leanh::lean_ctor_get(v_decl_2182_, 0);
                    leanh::lean_inc_ref(v_toSignature_2189_);
                    v_recursive_2190_ = leanh::lean_ctor_get_uint8(
                        v_decl_2182_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_2191_ = leanh::lean_ctor_get(v_decl_2182_, 2);
                    v_code_2192_ = leanh::lean_ctor_get(v_value_2188_, 0);
                    v_isSharedCheck_2244_ = (!leanh::lean_is_exclusive(v_value_2188_)) as u8;
                    if v_isSharedCheck_2244_ == 0 {
                        v___x_2194_ = v_value_2188_;
                        v_isShared_2195_ = v_isSharedCheck_2244_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_code_2192_);
                        leanh::lean_dec(v_value_2188_);
                        v___x_2194_ = leanh::lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2244_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_value_2188_, 1);
                    v___x_2245_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2245_, 0, v_decl_2182_);
                    return v___x_2245_;
                }
            }
            1 => {
                v_name_2196_ = leanh::lean_ctor_get(v_toSignature_2189_, 0);
                v_levelParams_2197_ = leanh::lean_ctor_get(v_toSignature_2189_, 1);
                v_type_2198_ = leanh::lean_ctor_get(v_toSignature_2189_, 2);
                v_params_2199_ = leanh::lean_ctor_get(v_toSignature_2189_, 3);
                v_safe_2200_ = leanh::lean_ctor_get_uint8(
                    v_toSignature_2189_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_2243_ =
                    (!leanh::lean_is_exclusive(v_toSignature_2189_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2202_ = v_toSignature_2189_;
                    v_isShared_2203_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_params_2199_);
                    leanh::lean_inc(v_type_2198_);
                    leanh::lean_inc(v_levelParams_2197_);
                    leanh::lean_inc(v_name_2196_);
                    leanh::lean_dec(v_toSignature_2189_);
                    v___x_2202_ = leanh::lean_box(0);
                    v_isShared_2203_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_type_2198_);
                v___x_2204_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(
                    v_type_2198_,
                    v_params_2199_,
                    v_code_2192_,
                    v_a_2183_,
                    v_a_2184_,
                    v_a_2185_,
                    v_a_2186_,
                );
                if leanh::lean_obj_tag(v___x_2204_) == 0 {
                    v_a_2205_ = leanh::lean_ctor_get(v___x_2204_, 0);
                    v_isSharedCheck_2234_ = (!leanh::lean_is_exclusive(v___x_2204_)) as u8;
                    if v_isSharedCheck_2234_ == 0 {
                        v___x_2207_ = v___x_2204_;
                        v_isShared_2208_ = v_isSharedCheck_2234_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2205_);
                        leanh::lean_dec(v___x_2204_);
                        v___x_2207_ = leanh::lean_box(0);
                        v_isShared_2208_ = v_isSharedCheck_2234_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2202_);
                    leanh::lean_dec_ref(v_type_2198_);
                    leanh::lean_dec(v_levelParams_2197_);
                    leanh::lean_dec(v_name_2196_);
                    leanh::lean_del_object(v___x_2194_);
                    leanh::lean_dec_ref(v_decl_2182_);
                    v_a_2235_ = leanh::lean_ctor_get(v___x_2204_, 0);
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2204_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2237_ = v___x_2204_;
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2235_);
                        leanh::lean_dec(v___x_2204_);
                        v___x_2237_ = leanh::lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2242_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2205_) == 1 {
                    leanh::lean_inc(v_inlineAttr_x3f_2191_);
                    v_isSharedCheck_2227_ = (!leanh::lean_is_exclusive(v_decl_2182_)) as u8;
                    if v_isSharedCheck_2227_ == 0 {
                        v_unused_2228_ = leanh::lean_ctor_get(v_decl_2182_, 2);
                        leanh::lean_dec(v_unused_2228_);
                        v_unused_2229_ = leanh::lean_ctor_get(v_decl_2182_, 1);
                        leanh::lean_dec(v_unused_2229_);
                        v_unused_2230_ = leanh::lean_ctor_get(v_decl_2182_, 0);
                        leanh::lean_dec(v_unused_2230_);
                        v___x_2210_ = v_decl_2182_;
                        v_isShared_2211_ = v_isSharedCheck_2227_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_decl_2182_);
                        v___x_2210_ = leanh::lean_box(0);
                        v_isShared_2211_ = v_isSharedCheck_2227_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2205_);
                    leanh::lean_del_object(v___x_2202_);
                    leanh::lean_dec_ref(v_type_2198_);
                    leanh::lean_dec(v_levelParams_2197_);
                    leanh::lean_dec(v_name_2196_);
                    leanh::lean_del_object(v___x_2194_);
                    if v_isShared_2208_ == 0 {
                        leanh::lean_ctor_set(v___x_2207_, 0, v_decl_2182_);
                        v___x_2232_ = v___x_2207_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_decl_2182_);
                        v___x_2232_ = v_reuseFailAlloc_2233_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_val_2212_ = leanh::lean_ctor_get(v_a_2205_, 0);
                leanh::lean_inc(v_val_2212_);
                leanh::lean_dec_ref_known(v_a_2205_, 1);
                v_fst_2213_ = leanh::lean_ctor_get(v_val_2212_, 0);
                leanh::lean_inc(v_fst_2213_);
                v_snd_2214_ = leanh::lean_ctor_get(v_val_2212_, 1);
                leanh::lean_inc(v_snd_2214_);
                leanh::lean_dec(v_val_2212_);
                if v_isShared_2203_ == 0 {
                    leanh::lean_ctor_set(v___x_2202_, 3, v_fst_2213_);
                    v___x_2216_ = v___x_2202_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_name_2196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_levelParams_2197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_type_2198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_fst_2213_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2226_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v_safe_2200_,
                    );
                    v___x_2216_ = v_reuseFailAlloc_2226_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2195_ == 0 {
                    leanh::lean_ctor_set(v___x_2194_, 0, v_snd_2214_);
                    v___x_2218_ = v___x_2194_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_snd_2214_);
                    v___x_2218_ = v_reuseFailAlloc_2225_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2211_ == 0 {
                    leanh::lean_ctor_set(v___x_2210_, 1, v___x_2218_);
                    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2216_);
                    v___x_2220_ = v___x_2210_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_inlineAttr_x3f_2191_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2224_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_recursive_2190_,
                    );
                    v___x_2220_ = v_reuseFailAlloc_2224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2208_ == 0 {
                    leanh::lean_ctor_set(v___x_2207_, 0, v___x_2220_);
                    v___x_2222_ = v___x_2207_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
                    v___x_2222_ = v_reuseFailAlloc_2223_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2222_;
            }
            9 => {
                return v___x_2232_;
            }
            10 => {
                if v_isShared_2238_ == 0 {
                    v___x_2240_ = v___x_2237_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(
    mut v_decl_2246_: *mut leanh::LeanObject,
    mut v_a_2247_: *mut leanh::LeanObject,
    mut v_a_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_Compiler_LCNF_Decl_etaExpand(
        v_decl_2246_,
        v_a_2247_,
        v_a_2248_,
        v_a_2249_,
        v_a_2250_,
    );
    leanh::lean_dec(v_a_2250_);
    leanh::lean_dec_ref(v_a_2249_);
    leanh::lean_dec(v_a_2248_);
    leanh::lean_dec_ref(v_a_2247_);
    return v_res_2252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Bind(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Bind(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Bind(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Bind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Bind(builtin);
}