// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Discharger
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.AppBuilder
use crate::r#gen::Lean::Expr::l_Lean_Expr_isTrue;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkOfEqTrueCore,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEq;
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_getConfig___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_lt};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Sym::Simp::SimpM::lean_sym_simp;
pub static l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value:
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
static mut l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [1 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(
    mut v_x_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_934_) == 0 {
        let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_935_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_935_;
    } else {
        let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_936_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_936_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(
    mut v_x_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(v_x_937_);
    crate::leanh::lean_dec_ref(v_x_937_);
    return v_res_938_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(
    mut v_t_939_: *mut crate::leanh::LeanObject,
    mut v_k_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_939_) == 0 {
        let mut v_contextDependent_941_: u8 = 0;
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_contextDependent_941_ = crate::leanh::lean_ctor_get_uint8(v_t_939_, 0 as u32);
        crate::leanh::lean_dec_ref_known(v_t_939_, 0);
        v___x_942_ = crate::leanh::lean_box((v_contextDependent_941_) as usize);
        v___x_943_ = crate::leanh::lean_apply_1(v_k_940_, v___x_942_);
        return v___x_943_;
    } else {
        let mut v_proof_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_contextDependent_945_: u8 = 0;
        let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_proof_944_ = crate::leanh::lean_ctor_get(v_t_939_, 0);
        crate::leanh::lean_inc_ref(v_proof_944_);
        v_contextDependent_945_ = crate::leanh::lean_ctor_get_uint8(
            v_t_939_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_t_939_, 1);
        v___x_946_ = crate::leanh::lean_box((v_contextDependent_945_) as usize);
        v___x_947_ = crate::leanh::lean_apply_2(v_k_940_, v_proof_944_, v___x_946_);
        return v___x_947_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(
    mut v_motive_948_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_949_: *mut crate::leanh::LeanObject,
    mut v_t_950_: *mut crate::leanh::LeanObject,
    mut v_h_951_: *mut crate::leanh::LeanObject,
    mut v_k_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_953_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_950_, v_k_952_);
    return v___x_953_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(
    mut v_motive_954_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_955_: *mut crate::leanh::LeanObject,
    mut v_t_956_: *mut crate::leanh::LeanObject,
    mut v_h_957_: *mut crate::leanh::LeanObject,
    mut v_k_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(
        v_motive_954_,
        v_ctorIdx_955_,
        v_t_956_,
        v_h_957_,
        v_k_958_,
    );
    crate::leanh::lean_dec(v_ctorIdx_955_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(
    mut v_t_960_: *mut crate::leanh::LeanObject,
    mut v_failed_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_960_, v_failed_961_);
    return v___x_962_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(
    mut v_motive_963_: *mut crate::leanh::LeanObject,
    mut v_t_964_: *mut crate::leanh::LeanObject,
    mut v_h_965_: *mut crate::leanh::LeanObject,
    mut v_failed_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_964_, v_failed_966_);
    return v___x_967_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(
    mut v_t_968_: *mut crate::leanh::LeanObject,
    mut v_solved_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_968_, v_solved_969_);
    return v___x_970_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(
    mut v_motive_971_: *mut crate::leanh::LeanObject,
    mut v_t_972_: *mut crate::leanh::LeanObject,
    mut v_h_973_: *mut crate::leanh::LeanObject,
    mut v_solved_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_975_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_972_, v_solved_974_);
    return v___x_975_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(
    mut v_e_976_: *mut crate::leanh::LeanObject,
    mut v_result_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_result_977_) == 0 {
        let mut v_contextDependent_978_: u8 = 0;
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_976_);
        v_contextDependent_978_ = crate::leanh::lean_ctor_get_uint8(v_result_977_, 1 as u32);
        crate::leanh::lean_dec_ref_known(v_result_977_, 0);
        v___x_979_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_979_, 0 as u32, v_contextDependent_978_);
        return v___x_979_;
    } else {
        let mut v_e_x27_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_contextDependent_982_: u8 = 0;
        let mut v___x_983_: u8 = 0;
        v_e_x27_980_ = crate::leanh::lean_ctor_get(v_result_977_, 0);
        crate::leanh::lean_inc_ref(v_e_x27_980_);
        v_proof_981_ = crate::leanh::lean_ctor_get(v_result_977_, 1);
        crate::leanh::lean_inc_ref(v_proof_981_);
        v_contextDependent_982_ = crate::leanh::lean_ctor_get_uint8(
            v_result_977_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_result_977_, 2);
        v___x_983_ = l_Lean_Expr_isTrue(v_e_x27_980_);
        if v___x_983_ == 0 {
            let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_proof_981_);
            crate::leanh::lean_dec_ref(v_e_976_);
            v___x_984_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
            crate::leanh::lean_ctor_set_uint8(v___x_984_, 0 as u32, v_contextDependent_982_);
            return v___x_984_;
        } else {
            let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_985_ = l_Lean_Meta_mkOfEqTrueCore(v_e_976_, v_proof_981_);
            v___x_986_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_985_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_986_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v_contextDependent_982_,
            );
            return v___x_986_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(
    mut v_p_987_: *mut crate::leanh::LeanObject,
    mut v_e_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
    mut v_a_990_: *mut crate::leanh::LeanObject,
    mut v_a_991_: *mut crate::leanh::LeanObject,
    mut v_a_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
    mut v_a_994_: *mut crate::leanh::LeanObject,
    mut v_a_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
    mut v_a_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1012_: u8 = 0;
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_997_);
                crate::leanh::lean_inc_ref(v_a_996_);
                crate::leanh::lean_inc(v_a_995_);
                crate::leanh::lean_inc_ref(v_a_994_);
                crate::leanh::lean_inc(v_a_993_);
                crate::leanh::lean_inc_ref(v_a_992_);
                crate::leanh::lean_inc(v_a_991_);
                crate::leanh::lean_inc_ref(v_a_990_);
                crate::leanh::lean_inc(v_a_989_);
                crate::leanh::lean_inc_ref(v_e_988_);
                v___x_999_ = crate::leanh::lean_apply_11(
                    v_p_987_,
                    v_e_988_,
                    v_a_989_,
                    v_a_990_,
                    v_a_991_,
                    v_a_992_,
                    v_a_993_,
                    v_a_994_,
                    v_a_995_,
                    v_a_996_,
                    v_a_997_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                    v_a_1000_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1008_ = (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_1002_ = v___x_999_;
                        v_isShared_1003_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1000_);
                        crate::leanh::lean_dec(v___x_999_);
                        v___x_1002_ = crate::leanh::lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_988_);
                    v_a_1009_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1016_ = (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1016_ == 0 {
                        v___x_1011_ = v___x_999_;
                        v_isShared_1012_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1009_);
                        crate::leanh::lean_dec(v___x_999_);
                        v___x_1011_ = crate::leanh::lean_box(0);
                        v_isShared_1012_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1004_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_988_, v_a_1000_);
                if v_isShared_1003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1006_;
            }
            3 => {
                if v_isShared_1012_ == 0 {
                    v___x_1014_ = v___x_1011_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
                    v___x_1014_ = v_reuseFailAlloc_1015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(
    mut v_p_1017_: *mut crate::leanh::LeanObject,
    mut v_e_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
    mut v_a_1026_: *mut crate::leanh::LeanObject,
    mut v_a_1027_: *mut crate::leanh::LeanObject,
    mut v_a_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(
        v_p_1017_, v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_,
        v_a_1025_, v_a_1026_, v_a_1027_,
    );
    crate::leanh::lean_dec(v_a_1027_);
    crate::leanh::lean_dec_ref(v_a_1026_);
    crate::leanh::lean_dec(v_a_1025_);
    crate::leanh::lean_dec_ref(v_a_1024_);
    crate::leanh::lean_dec(v_a_1023_);
    crate::leanh::lean_dec_ref(v_a_1022_);
    crate::leanh::lean_dec(v_a_1021_);
    crate::leanh::lean_dec_ref(v_a_1020_);
    crate::leanh::lean_dec(v_a_1019_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
    mut v_a_1030_: *mut crate::leanh::LeanObject,
    mut v_persistentCache_1031_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1032_: *mut crate::leanh::LeanObject,
    mut v_funext_1033_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v_unused_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_st_ref_take(v_a_1030_);
                v_numSteps_1037_ = crate::leanh::lean_ctor_get(v___x_1036_, 0);
                v_isSharedCheck_1047_ = (!crate::leanh::lean_is_exclusive(v___x_1036_)) as u8;
                if v_isSharedCheck_1047_ == 0 {
                    v_unused_1048_ = crate::leanh::lean_ctor_get(v___x_1036_, 3);
                    crate::leanh::lean_dec(v_unused_1048_);
                    v_unused_1049_ = crate::leanh::lean_ctor_get(v___x_1036_, 2);
                    crate::leanh::lean_dec(v_unused_1049_);
                    v_unused_1050_ = crate::leanh::lean_ctor_get(v___x_1036_, 1);
                    crate::leanh::lean_dec(v_unused_1050_);
                    v___x_1039_ = v___x_1036_;
                    v_isShared_1040_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numSteps_1037_);
                    crate::leanh::lean_dec(v___x_1036_);
                    v___x_1039_ = crate::leanh::lean_box(0);
                    v_isShared_1040_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1039_, 3, v_funext_1033_);
                    crate::leanh::lean_ctor_set(v___x_1039_, 2, v_transientCache_1032_);
                    crate::leanh::lean_ctor_set(v___x_1039_, 1, v_persistentCache_1031_);
                    v___x_1042_ = v___x_1039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_numSteps_1037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_persistentCache_1031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_transientCache_1032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_funext_1033_);
                    v___x_1042_ = v_reuseFailAlloc_1046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1043_ = lean_st_ref_set(v_a_1030_, v___x_1042_);
                v___x_1044_ = crate::leanh::lean_box(0);
                v___x_1045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1045_, 0, v___x_1044_);
                return v___x_1045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_persistentCache_1052_: *mut crate::leanh::LeanObject,
    mut v_transientCache_1053_: *mut crate::leanh::LeanObject,
    mut v_funext_1054_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
        v_a_1051_,
        v_persistentCache_1052_,
        v_transientCache_1053_,
        v_funext_1054_,
        v_a_x3f_1055_,
    );
    crate::leanh::lean_dec(v_a_x3f_1055_);
    crate::leanh::lean_dec(v_a_1051_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf(
    mut v_e_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_a_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v_maxDischargeDepth_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLCtxSize_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeDepth_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut v_unused_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_unused_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut v_a_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1071_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1062_);
                if crate::leanh::lean_obj_tag(v___x_1071_) == 0 {
                    v_a_1072_ = crate::leanh::lean_ctor_get(v___x_1071_, 0);
                    v_isSharedCheck_1124_ = (!crate::leanh::lean_is_exclusive(v___x_1071_)) as u8;
                    if v_isSharedCheck_1124_ == 0 {
                        v___x_1074_ = v___x_1071_;
                        v_isShared_1075_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1072_);
                        crate::leanh::lean_dec(v___x_1071_);
                        v___x_1074_ = crate::leanh::lean_box(0);
                        v_isShared_1075_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1060_);
                    v_a_1125_ = crate::leanh::lean_ctor_get(v___x_1071_, 0);
                    v_isSharedCheck_1132_ = (!crate::leanh::lean_is_exclusive(v___x_1071_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1127_ = v___x_1071_;
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1125_);
                        crate::leanh::lean_dec(v___x_1071_);
                        v___x_1127_ = crate::leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_maxDischargeDepth_1076_ = crate::leanh::lean_ctor_get(v_a_1072_, 1);
                crate::leanh::lean_inc(v_maxDischargeDepth_1076_);
                crate::leanh::lean_dec(v_a_1072_);
                v_config_1077_ = crate::leanh::lean_ctor_get(v_a_1062_, 0);
                v_initialLCtxSize_1078_ = crate::leanh::lean_ctor_get(v_a_1062_, 1);
                v_dischargeDepth_1079_ = crate::leanh::lean_ctor_get(v_a_1062_, 2);
                v___x_1080_ = lean_nat_dec_lt(v_maxDischargeDepth_1076_, v_dischargeDepth_1079_);
                crate::leanh::lean_dec(v_maxDischargeDepth_1076_);
                if v___x_1080_ == 0 {
                    crate::leanh::lean_del_object(v___x_1074_);
                    v___x_1081_ = lean_st_ref_get(v_a_1063_);
                    v___x_1082_ = lean_st_ref_get(v_a_1063_);
                    v___x_1083_ = lean_st_ref_get(v_a_1063_);
                    v_persistentCache_1084_ = crate::leanh::lean_ctor_get(v___x_1081_, 1);
                    crate::leanh::lean_inc_ref(v_persistentCache_1084_);
                    crate::leanh::lean_dec(v___x_1081_);
                    v_transientCache_1085_ = crate::leanh::lean_ctor_get(v___x_1082_, 2);
                    crate::leanh::lean_inc_ref(v_transientCache_1085_);
                    crate::leanh::lean_dec(v___x_1082_);
                    v_funext_1086_ = crate::leanh::lean_ctor_get(v___x_1083_, 3);
                    crate::leanh::lean_inc_ref(v_funext_1086_);
                    crate::leanh::lean_dec(v___x_1083_);
                    v___x_1087_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1088_ = lean_nat_add(v_dischargeDepth_1079_, v___x_1087_);
                    crate::leanh::lean_inc(v_initialLCtxSize_1078_);
                    crate::leanh::lean_inc_ref(v_config_1077_);
                    v___x_1089_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1089_, 0, v_config_1077_);
                    crate::leanh::lean_ctor_set(v___x_1089_, 1, v_initialLCtxSize_1078_);
                    crate::leanh::lean_ctor_set(v___x_1089_, 2, v___x_1088_);
                    crate::leanh::lean_inc(v_a_1069_);
                    crate::leanh::lean_inc_ref(v_a_1068_);
                    crate::leanh::lean_inc(v_a_1067_);
                    crate::leanh::lean_inc_ref(v_a_1066_);
                    crate::leanh::lean_inc(v_a_1065_);
                    crate::leanh::lean_inc_ref(v_a_1064_);
                    crate::leanh::lean_inc(v_a_1063_);
                    crate::leanh::lean_inc(v_a_1061_);
                    crate::leanh::lean_inc_ref(v_e_1060_);
                    v___x_1090_ = lean_sym_simp(
                        v_e_1060_,
                        v_a_1061_,
                        v___x_1089_,
                        v_a_1063_,
                        v_a_1064_,
                        v_a_1065_,
                        v_a_1066_,
                        v_a_1067_,
                        v_a_1068_,
                        v_a_1069_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                        v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        v_isSharedCheck_1108_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                        if v_isSharedCheck_1108_ == 0 {
                            v___x_1093_ = v___x_1090_;
                            v_isShared_1094_ = v_isSharedCheck_1108_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1091_);
                            crate::leanh::lean_dec(v___x_1090_);
                            v___x_1093_ = crate::leanh::lean_box(0);
                            v_isShared_1094_ = v_isSharedCheck_1108_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1060_);
                        v_a_1109_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        crate::leanh::lean_inc(v_a_1109_);
                        crate::leanh::lean_dec_ref_known(v___x_1090_, 1);
                        v___x_1110_ = crate::leanh::lean_box(0);
                        v___x_1111_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
                            v_a_1063_,
                            v_persistentCache_1084_,
                            v_transientCache_1085_,
                            v_funext_1086_,
                            v___x_1110_,
                        );
                        v_isSharedCheck_1118_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1111_)) as u8;
                        if v_isSharedCheck_1118_ == 0 {
                            v_unused_1119_ = crate::leanh::lean_ctor_get(v___x_1111_, 0);
                            crate::leanh::lean_dec(v_unused_1119_);
                            v___x_1113_ = v___x_1111_;
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1111_);
                            v___x_1113_ = crate::leanh::lean_box(0);
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1060_);
                    v___x_1120_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0;
                    if v_isShared_1075_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1120_);
                        v___x_1122_ = v___x_1074_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
                        v___x_1122_ = v_reuseFailAlloc_1123_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1095_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_1060_, v_a_1091_);
                crate::leanh::lean_inc_ref(v___x_1095_);
                if v_isShared_1094_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1093_, 1);
                    crate::leanh::lean_ctor_set(v___x_1093_, 0, v___x_1095_);
                    v___x_1097_ = v___x_1093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1095_);
                    v___x_1097_ = v_reuseFailAlloc_1107_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1098_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
                    v_a_1063_,
                    v_persistentCache_1084_,
                    v_transientCache_1085_,
                    v_funext_1086_,
                    v___x_1097_,
                );
                crate::leanh::lean_dec_ref(v___x_1097_);
                v_isSharedCheck_1105_ = (!crate::leanh::lean_is_exclusive(v___x_1098_)) as u8;
                if v_isSharedCheck_1105_ == 0 {
                    v_unused_1106_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
                    crate::leanh::lean_dec(v_unused_1106_);
                    v___x_1100_ = v___x_1098_;
                    v_isShared_1101_ = v_isSharedCheck_1105_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1098_);
                    v___x_1100_ = crate::leanh::lean_box(0);
                    v_isShared_1101_ = v_isSharedCheck_1105_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1095_);
                    v___x_1103_ = v___x_1100_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1095_);
                    v___x_1103_ = v_reuseFailAlloc_1104_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1103_;
            }
            6 => {
                if v_isShared_1114_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1113_, 1);
                    crate::leanh::lean_ctor_set(v___x_1113_, 0, v_a_1109_);
                    v___x_1116_ = v___x_1113_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1109_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1116_;
            }
            8 => {
                return v___x_1122_;
            }
            9 => {
                if v_isShared_1128_ == 0 {
                    v___x_1130_ = v___x_1127_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
                    v___x_1130_ = v_reuseFailAlloc_1131_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(
    mut v_e_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
    mut v_a_1137_: *mut crate::leanh::LeanObject,
    mut v_a_1138_: *mut crate::leanh::LeanObject,
    mut v_a_1139_: *mut crate::leanh::LeanObject,
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_a_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(
        v_e_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_,
        v_a_1141_, v_a_1142_,
    );
    crate::leanh::lean_dec(v_a_1142_);
    crate::leanh::lean_dec_ref(v_a_1141_);
    crate::leanh::lean_dec(v_a_1140_);
    crate::leanh::lean_dec_ref(v_a_1139_);
    crate::leanh::lean_dec(v_a_1138_);
    crate::leanh::lean_dec_ref(v_a_1137_);
    crate::leanh::lean_dec(v_a_1136_);
    crate::leanh::lean_dec_ref(v_a_1135_);
    crate::leanh::lean_dec(v_a_1134_);
    return v_res_1144_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___redArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0;
    v___x_1147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
    return v___x_1147_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(
    mut v_a_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
    return v_res_1149_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone(
    mut v_x_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
    return v___x_1161_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___boxed(
    mut v_x_1162_: *mut crate::leanh::LeanObject,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Lean_Meta_Sym_Simp_dischargeNone(
        v_x_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_,
        v_a_1170_, v_a_1171_,
    );
    crate::leanh::lean_dec(v_a_1171_);
    crate::leanh::lean_dec_ref(v_a_1170_);
    crate::leanh::lean_dec(v_a_1169_);
    crate::leanh::lean_dec_ref(v_a_1168_);
    crate::leanh::lean_dec(v_a_1167_);
    crate::leanh::lean_dec_ref(v_a_1166_);
    crate::leanh::lean_dec(v_a_1165_);
    crate::leanh::lean_dec_ref(v_a_1164_);
    crate::leanh::lean_dec(v_a_1163_);
    crate::leanh::lean_dec_ref(v_x_1162_);
    return v_res_1173_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(
    mut v_e_1177_: *mut crate::leanh::LeanObject,
    mut v_as_1178_: *mut crate::leanh::LeanObject,
    mut v_sz_1179_: usize,
    mut v_i_1180_: usize,
    mut v_b_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v_reuseFailAlloc_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u8 = 0;
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v_a_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_unused_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1187_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
                if v___x_1187_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1177_);
                    v___x_1188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1188_, 0, v_b_1181_);
                    return v___x_1188_;
                } else {
                    v_snd_1189_ = crate::leanh::lean_ctor_get(v_b_1181_, 1);
                    v_isSharedCheck_1239_ = (!crate::leanh::lean_is_exclusive(v_b_1181_)) as u8;
                    if v_isSharedCheck_1239_ == 0 {
                        v_unused_1240_ = crate::leanh::lean_ctor_get(v_b_1181_, 0);
                        crate::leanh::lean_dec(v_unused_1240_);
                        v___x_1191_ = v_b_1181_;
                        v_isShared_1192_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1189_);
                        crate::leanh::lean_dec(v_b_1181_);
                        v___x_1191_ = crate::leanh::lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1193_ = crate::leanh::lean_box(0);
                v_a_1202_ = lean_array_uget(v_as_1178_, v_i_1180_);
                if crate::leanh::lean_obj_tag(v_a_1202_) == 0 {
                    v_a_1195_ = v_snd_1189_;
                    state = 2;
                    continue;
                } else {
                    v_val_1203_ = crate::leanh::lean_ctor_get(v_a_1202_, 0);
                    v_isSharedCheck_1238_ = (!crate::leanh::lean_is_exclusive(v_a_1202_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1205_ = v_a_1202_;
                        v_isShared_1206_ = v_isSharedCheck_1238_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1203_);
                        crate::leanh::lean_dec(v_a_1202_);
                        v___x_1205_ = crate::leanh::lean_box(0);
                        v_isShared_1206_ = v_isSharedCheck_1238_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1191_, 1, v_a_1195_);
                    crate::leanh::lean_ctor_set(v___x_1191_, 0, v___x_1193_);
                    v___x_1197_ = v___x_1191_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_a_1195_);
                    v___x_1197_ = v_reuseFailAlloc_1201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1198_ = 1usize;
                v___x_1199_ = lean_usize_add(v_i_1180_, v___x_1198_);
                v_i_1180_ = v___x_1199_;
                v_b_1181_ = v___x_1197_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1207_ = crate::leanh::lean_box(0);
                v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0;
                v___x_1209_ = l_Lean_LocalDecl_isAuxDecl(v_val_1203_);
                if v___x_1209_ == 0 {
                    v___x_1210_ = l_Lean_LocalDecl_type(v_val_1203_);
                    crate::leanh::lean_inc_ref(v_e_1177_);
                    v___x_1211_ = l_Lean_Meta_isExprDefEq(
                        v___x_1210_,
                        v_e_1177_,
                        v___y_1182_,
                        v___y_1183_,
                        v___y_1184_,
                        v___y_1185_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1211_) == 0 {
                        v_a_1212_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                        v_isSharedCheck_1229_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1211_)) as u8;
                        if v_isSharedCheck_1229_ == 0 {
                            v___x_1214_ = v___x_1211_;
                            v_isShared_1215_ = v_isSharedCheck_1229_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1212_);
                            crate::leanh::lean_dec(v___x_1211_);
                            v___x_1214_ = crate::leanh::lean_box(0);
                            v_isShared_1215_ = v_isSharedCheck_1229_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1205_);
                        crate::leanh::lean_dec(v_val_1203_);
                        crate::leanh::lean_del_object(v___x_1191_);
                        crate::leanh::lean_dec(v_snd_1189_);
                        crate::leanh::lean_dec_ref(v_e_1177_);
                        v_a_1230_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                        v_isSharedCheck_1237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1211_)) as u8;
                        if v_isSharedCheck_1237_ == 0 {
                            v___x_1232_ = v___x_1211_;
                            v_isShared_1233_ = v_isSharedCheck_1237_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1230_);
                            crate::leanh::lean_dec(v___x_1211_);
                            v___x_1232_ = crate::leanh::lean_box(0);
                            v_isShared_1233_ = v_isSharedCheck_1237_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1205_);
                    crate::leanh::lean_dec(v_val_1203_);
                    crate::leanh::lean_dec(v_snd_1189_);
                    v_a_1195_ = v___x_1208_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1216_ = (crate::leanh::lean_unbox(v_a_1212_) as u8);
                if v___x_1216_ == 0 {
                    crate::leanh::lean_del_object(v___x_1214_);
                    crate::leanh::lean_dec(v_a_1212_);
                    crate::leanh::lean_del_object(v___x_1205_);
                    crate::leanh::lean_dec(v_val_1203_);
                    crate::leanh::lean_dec(v_snd_1189_);
                    v_a_1195_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1191_);
                    crate::leanh::lean_dec_ref(v_e_1177_);
                    v___x_1217_ = l_Lean_LocalDecl_toExpr(v_val_1203_);
                    v___x_1218_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1218_, 0, v___x_1217_);
                    v___x_1219_ = (crate::leanh::lean_unbox(v_a_1212_) as u8);
                    crate::leanh::lean_dec(v_a_1212_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1218_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1219_,
                    );
                    if v_isShared_1206_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1205_, 0, v___x_1218_);
                        v___x_1221_ = v___x_1205_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1218_);
                        v___x_1221_ = v_reuseFailAlloc_1228_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1222_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1222_, 0, v___x_1221_);
                crate::leanh::lean_ctor_set(v___x_1222_, 1, v___x_1207_);
                v___x_1223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
                v___x_1224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                crate::leanh::lean_ctor_set(v___x_1224_, 1, v_snd_1189_);
                if v_isShared_1215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1224_);
                    v___x_1226_ = v___x_1214_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
                    v___x_1226_ = v_reuseFailAlloc_1227_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1226_;
            }
            8 => {
                if v_isShared_1233_ == 0 {
                    v___x_1235_ = v___x_1232_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
                    v___x_1235_ = v_reuseFailAlloc_1236_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_e_1241_: *mut crate::leanh::LeanObject,
    mut v_as_1242_: *mut crate::leanh::LeanObject,
    mut v_sz_1243_: *mut crate::leanh::LeanObject,
    mut v_i_1244_: *mut crate::leanh::LeanObject,
    mut v_b_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1251_: usize = 0;
    let mut v_i_boxed_1252_: usize = 0;
    let mut v_res_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1251_ = crate::leanh::lean_unbox_usize(v_sz_1243_);
    crate::leanh::lean_dec(v_sz_1243_);
    v_i_boxed_1252_ = crate::leanh::lean_unbox_usize(v_i_1244_);
    crate::leanh::lean_dec(v_i_1244_);
    v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_1241_, v_as_1242_, v_sz_boxed_1251_, v_i_boxed_1252_, v_b_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
    crate::leanh::lean_dec(v___y_1249_);
    crate::leanh::lean_dec_ref(v___y_1248_);
    crate::leanh::lean_dec(v___y_1247_);
    crate::leanh::lean_dec_ref(v___y_1246_);
    crate::leanh::lean_dec_ref(v_as_1242_);
    return v_res_1253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(
    mut v_e_1254_: *mut crate::leanh::LeanObject,
    mut v_as_1255_: *mut crate::leanh::LeanObject,
    mut v_sz_1256_: usize,
    mut v_i_1257_: usize,
    mut v_b_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v___y_1264_: *mut crate::leanh::LeanObject,
    mut v___y_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: u8 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut v_a_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_unused_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
                if v___x_1269_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1254_);
                    v___x_1270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1270_, 0, v_b_1258_);
                    return v___x_1270_;
                } else {
                    v_snd_1271_ = crate::leanh::lean_ctor_get(v_b_1258_, 1);
                    v_isSharedCheck_1321_ = (!crate::leanh::lean_is_exclusive(v_b_1258_)) as u8;
                    if v_isSharedCheck_1321_ == 0 {
                        v_unused_1322_ = crate::leanh::lean_ctor_get(v_b_1258_, 0);
                        crate::leanh::lean_dec(v_unused_1322_);
                        v___x_1273_ = v_b_1258_;
                        v_isShared_1274_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1271_);
                        crate::leanh::lean_dec(v_b_1258_);
                        v___x_1273_ = crate::leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1275_ = crate::leanh::lean_box(0);
                v_a_1284_ = lean_array_uget(v_as_1255_, v_i_1257_);
                if crate::leanh::lean_obj_tag(v_a_1284_) == 0 {
                    v_a_1277_ = v_snd_1271_;
                    state = 2;
                    continue;
                } else {
                    v_val_1285_ = crate::leanh::lean_ctor_get(v_a_1284_, 0);
                    v_isSharedCheck_1320_ = (!crate::leanh::lean_is_exclusive(v_a_1284_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1287_ = v_a_1284_;
                        v_isShared_1288_ = v_isSharedCheck_1320_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1285_);
                        crate::leanh::lean_dec(v_a_1284_);
                        v___x_1287_ = crate::leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1320_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1273_, 1, v_a_1277_);
                    crate::leanh::lean_ctor_set(v___x_1273_, 0, v___x_1275_);
                    v___x_1279_ = v___x_1273_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
                    v___x_1279_ = v_reuseFailAlloc_1283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1280_ = 1usize;
                v___x_1281_ = lean_usize_add(v_i_1257_, v___x_1280_);
                v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_1254_, v_as_1255_, v_sz_1256_, v___x_1281_, v___x_1279_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
                return v___x_1282_;
            }
            4 => {
                v___x_1289_ = crate::leanh::lean_box(0);
                v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0;
                v___x_1291_ = l_Lean_LocalDecl_isAuxDecl(v_val_1285_);
                if v___x_1291_ == 0 {
                    v___x_1292_ = l_Lean_LocalDecl_type(v_val_1285_);
                    crate::leanh::lean_inc_ref(v_e_1254_);
                    v___x_1293_ = l_Lean_Meta_isExprDefEq(
                        v___x_1292_,
                        v_e_1254_,
                        v___y_1264_,
                        v___y_1265_,
                        v___y_1266_,
                        v___y_1267_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1293_) == 0 {
                        v_a_1294_ = crate::leanh::lean_ctor_get(v___x_1293_, 0);
                        v_isSharedCheck_1311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1293_)) as u8;
                        if v_isSharedCheck_1311_ == 0 {
                            v___x_1296_ = v___x_1293_;
                            v_isShared_1297_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1294_);
                            crate::leanh::lean_dec(v___x_1293_);
                            v___x_1296_ = crate::leanh::lean_box(0);
                            v_isShared_1297_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1287_);
                        crate::leanh::lean_dec(v_val_1285_);
                        crate::leanh::lean_del_object(v___x_1273_);
                        crate::leanh::lean_dec(v_snd_1271_);
                        crate::leanh::lean_dec_ref(v_e_1254_);
                        v_a_1312_ = crate::leanh::lean_ctor_get(v___x_1293_, 0);
                        v_isSharedCheck_1319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1293_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1314_ = v___x_1293_;
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1312_);
                            crate::leanh::lean_dec(v___x_1293_);
                            v___x_1314_ = crate::leanh::lean_box(0);
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1287_);
                    crate::leanh::lean_dec(v_val_1285_);
                    crate::leanh::lean_dec(v_snd_1271_);
                    v_a_1277_ = v___x_1290_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1298_ = (crate::leanh::lean_unbox(v_a_1294_) as u8);
                if v___x_1298_ == 0 {
                    crate::leanh::lean_del_object(v___x_1296_);
                    crate::leanh::lean_dec(v_a_1294_);
                    crate::leanh::lean_del_object(v___x_1287_);
                    crate::leanh::lean_dec(v_val_1285_);
                    crate::leanh::lean_dec(v_snd_1271_);
                    v_a_1277_ = v___x_1290_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1273_);
                    crate::leanh::lean_dec_ref(v_e_1254_);
                    v___x_1299_ = l_Lean_LocalDecl_toExpr(v_val_1285_);
                    v___x_1300_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1299_);
                    v___x_1301_ = (crate::leanh::lean_unbox(v_a_1294_) as u8);
                    crate::leanh::lean_dec(v_a_1294_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1300_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1301_,
                    );
                    if v_isShared_1288_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1300_);
                        v___x_1303_ = v___x_1287_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1300_);
                        v___x_1303_ = v_reuseFailAlloc_1310_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1303_);
                crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1289_);
                v___x_1305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
                v___x_1306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                crate::leanh::lean_ctor_set(v___x_1306_, 1, v_snd_1271_);
                if v_isShared_1297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1306_);
                    v___x_1308_ = v___x_1296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
                    v___x_1308_ = v_reuseFailAlloc_1309_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1308_;
            }
            8 => {
                if v_isShared_1315_ == 0 {
                    v___x_1317_ = v___x_1314_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
                    v___x_1317_ = v_reuseFailAlloc_1318_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(
    mut v_e_1323_: *mut crate::leanh::LeanObject,
    mut v_as_1324_: *mut crate::leanh::LeanObject,
    mut v_sz_1325_: *mut crate::leanh::LeanObject,
    mut v_i_1326_: *mut crate::leanh::LeanObject,
    mut v_b_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1338_: usize = 0;
    let mut v_i_boxed_1339_: usize = 0;
    let mut v_res_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1338_ = crate::leanh::lean_unbox_usize(v_sz_1325_);
    crate::leanh::lean_dec(v_sz_1325_);
    v_i_boxed_1339_ = crate::leanh::lean_unbox_usize(v_i_1326_);
    crate::leanh::lean_dec(v_i_1326_);
    v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_1323_, v_as_1324_, v_sz_boxed_1338_, v_i_boxed_1339_, v_b_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    crate::leanh::lean_dec(v___y_1336_);
    crate::leanh::lean_dec_ref(v___y_1335_);
    crate::leanh::lean_dec(v___y_1334_);
    crate::leanh::lean_dec_ref(v___y_1333_);
    crate::leanh::lean_dec(v___y_1332_);
    crate::leanh::lean_dec_ref(v___y_1331_);
    crate::leanh::lean_dec(v___y_1330_);
    crate::leanh::lean_dec_ref(v___y_1329_);
    crate::leanh::lean_dec(v___y_1328_);
    crate::leanh::lean_dec_ref(v_as_1324_);
    return v_res_1340_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_e_1344_: *mut crate::leanh::LeanObject,
    mut v_as_1345_: *mut crate::leanh::LeanObject,
    mut v_sz_1346_: usize,
    mut v_i_1347_: usize,
    mut v_b_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: usize = 0;
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_a_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_unused_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
                if v___x_1354_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1344_);
                    v___x_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1355_, 0, v_b_1348_);
                    return v___x_1355_;
                } else {
                    v_snd_1356_ = crate::leanh::lean_ctor_get(v_b_1348_, 1);
                    v_isSharedCheck_1407_ = (!crate::leanh::lean_is_exclusive(v_b_1348_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v_unused_1408_ = crate::leanh::lean_ctor_get(v_b_1348_, 0);
                        crate::leanh::lean_dec(v_unused_1408_);
                        v___x_1358_ = v_b_1348_;
                        v_isShared_1359_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1356_);
                        crate::leanh::lean_dec(v_b_1348_);
                        v___x_1358_ = crate::leanh::lean_box(0);
                        v_isShared_1359_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1360_ = crate::leanh::lean_box(0);
                v_a_1369_ = lean_array_uget(v_as_1345_, v_i_1347_);
                if crate::leanh::lean_obj_tag(v_a_1369_) == 0 {
                    v_a_1362_ = v_snd_1356_;
                    state = 2;
                    continue;
                } else {
                    v_val_1370_ = crate::leanh::lean_ctor_get(v_a_1369_, 0);
                    v_isSharedCheck_1406_ = (!crate::leanh::lean_is_exclusive(v_a_1369_)) as u8;
                    if v_isSharedCheck_1406_ == 0 {
                        v___x_1372_ = v_a_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1370_);
                        crate::leanh::lean_dec(v_a_1369_);
                        v___x_1372_ = crate::leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1358_, 1, v_a_1362_);
                    crate::leanh::lean_ctor_set(v___x_1358_, 0, v___x_1360_);
                    v___x_1364_ = v___x_1358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1362_);
                    v___x_1364_ = v_reuseFailAlloc_1368_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1365_ = 1usize;
                v___x_1366_ = lean_usize_add(v_i_1347_, v___x_1365_);
                v_i_1347_ = v___x_1366_;
                v_b_1348_ = v___x_1364_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1374_ = crate::leanh::lean_box(0);
                v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
                v___x_1376_ = l_Lean_LocalDecl_isAuxDecl(v_val_1370_);
                if v___x_1376_ == 0 {
                    v___x_1377_ = l_Lean_LocalDecl_type(v_val_1370_);
                    crate::leanh::lean_inc_ref(v_e_1344_);
                    v___x_1378_ = l_Lean_Meta_isExprDefEq(
                        v___x_1377_,
                        v_e_1344_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                        v___y_1352_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1378_) == 0 {
                        v_a_1379_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                        v_isSharedCheck_1397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1378_)) as u8;
                        if v_isSharedCheck_1397_ == 0 {
                            v___x_1381_ = v___x_1378_;
                            v_isShared_1382_ = v_isSharedCheck_1397_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1379_);
                            crate::leanh::lean_dec(v___x_1378_);
                            v___x_1381_ = crate::leanh::lean_box(0);
                            v_isShared_1382_ = v_isSharedCheck_1397_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1372_);
                        crate::leanh::lean_dec(v_val_1370_);
                        crate::leanh::lean_del_object(v___x_1358_);
                        crate::leanh::lean_dec(v_snd_1356_);
                        crate::leanh::lean_dec_ref(v_e_1344_);
                        v_a_1398_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                        v_isSharedCheck_1405_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1378_)) as u8;
                        if v_isSharedCheck_1405_ == 0 {
                            v___x_1400_ = v___x_1378_;
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1398_);
                            crate::leanh::lean_dec(v___x_1378_);
                            v___x_1400_ = crate::leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1372_);
                    crate::leanh::lean_dec(v_val_1370_);
                    crate::leanh::lean_dec(v_snd_1356_);
                    v_a_1362_ = v___x_1375_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1383_ = (crate::leanh::lean_unbox(v_a_1379_) as u8);
                if v___x_1383_ == 0 {
                    crate::leanh::lean_del_object(v___x_1381_);
                    crate::leanh::lean_dec(v_a_1379_);
                    crate::leanh::lean_del_object(v___x_1372_);
                    crate::leanh::lean_dec(v_val_1370_);
                    crate::leanh::lean_dec(v_snd_1356_);
                    v_a_1362_ = v___x_1375_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1358_);
                    crate::leanh::lean_dec_ref(v_e_1344_);
                    v___x_1384_ = l_Lean_LocalDecl_toExpr(v_val_1370_);
                    v___x_1385_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                    v___x_1386_ = (crate::leanh::lean_unbox(v_a_1379_) as u8);
                    crate::leanh::lean_dec(v_a_1379_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1385_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1386_,
                    );
                    if v_isShared_1373_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1372_, 0, v___x_1385_);
                        v___x_1388_ = v___x_1372_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1385_);
                        v___x_1388_ = v_reuseFailAlloc_1396_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1388_);
                crate::leanh::lean_ctor_set(v___x_1389_, 1, v___x_1374_);
                v___x_1390_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1390_, 0, v___x_1389_);
                v___x_1391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1391_, 0, v___x_1390_);
                v___x_1392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                crate::leanh::lean_ctor_set(v___x_1392_, 1, v_snd_1356_);
                if v_isShared_1382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1381_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1381_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1394_;
            }
            8 => {
                if v_isShared_1401_ == 0 {
                    v___x_1403_ = v___x_1400_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
                    v___x_1403_ = v_reuseFailAlloc_1404_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_e_1409_: *mut crate::leanh::LeanObject,
    mut v_as_1410_: *mut crate::leanh::LeanObject,
    mut v_sz_1411_: *mut crate::leanh::LeanObject,
    mut v_i_1412_: *mut crate::leanh::LeanObject,
    mut v_b_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1419_: usize = 0;
    let mut v_i_boxed_1420_: usize = 0;
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1419_ = crate::leanh::lean_unbox_usize(v_sz_1411_);
    crate::leanh::lean_dec(v_sz_1411_);
    v_i_boxed_1420_ = crate::leanh::lean_unbox_usize(v_i_1412_);
    crate::leanh::lean_dec(v_i_1412_);
    v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_1409_, v_as_1410_, v_sz_boxed_1419_, v_i_boxed_1420_, v_b_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    crate::leanh::lean_dec(v___y_1417_);
    crate::leanh::lean_dec_ref(v___y_1416_);
    crate::leanh::lean_dec(v___y_1415_);
    crate::leanh::lean_dec_ref(v___y_1414_);
    crate::leanh::lean_dec_ref(v_as_1410_);
    return v_res_1421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(
    mut v_e_1422_: *mut crate::leanh::LeanObject,
    mut v_as_1423_: *mut crate::leanh::LeanObject,
    mut v_sz_1424_: usize,
    mut v_i_1425_: usize,
    mut v_b_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut v_a_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1437_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
                if v___x_1437_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1422_);
                    v___x_1438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1438_, 0, v_b_1426_);
                    return v___x_1438_;
                } else {
                    v_snd_1439_ = crate::leanh::lean_ctor_get(v_b_1426_, 1);
                    v_isSharedCheck_1490_ = (!crate::leanh::lean_is_exclusive(v_b_1426_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v_unused_1491_ = crate::leanh::lean_ctor_get(v_b_1426_, 0);
                        crate::leanh::lean_dec(v_unused_1491_);
                        v___x_1441_ = v_b_1426_;
                        v_isShared_1442_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1439_);
                        crate::leanh::lean_dec(v_b_1426_);
                        v___x_1441_ = crate::leanh::lean_box(0);
                        v_isShared_1442_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1443_ = crate::leanh::lean_box(0);
                v_a_1452_ = lean_array_uget(v_as_1423_, v_i_1425_);
                if crate::leanh::lean_obj_tag(v_a_1452_) == 0 {
                    v_a_1445_ = v_snd_1439_;
                    state = 2;
                    continue;
                } else {
                    v_val_1453_ = crate::leanh::lean_ctor_get(v_a_1452_, 0);
                    v_isSharedCheck_1489_ = (!crate::leanh::lean_is_exclusive(v_a_1452_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1455_ = v_a_1452_;
                        v_isShared_1456_ = v_isSharedCheck_1489_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1453_);
                        crate::leanh::lean_dec(v_a_1452_);
                        v___x_1455_ = crate::leanh::lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1489_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1441_, 1, v_a_1445_);
                    crate::leanh::lean_ctor_set(v___x_1441_, 0, v___x_1443_);
                    v___x_1447_ = v___x_1441_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1445_);
                    v___x_1447_ = v_reuseFailAlloc_1451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1448_ = 1usize;
                v___x_1449_ = lean_usize_add(v_i_1425_, v___x_1448_);
                v___x_1450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_1422_, v_as_1423_, v_sz_1424_, v___x_1449_, v___x_1447_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
                return v___x_1450_;
            }
            4 => {
                v___x_1457_ = crate::leanh::lean_box(0);
                v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
                v___x_1459_ = l_Lean_LocalDecl_isAuxDecl(v_val_1453_);
                if v___x_1459_ == 0 {
                    v___x_1460_ = l_Lean_LocalDecl_type(v_val_1453_);
                    crate::leanh::lean_inc_ref(v_e_1422_);
                    v___x_1461_ = l_Lean_Meta_isExprDefEq(
                        v___x_1460_,
                        v_e_1422_,
                        v___y_1432_,
                        v___y_1433_,
                        v___y_1434_,
                        v___y_1435_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1461_) == 0 {
                        v_a_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1480_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1480_ == 0 {
                            v___x_1464_ = v___x_1461_;
                            v_isShared_1465_ = v_isSharedCheck_1480_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1462_);
                            crate::leanh::lean_dec(v___x_1461_);
                            v___x_1464_ = crate::leanh::lean_box(0);
                            v_isShared_1465_ = v_isSharedCheck_1480_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1455_);
                        crate::leanh::lean_dec(v_val_1453_);
                        crate::leanh::lean_del_object(v___x_1441_);
                        crate::leanh::lean_dec(v_snd_1439_);
                        crate::leanh::lean_dec_ref(v_e_1422_);
                        v_a_1481_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1488_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1488_ == 0 {
                            v___x_1483_ = v___x_1461_;
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1481_);
                            crate::leanh::lean_dec(v___x_1461_);
                            v___x_1483_ = crate::leanh::lean_box(0);
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1455_);
                    crate::leanh::lean_dec(v_val_1453_);
                    crate::leanh::lean_dec(v_snd_1439_);
                    v_a_1445_ = v___x_1458_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1466_ = (crate::leanh::lean_unbox(v_a_1462_) as u8);
                if v___x_1466_ == 0 {
                    crate::leanh::lean_del_object(v___x_1464_);
                    crate::leanh::lean_dec(v_a_1462_);
                    crate::leanh::lean_del_object(v___x_1455_);
                    crate::leanh::lean_dec(v_val_1453_);
                    crate::leanh::lean_dec(v_snd_1439_);
                    v_a_1445_ = v___x_1458_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1441_);
                    crate::leanh::lean_dec_ref(v_e_1422_);
                    v___x_1467_ = l_Lean_LocalDecl_toExpr(v_val_1453_);
                    v___x_1468_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
                    v___x_1469_ = (crate::leanh::lean_unbox(v_a_1462_) as u8);
                    crate::leanh::lean_dec(v_a_1462_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1468_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1469_,
                    );
                    if v_isShared_1456_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1468_);
                        v___x_1471_ = v___x_1455_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1468_);
                        v___x_1471_ = v_reuseFailAlloc_1479_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                crate::leanh::lean_ctor_set(v___x_1472_, 1, v___x_1457_);
                v___x_1473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
                v___x_1474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                v___x_1475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                crate::leanh::lean_ctor_set(v___x_1475_, 1, v_snd_1439_);
                if v_isShared_1465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1475_);
                    v___x_1477_ = v___x_1464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1477_;
            }
            8 => {
                if v_isShared_1484_ == 0 {
                    v___x_1486_ = v___x_1483_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(
    mut v_e_1492_: *mut crate::leanh::LeanObject,
    mut v_as_1493_: *mut crate::leanh::LeanObject,
    mut v_sz_1494_: *mut crate::leanh::LeanObject,
    mut v_i_1495_: *mut crate::leanh::LeanObject,
    mut v_b_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
    mut v___y_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1507_: usize = 0;
    let mut v_i_boxed_1508_: usize = 0;
    let mut v_res_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1507_ = crate::leanh::lean_unbox_usize(v_sz_1494_);
    crate::leanh::lean_dec(v_sz_1494_);
    v_i_boxed_1508_ = crate::leanh::lean_unbox_usize(v_i_1495_);
    crate::leanh::lean_dec(v_i_1495_);
    v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_1492_, v_as_1493_, v_sz_boxed_1507_, v_i_boxed_1508_, v_b_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    crate::leanh::lean_dec(v___y_1505_);
    crate::leanh::lean_dec_ref(v___y_1504_);
    crate::leanh::lean_dec(v___y_1503_);
    crate::leanh::lean_dec_ref(v___y_1502_);
    crate::leanh::lean_dec(v___y_1501_);
    crate::leanh::lean_dec_ref(v___y_1500_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v___y_1497_);
    crate::leanh::lean_dec_ref(v_as_1493_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(
    mut v_init_1510_: *mut crate::leanh::LeanObject,
    mut v_e_1511_: *mut crate::leanh::LeanObject,
    mut v_n_1512_: *mut crate::leanh::LeanObject,
    mut v_b_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1527_: usize = 0;
    let mut v___x_1528_: usize = 0;
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v_fst_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_a_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_vs_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1556_: usize = 0;
    let mut v___x_1557_: usize = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v_fst_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_1512_) == 0 {
                    v_cs_1524_ = crate::leanh::lean_ctor_get(v_n_1512_, 0);
                    v___x_1525_ = crate::leanh::lean_box(0);
                    v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                    crate::leanh::lean_ctor_set(v___x_1526_, 1, v_b_1513_);
                    v_sz_1527_ = lean_array_size(v_cs_1524_);
                    v___x_1528_ = 0usize;
                    v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_1510_, v_e_1511_, v_cs_1524_, v_sz_1527_, v___x_1528_, v___x_1526_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
                    if crate::leanh::lean_obj_tag(v___x_1529_) == 0 {
                        v_a_1530_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                        v_isSharedCheck_1544_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1529_)) as u8;
                        if v_isSharedCheck_1544_ == 0 {
                            v___x_1532_ = v___x_1529_;
                            v_isShared_1533_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1530_);
                            crate::leanh::lean_dec(v___x_1529_);
                            v___x_1532_ = crate::leanh::lean_box(0);
                            v_isShared_1533_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1545_ = crate::leanh::lean_ctor_get(v___x_1529_, 0);
                        v_isSharedCheck_1552_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1529_)) as u8;
                        if v_isSharedCheck_1552_ == 0 {
                            v___x_1547_ = v___x_1529_;
                            v_isShared_1548_ = v_isSharedCheck_1552_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1545_);
                            crate::leanh::lean_dec(v___x_1529_);
                            v___x_1547_ = crate::leanh::lean_box(0);
                            v_isShared_1548_ = v_isSharedCheck_1552_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1553_ = crate::leanh::lean_ctor_get(v_n_1512_, 0);
                    v___x_1554_ = crate::leanh::lean_box(0);
                    v___x_1555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1555_, 0, v___x_1554_);
                    crate::leanh::lean_ctor_set(v___x_1555_, 1, v_b_1513_);
                    v_sz_1556_ = lean_array_size(v_vs_1553_);
                    v___x_1557_ = 0usize;
                    v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_1511_, v_vs_1553_, v_sz_1556_, v___x_1557_, v___x_1555_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
                    if crate::leanh::lean_obj_tag(v___x_1558_) == 0 {
                        v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1573_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1573_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1573_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1559_);
                            crate::leanh::lean_dec(v___x_1558_);
                            v___x_1561_ = crate::leanh::lean_box(0);
                            v_isShared_1562_ = v_isSharedCheck_1573_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1574_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v___x_1576_ = v___x_1558_;
                            v_isShared_1577_ = v_isSharedCheck_1581_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1574_);
                            crate::leanh::lean_dec(v___x_1558_);
                            v___x_1576_ = crate::leanh::lean_box(0);
                            v_isShared_1577_ = v_isSharedCheck_1581_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1534_ = crate::leanh::lean_ctor_get(v_a_1530_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1534_) == 0 {
                    v_snd_1535_ = crate::leanh::lean_ctor_get(v_a_1530_, 1);
                    crate::leanh::lean_inc(v_snd_1535_);
                    crate::leanh::lean_dec(v_a_1530_);
                    v___x_1536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1536_, 0, v_snd_1535_);
                    if v_isShared_1533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1532_, 0, v___x_1536_);
                        v___x_1538_ = v___x_1532_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
                        v___x_1538_ = v_reuseFailAlloc_1539_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1534_);
                    crate::leanh::lean_dec(v_a_1530_);
                    v_val_1540_ = crate::leanh::lean_ctor_get(v_fst_1534_, 0);
                    crate::leanh::lean_inc(v_val_1540_);
                    crate::leanh::lean_dec_ref_known(v_fst_1534_, 1);
                    if v_isShared_1533_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1532_, 0, v_val_1540_);
                        v___x_1542_ = v___x_1532_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_val_1540_);
                        v___x_1542_ = v_reuseFailAlloc_1543_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1538_;
            }
            3 => {
                return v___x_1542_;
            }
            4 => {
                if v_isShared_1548_ == 0 {
                    v___x_1550_ = v___x_1547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1551_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
                    v___x_1550_ = v_reuseFailAlloc_1551_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1550_;
            }
            6 => {
                v_fst_1563_ = crate::leanh::lean_ctor_get(v_a_1559_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1563_) == 0 {
                    v_snd_1564_ = crate::leanh::lean_ctor_get(v_a_1559_, 1);
                    crate::leanh::lean_inc(v_snd_1564_);
                    crate::leanh::lean_dec(v_a_1559_);
                    v___x_1565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1565_, 0, v_snd_1564_);
                    if v_isShared_1562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1561_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1563_);
                    crate::leanh::lean_dec(v_a_1559_);
                    v_val_1569_ = crate::leanh::lean_ctor_get(v_fst_1563_, 0);
                    crate::leanh::lean_inc(v_val_1569_);
                    crate::leanh::lean_dec_ref_known(v_fst_1563_, 1);
                    if v_isShared_1562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1561_, 0, v_val_1569_);
                        v___x_1571_ = v___x_1561_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_val_1569_);
                        v___x_1571_ = v_reuseFailAlloc_1572_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1567_;
            }
            8 => {
                return v___x_1571_;
            }
            9 => {
                if v_isShared_1577_ == 0 {
                    v___x_1579_ = v___x_1576_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(
    mut v_init_1582_: *mut crate::leanh::LeanObject,
    mut v_e_1583_: *mut crate::leanh::LeanObject,
    mut v_as_1584_: *mut crate::leanh::LeanObject,
    mut v_sz_1585_: usize,
    mut v_i_1586_: usize,
    mut v_b_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v_a_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: usize = 0;
    let mut v___x_1622_: usize = 0;
    let mut v_reuseFailAlloc_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v_unused_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
                if v___x_1598_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1583_);
                    v___x_1599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1599_, 0, v_b_1587_);
                    return v___x_1599_;
                } else {
                    v_snd_1600_ = crate::leanh::lean_ctor_get(v_b_1587_, 1);
                    v_isSharedCheck_1634_ = (!crate::leanh::lean_is_exclusive(v_b_1587_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v_unused_1635_ = crate::leanh::lean_ctor_get(v_b_1587_, 0);
                        crate::leanh::lean_dec(v_unused_1635_);
                        v___x_1602_ = v_b_1587_;
                        v_isShared_1603_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1600_);
                        crate::leanh::lean_dec(v_b_1587_);
                        v___x_1602_ = crate::leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1604_ = lean_array_uget_borrowed(v_as_1584_, v_i_1586_);
                crate::leanh::lean_inc(v_snd_1600_);
                crate::leanh::lean_inc_ref(v_e_1583_);
                v___x_1605_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1582_, v_e_1583_, v_a_1604_, v_snd_1600_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
                if crate::leanh::lean_obj_tag(v___x_1605_) == 0 {
                    v_a_1606_ = crate::leanh::lean_ctor_get(v___x_1605_, 0);
                    v_isSharedCheck_1625_ = (!crate::leanh::lean_is_exclusive(v___x_1605_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1608_ = v___x_1605_;
                        v_isShared_1609_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1606_);
                        crate::leanh::lean_dec(v___x_1605_);
                        v___x_1608_ = crate::leanh::lean_box(0);
                        v_isShared_1609_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1602_);
                    crate::leanh::lean_dec(v_snd_1600_);
                    crate::leanh::lean_dec_ref(v_e_1583_);
                    v_a_1626_ = crate::leanh::lean_ctor_get(v___x_1605_, 0);
                    v_isSharedCheck_1633_ = (!crate::leanh::lean_is_exclusive(v___x_1605_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1628_ = v___x_1605_;
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1626_);
                        crate::leanh::lean_dec(v___x_1605_);
                        v___x_1628_ = crate::leanh::lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1606_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_1583_);
                    v___x_1610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1610_, 0, v_a_1606_);
                    if v_isShared_1603_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1602_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1602_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_snd_1600_);
                        v___x_1612_ = v_reuseFailAlloc_1616_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1608_);
                    crate::leanh::lean_dec(v_snd_1600_);
                    v_a_1617_ = crate::leanh::lean_ctor_get(v_a_1606_, 0);
                    crate::leanh::lean_inc(v_a_1617_);
                    crate::leanh::lean_dec_ref_known(v_a_1606_, 1);
                    v___x_1618_ = crate::leanh::lean_box(0);
                    if v_isShared_1603_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1602_, 1, v_a_1617_);
                        crate::leanh::lean_ctor_set(v___x_1602_, 0, v___x_1618_);
                        v___x_1620_ = v___x_1602_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_a_1617_);
                        v___x_1620_ = v_reuseFailAlloc_1624_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1608_, 0, v___x_1612_);
                    v___x_1614_ = v___x_1608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1614_;
            }
            5 => {
                v___x_1621_ = 1usize;
                v___x_1622_ = lean_usize_add(v_i_1586_, v___x_1621_);
                v_i_1586_ = v___x_1622_;
                v_b_1587_ = v___x_1620_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1629_ == 0 {
                    v___x_1631_ = v___x_1628_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(
    mut v_init_1636_: *mut crate::leanh::LeanObject,
    mut v_e_1637_: *mut crate::leanh::LeanObject,
    mut v_as_1638_: *mut crate::leanh::LeanObject,
    mut v_sz_1639_: *mut crate::leanh::LeanObject,
    mut v_i_1640_: *mut crate::leanh::LeanObject,
    mut v_b_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1652_: usize = 0;
    let mut v_i_boxed_1653_: usize = 0;
    let mut v_res_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1652_ = crate::leanh::lean_unbox_usize(v_sz_1639_);
    crate::leanh::lean_dec(v_sz_1639_);
    v_i_boxed_1653_ = crate::leanh::lean_unbox_usize(v_i_1640_);
    crate::leanh::lean_dec(v_i_1640_);
    v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_1636_, v_e_1637_, v_as_1638_, v_sz_boxed_1652_, v_i_boxed_1653_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
    crate::leanh::lean_dec(v___y_1650_);
    crate::leanh::lean_dec_ref(v___y_1649_);
    crate::leanh::lean_dec(v___y_1648_);
    crate::leanh::lean_dec_ref(v___y_1647_);
    crate::leanh::lean_dec(v___y_1646_);
    crate::leanh::lean_dec_ref(v___y_1645_);
    crate::leanh::lean_dec(v___y_1644_);
    crate::leanh::lean_dec_ref(v___y_1643_);
    crate::leanh::lean_dec(v___y_1642_);
    crate::leanh::lean_dec_ref(v_as_1638_);
    crate::leanh::lean_dec_ref(v_init_1636_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(
    mut v_init_1655_: *mut crate::leanh::LeanObject,
    mut v_e_1656_: *mut crate::leanh::LeanObject,
    mut v_n_1657_: *mut crate::leanh::LeanObject,
    mut v_b_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1655_, v_e_1656_, v_n_1657_, v_b_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
    crate::leanh::lean_dec(v___y_1667_);
    crate::leanh::lean_dec_ref(v___y_1666_);
    crate::leanh::lean_dec(v___y_1665_);
    crate::leanh::lean_dec_ref(v___y_1664_);
    crate::leanh::lean_dec(v___y_1663_);
    crate::leanh::lean_dec_ref(v___y_1662_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    crate::leanh::lean_dec(v___y_1659_);
    crate::leanh::lean_dec_ref(v_n_1657_);
    crate::leanh::lean_dec_ref(v_init_1655_);
    return v_res_1669_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(
    mut v_e_1670_: *mut crate::leanh::LeanObject,
    mut v_t_1671_: *mut crate::leanh::LeanObject,
    mut v_init_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v_a_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1697_: usize = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v_fst_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1683_ = crate::leanh::lean_ctor_get(v_t_1671_, 0);
                v_tail_1684_ = crate::leanh::lean_ctor_get(v_t_1671_, 1);
                crate::leanh::lean_inc_ref(v_e_1670_);
                crate::leanh::lean_inc_ref(v_init_1672_);
                v___x_1685_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1672_, v_e_1670_, v_root_1683_, v_init_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                crate::leanh::lean_dec_ref(v_init_1672_);
                if crate::leanh::lean_obj_tag(v___x_1685_) == 0 {
                    v_a_1686_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1722_ = (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1722_ == 0 {
                        v___x_1688_ = v___x_1685_;
                        v_isShared_1689_ = v_isSharedCheck_1722_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1686_);
                        crate::leanh::lean_dec(v___x_1685_);
                        v___x_1688_ = crate::leanh::lean_box(0);
                        v_isShared_1689_ = v_isSharedCheck_1722_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1670_);
                    v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1730_ = (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1730_ == 0 {
                        v___x_1725_ = v___x_1685_;
                        v_isShared_1726_ = v_isSharedCheck_1730_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1723_);
                        crate::leanh::lean_dec(v___x_1685_);
                        v___x_1725_ = crate::leanh::lean_box(0);
                        v_isShared_1726_ = v_isSharedCheck_1730_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1686_) == 0 {
                    crate::leanh::lean_dec_ref(v_e_1670_);
                    v_a_1690_ = crate::leanh::lean_ctor_get(v_a_1686_, 0);
                    crate::leanh::lean_inc(v_a_1690_);
                    crate::leanh::lean_dec_ref_known(v_a_1686_, 1);
                    if v_isShared_1689_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1688_, 0, v_a_1690_);
                        v___x_1692_ = v___x_1688_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1690_);
                        v___x_1692_ = v_reuseFailAlloc_1693_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1688_);
                    v_a_1694_ = crate::leanh::lean_ctor_get(v_a_1686_, 0);
                    crate::leanh::lean_inc(v_a_1694_);
                    crate::leanh::lean_dec_ref_known(v_a_1686_, 1);
                    v___x_1695_ = crate::leanh::lean_box(0);
                    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
                    crate::leanh::lean_ctor_set(v___x_1696_, 1, v_a_1694_);
                    v_sz_1697_ = lean_array_size(v_tail_1684_);
                    v___x_1698_ = 0usize;
                    v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_1670_, v_tail_1684_, v_sz_1697_, v___x_1698_, v___x_1696_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                    if crate::leanh::lean_obj_tag(v___x_1699_) == 0 {
                        v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1713_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1713_ == 0 {
                            v___x_1702_ = v___x_1699_;
                            v_isShared_1703_ = v_isSharedCheck_1713_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1700_);
                            crate::leanh::lean_dec(v___x_1699_);
                            v___x_1702_ = crate::leanh::lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1713_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1714_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1721_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1721_ == 0 {
                            v___x_1716_ = v___x_1699_;
                            v_isShared_1717_ = v_isSharedCheck_1721_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1714_);
                            crate::leanh::lean_dec(v___x_1699_);
                            v___x_1716_ = crate::leanh::lean_box(0);
                            v_isShared_1717_ = v_isSharedCheck_1721_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1692_;
            }
            3 => {
                v_fst_1704_ = crate::leanh::lean_ctor_get(v_a_1700_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1704_) == 0 {
                    v_snd_1705_ = crate::leanh::lean_ctor_get(v_a_1700_, 1);
                    crate::leanh::lean_inc(v_snd_1705_);
                    crate::leanh::lean_dec(v_a_1700_);
                    if v_isShared_1703_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1702_, 0, v_snd_1705_);
                        v___x_1707_ = v___x_1702_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_snd_1705_);
                        v___x_1707_ = v_reuseFailAlloc_1708_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1704_);
                    crate::leanh::lean_dec(v_a_1700_);
                    v_val_1709_ = crate::leanh::lean_ctor_get(v_fst_1704_, 0);
                    crate::leanh::lean_inc(v_val_1709_);
                    crate::leanh::lean_dec_ref_known(v_fst_1704_, 1);
                    if v_isShared_1703_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1702_, 0, v_val_1709_);
                        v___x_1711_ = v___x_1702_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_val_1709_);
                        v___x_1711_ = v_reuseFailAlloc_1712_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1707_;
            }
            5 => {
                return v___x_1711_;
            }
            6 => {
                if v_isShared_1717_ == 0 {
                    v___x_1719_ = v___x_1716_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1719_;
            }
            8 => {
                if v_isShared_1726_ == 0 {
                    v___x_1728_ = v___x_1725_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
                    v___x_1728_ = v_reuseFailAlloc_1729_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(
    mut v_e_1731_: *mut crate::leanh::LeanObject,
    mut v_t_1732_: *mut crate::leanh::LeanObject,
    mut v_init_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(
            v_e_1731_,
            v_t_1732_,
            v_init_1733_,
            v___y_1734_,
            v___y_1735_,
            v___y_1736_,
            v___y_1737_,
            v___y_1738_,
            v___y_1739_,
            v___y_1740_,
            v___y_1741_,
            v___y_1742_,
        );
    crate::leanh::lean_dec(v___y_1742_);
    crate::leanh::lean_dec_ref(v___y_1741_);
    crate::leanh::lean_dec(v___y_1740_);
    crate::leanh::lean_dec_ref(v___y_1739_);
    crate::leanh::lean_dec(v___y_1738_);
    crate::leanh::lean_dec_ref(v___y_1737_);
    crate::leanh::lean_dec(v___y_1736_);
    crate::leanh::lean_dec_ref(v___y_1735_);
    crate::leanh::lean_dec(v___y_1734_);
    crate::leanh::lean_dec_ref(v_t_1732_);
    return v_res_1744_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeAssumption(
    mut v_e_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v_fst_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v_a_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1761_ = crate::leanh::lean_ctor_get(v_a_1756_, 2);
                v_decls_1762_ = crate::leanh::lean_ctor_get(v_lctx_1761_, 1);
                v___x_1763_ = l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0;
                v___x_1764_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_1750_, v_decls_1762_, v___x_1763_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
                if crate::leanh::lean_obj_tag(v___x_1764_) == 0 {
                    v_a_1765_ = crate::leanh::lean_ctor_get(v___x_1764_, 0);
                    v_isSharedCheck_1778_ = (!crate::leanh::lean_is_exclusive(v___x_1764_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1767_ = v___x_1764_;
                        v_isShared_1768_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1765_);
                        crate::leanh::lean_dec(v___x_1764_);
                        v___x_1767_ = crate::leanh::lean_box(0);
                        v_isShared_1768_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1779_ = crate::leanh::lean_ctor_get(v___x_1764_, 0);
                    v_isSharedCheck_1786_ = (!crate::leanh::lean_is_exclusive(v___x_1764_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1764_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1779_);
                        crate::leanh::lean_dec(v___x_1764_);
                        v___x_1781_ = crate::leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1769_ = crate::leanh::lean_ctor_get(v_a_1765_, 0);
                crate::leanh::lean_inc(v_fst_1769_);
                crate::leanh::lean_dec(v_a_1765_);
                if crate::leanh::lean_obj_tag(v_fst_1769_) == 0 {
                    v___x_1770_ = l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1;
                    if v_isShared_1768_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1767_, 0, v___x_1770_);
                        v___x_1772_ = v___x_1767_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
                        v___x_1772_ = v_reuseFailAlloc_1773_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1774_ = crate::leanh::lean_ctor_get(v_fst_1769_, 0);
                    crate::leanh::lean_inc(v_val_1774_);
                    crate::leanh::lean_dec_ref_known(v_fst_1769_, 1);
                    if v_isShared_1768_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1767_, 0, v_val_1774_);
                        v___x_1776_ = v___x_1767_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_val_1774_);
                        v___x_1776_ = v_reuseFailAlloc_1777_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1772_;
            }
            3 => {
                return v___x_1776_;
            }
            4 => {
                if v_isShared_1782_ == 0 {
                    v___x_1784_ = v___x_1781_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
                    v___x_1784_ = v_reuseFailAlloc_1785_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(
    mut v_e_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
    mut v_a_1792_: *mut crate::leanh::LeanObject,
    mut v_a_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(
        v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_,
        v_a_1795_, v_a_1796_,
    );
    crate::leanh::lean_dec(v_a_1796_);
    crate::leanh::lean_dec_ref(v_a_1795_);
    crate::leanh::lean_dec(v_a_1794_);
    crate::leanh::lean_dec_ref(v_a_1793_);
    crate::leanh::lean_dec(v_a_1792_);
    crate::leanh::lean_dec_ref(v_a_1791_);
    crate::leanh::lean_dec(v_a_1790_);
    crate::leanh::lean_dec_ref(v_a_1789_);
    crate::leanh::lean_dec(v_a_1788_);
    return v_res_1798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(
    mut v_e_1799_: *mut crate::leanh::LeanObject,
    mut v_as_1800_: *mut crate::leanh::LeanObject,
    mut v_sz_1801_: usize,
    mut v_i_1802_: usize,
    mut v_b_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_1799_, v_as_1800_, v_sz_1801_, v_i_1802_, v_b_1803_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
    return v___x_1814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(
    mut v_e_1815_: *mut crate::leanh::LeanObject,
    mut v_as_1816_: *mut crate::leanh::LeanObject,
    mut v_sz_1817_: *mut crate::leanh::LeanObject,
    mut v_i_1818_: *mut crate::leanh::LeanObject,
    mut v_b_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1830_: usize = 0;
    let mut v_i_boxed_1831_: usize = 0;
    let mut v_res_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1830_ = crate::leanh::lean_unbox_usize(v_sz_1817_);
    crate::leanh::lean_dec(v_sz_1817_);
    v_i_boxed_1831_ = crate::leanh::lean_unbox_usize(v_i_1818_);
    crate::leanh::lean_dec(v_i_1818_);
    v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_1815_, v_as_1816_, v_sz_boxed_1830_, v_i_boxed_1831_, v_b_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    crate::leanh::lean_dec(v___y_1826_);
    crate::leanh::lean_dec_ref(v___y_1825_);
    crate::leanh::lean_dec(v___y_1824_);
    crate::leanh::lean_dec_ref(v___y_1823_);
    crate::leanh::lean_dec(v___y_1822_);
    crate::leanh::lean_dec_ref(v___y_1821_);
    crate::leanh::lean_dec(v___y_1820_);
    crate::leanh::lean_dec_ref(v_as_1816_);
    return v_res_1832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(
    mut v_e_1833_: *mut crate::leanh::LeanObject,
    mut v_as_1834_: *mut crate::leanh::LeanObject,
    mut v_sz_1835_: usize,
    mut v_i_1836_: usize,
    mut v_b_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_1833_, v_as_1834_, v_sz_1835_, v_i_1836_, v_b_1837_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    return v___x_1848_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_e_1849_: *mut crate::leanh::LeanObject,
    mut v_as_1850_: *mut crate::leanh::LeanObject,
    mut v_sz_1851_: *mut crate::leanh::LeanObject,
    mut v_i_1852_: *mut crate::leanh::LeanObject,
    mut v_b_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1864_: usize = 0;
    let mut v_i_boxed_1865_: usize = 0;
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1864_ = crate::leanh::lean_unbox_usize(v_sz_1851_);
    crate::leanh::lean_dec(v_sz_1851_);
    v_i_boxed_1865_ = crate::leanh::lean_unbox_usize(v_i_1852_);
    crate::leanh::lean_dec(v_i_1852_);
    v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_1849_, v_as_1850_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
    crate::leanh::lean_dec(v___y_1862_);
    crate::leanh::lean_dec_ref(v___y_1861_);
    crate::leanh::lean_dec(v___y_1860_);
    crate::leanh::lean_dec_ref(v___y_1859_);
    crate::leanh::lean_dec(v___y_1858_);
    crate::leanh::lean_dec_ref(v___y_1857_);
    crate::leanh::lean_dec(v___y_1856_);
    crate::leanh::lean_dec_ref(v___y_1855_);
    crate::leanh::lean_dec(v___y_1854_);
    crate::leanh::lean_dec_ref(v_as_1850_);
    return v_res_1866_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Discharger(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Discharger(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Discharger(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
}
