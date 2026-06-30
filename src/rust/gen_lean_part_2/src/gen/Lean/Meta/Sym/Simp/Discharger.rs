// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Discharger
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.AppBuilder
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_sym_simp, lean_usize_add,
    lean_usize_dec_lt,
};
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
pub static l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [1 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(
    mut v_x_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_934_) == 0 {
        let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_935_ = leanh::lean_unsigned_to_nat(0);
        return v___x_935_;
    } else {
        let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_936_ = leanh::lean_unsigned_to_nat(1);
        return v___x_936_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(
    mut v_x_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(v_x_937_);
    leanh::lean_dec_ref(v_x_937_);
    return v_res_938_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(
    mut v_t_939_: *mut leanh::LeanObject,
    mut v_k_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_939_) == 0 {
        let mut v_contextDependent_941_: u8 = 0;
        let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_contextDependent_941_ = leanh::lean_ctor_get_uint8(v_t_939_, 0 as u32);
        leanh::lean_dec_ref_known(v_t_939_, 0);
        v___x_942_ = leanh::lean_box((v_contextDependent_941_) as usize);
        v___x_943_ = leanh::lean_apply_1(v_k_940_, v___x_942_);
        return v___x_943_;
    } else {
        let mut v_proof_944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_contextDependent_945_: u8 = 0;
        let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_proof_944_ = leanh::lean_ctor_get(v_t_939_, 0);
        leanh::lean_inc_ref(v_proof_944_);
        v_contextDependent_945_ = leanh::lean_ctor_get_uint8(
            v_t_939_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        );
        leanh::lean_dec_ref_known(v_t_939_, 1);
        v___x_946_ = leanh::lean_box((v_contextDependent_945_) as usize);
        v___x_947_ = leanh::lean_apply_2(v_k_940_, v_proof_944_, v___x_946_);
        return v___x_947_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(
    mut v_motive_948_: *mut leanh::LeanObject,
    mut v_ctorIdx_949_: *mut leanh::LeanObject,
    mut v_t_950_: *mut leanh::LeanObject,
    mut v_h_951_: *mut leanh::LeanObject,
    mut v_k_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_953_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_950_, v_k_952_);
    return v___x_953_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(
    mut v_motive_954_: *mut leanh::LeanObject,
    mut v_ctorIdx_955_: *mut leanh::LeanObject,
    mut v_t_956_: *mut leanh::LeanObject,
    mut v_h_957_: *mut leanh::LeanObject,
    mut v_k_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(
        v_motive_954_,
        v_ctorIdx_955_,
        v_t_956_,
        v_h_957_,
        v_k_958_,
    );
    leanh::lean_dec(v_ctorIdx_955_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(
    mut v_t_960_: *mut leanh::LeanObject,
    mut v_failed_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_960_, v_failed_961_);
    return v___x_962_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(
    mut v_motive_963_: *mut leanh::LeanObject,
    mut v_t_964_: *mut leanh::LeanObject,
    mut v_h_965_: *mut leanh::LeanObject,
    mut v_failed_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_964_, v_failed_966_);
    return v___x_967_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(
    mut v_t_968_: *mut leanh::LeanObject,
    mut v_solved_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_968_, v_solved_969_);
    return v___x_970_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(
    mut v_motive_971_: *mut leanh::LeanObject,
    mut v_t_972_: *mut leanh::LeanObject,
    mut v_h_973_: *mut leanh::LeanObject,
    mut v_solved_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_975_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_972_, v_solved_974_);
    return v___x_975_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(
    mut v_e_976_: *mut leanh::LeanObject,
    mut v_result_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_result_977_) == 0 {
        let mut v_contextDependent_978_: u8 = 0;
        let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_976_);
        v_contextDependent_978_ = leanh::lean_ctor_get_uint8(v_result_977_, 1 as u32);
        leanh::lean_dec_ref_known(v_result_977_, 0);
        v___x_979_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
        leanh::lean_ctor_set_uint8(v___x_979_, 0 as u32, v_contextDependent_978_);
        return v___x_979_;
    } else {
        let mut v_e_x27_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_proof_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_contextDependent_982_: u8 = 0;
        let mut v___x_983_: u8 = 0;
        v_e_x27_980_ = leanh::lean_ctor_get(v_result_977_, 0);
        leanh::lean_inc_ref(v_e_x27_980_);
        v_proof_981_ = leanh::lean_ctor_get(v_result_977_, 1);
        leanh::lean_inc_ref(v_proof_981_);
        v_contextDependent_982_ = leanh::lean_ctor_get_uint8(
            v_result_977_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
        );
        leanh::lean_dec_ref_known(v_result_977_, 2);
        v___x_983_ = l_Lean_Expr_isTrue(v_e_x27_980_);
        if v___x_983_ == 0 {
            let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_proof_981_);
            leanh::lean_dec_ref(v_e_976_);
            v___x_984_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
            leanh::lean_ctor_set_uint8(v___x_984_, 0 as u32, v_contextDependent_982_);
            return v___x_984_;
        } else {
            let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_985_ = l_Lean_Meta_mkOfEqTrueCore(v_e_976_, v_proof_981_);
            v___x_986_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_986_, 0, v___x_985_);
            leanh::lean_ctor_set_uint8(
                v___x_986_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v_contextDependent_982_,
            );
            return v___x_986_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(
    mut v_p_987_: *mut leanh::LeanObject,
    mut v_e_988_: *mut leanh::LeanObject,
    mut v_a_989_: *mut leanh::LeanObject,
    mut v_a_990_: *mut leanh::LeanObject,
    mut v_a_991_: *mut leanh::LeanObject,
    mut v_a_992_: *mut leanh::LeanObject,
    mut v_a_993_: *mut leanh::LeanObject,
    mut v_a_994_: *mut leanh::LeanObject,
    mut v_a_995_: *mut leanh::LeanObject,
    mut v_a_996_: *mut leanh::LeanObject,
    mut v_a_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1012_: u8 = 0;
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_997_);
                leanh::lean_inc_ref(v_a_996_);
                leanh::lean_inc(v_a_995_);
                leanh::lean_inc_ref(v_a_994_);
                leanh::lean_inc(v_a_993_);
                leanh::lean_inc_ref(v_a_992_);
                leanh::lean_inc(v_a_991_);
                leanh::lean_inc_ref(v_a_990_);
                leanh::lean_inc(v_a_989_);
                leanh::lean_inc_ref(v_e_988_);
                v___x_999_ = leanh::lean_apply_11(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_999_) == 0 {
                    v_a_1000_ = leanh::lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1008_ = (!leanh::lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_1002_ = v___x_999_;
                        v_isShared_1003_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1000_);
                        leanh::lean_dec(v___x_999_);
                        v___x_1002_ = leanh::lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_988_);
                    v_a_1009_ = leanh::lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1016_ = (!leanh::lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1016_ == 0 {
                        v___x_1011_ = v___x_999_;
                        v_isShared_1012_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1009_);
                        leanh::lean_dec(v___x_999_);
                        v___x_1011_ = leanh::lean_box(0);
                        v_isShared_1012_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1004_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_988_, v_a_1000_);
                if v_isShared_1003_ == 0 {
                    leanh::lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
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
                    v_reuseFailAlloc_1015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
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
    mut v_p_1017_: *mut leanh::LeanObject,
    mut v_e_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
    mut v_a_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
    mut v_a_1026_: *mut leanh::LeanObject,
    mut v_a_1027_: *mut leanh::LeanObject,
    mut v_a_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(
        v_p_1017_, v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_,
        v_a_1025_, v_a_1026_, v_a_1027_,
    );
    leanh::lean_dec(v_a_1027_);
    leanh::lean_dec_ref(v_a_1026_);
    leanh::lean_dec(v_a_1025_);
    leanh::lean_dec_ref(v_a_1024_);
    leanh::lean_dec(v_a_1023_);
    leanh::lean_dec_ref(v_a_1022_);
    leanh::lean_dec(v_a_1021_);
    leanh::lean_dec_ref(v_a_1020_);
    leanh::lean_dec(v_a_1019_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_persistentCache_1031_: *mut leanh::LeanObject,
    mut v_transientCache_1032_: *mut leanh::LeanObject,
    mut v_funext_1033_: *mut leanh::LeanObject,
    mut v_a_x3f_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v_unused_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_st_ref_take(v_a_1030_);
                v_numSteps_1037_ = leanh::lean_ctor_get(v___x_1036_, 0);
                v_isSharedCheck_1047_ = (!leanh::lean_is_exclusive(v___x_1036_)) as u8;
                if v_isSharedCheck_1047_ == 0 {
                    v_unused_1048_ = leanh::lean_ctor_get(v___x_1036_, 3);
                    leanh::lean_dec(v_unused_1048_);
                    v_unused_1049_ = leanh::lean_ctor_get(v___x_1036_, 2);
                    leanh::lean_dec(v_unused_1049_);
                    v_unused_1050_ = leanh::lean_ctor_get(v___x_1036_, 1);
                    leanh::lean_dec(v_unused_1050_);
                    v___x_1039_ = v___x_1036_;
                    v_isShared_1040_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numSteps_1037_);
                    leanh::lean_dec(v___x_1036_);
                    v___x_1039_ = leanh::lean_box(0);
                    v_isShared_1040_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1040_ == 0 {
                    leanh::lean_ctor_set(v___x_1039_, 3, v_funext_1033_);
                    leanh::lean_ctor_set(v___x_1039_, 2, v_transientCache_1032_);
                    leanh::lean_ctor_set(v___x_1039_, 1, v_persistentCache_1031_);
                    v___x_1042_ = v___x_1039_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_numSteps_1037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_persistentCache_1031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_transientCache_1032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_funext_1033_);
                    v___x_1042_ = v_reuseFailAlloc_1046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1043_ = lean_st_ref_set(v_a_1030_, v___x_1042_);
                v___x_1044_ = leanh::lean_box(0);
                v___x_1045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1045_, 0, v___x_1044_);
                return v___x_1045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_persistentCache_1052_: *mut leanh::LeanObject,
    mut v_transientCache_1053_: *mut leanh::LeanObject,
    mut v_funext_1054_: *mut leanh::LeanObject,
    mut v_a_x3f_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
        v_a_1051_,
        v_persistentCache_1052_,
        v_transientCache_1053_,
        v_funext_1054_,
        v_a_x3f_1055_,
    );
    leanh::lean_dec(v_a_x3f_1055_);
    leanh::lean_dec(v_a_1051_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeSimpSelf(
    mut v_e_1060_: *mut leanh::LeanObject,
    mut v_a_1061_: *mut leanh::LeanObject,
    mut v_a_1062_: *mut leanh::LeanObject,
    mut v_a_1063_: *mut leanh::LeanObject,
    mut v_a_1064_: *mut leanh::LeanObject,
    mut v_a_1065_: *mut leanh::LeanObject,
    mut v_a_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
    mut v_a_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v_maxDischargeDepth_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLCtxSize_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeDepth_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut v_unused_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_unused_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut v_a_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1071_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_1062_);
                if leanh::lean_obj_tag(v___x_1071_) == 0 {
                    v_a_1072_ = leanh::lean_ctor_get(v___x_1071_, 0);
                    v_isSharedCheck_1124_ = (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                    if v_isSharedCheck_1124_ == 0 {
                        v___x_1074_ = v___x_1071_;
                        v_isShared_1075_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1072_);
                        leanh::lean_dec(v___x_1071_);
                        v___x_1074_ = leanh::lean_box(0);
                        v_isShared_1075_ = v_isSharedCheck_1124_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1060_);
                    v_a_1125_ = leanh::lean_ctor_get(v___x_1071_, 0);
                    v_isSharedCheck_1132_ = (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1127_ = v___x_1071_;
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1125_);
                        leanh::lean_dec(v___x_1071_);
                        v___x_1127_ = leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1132_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_maxDischargeDepth_1076_ = leanh::lean_ctor_get(v_a_1072_, 1);
                leanh::lean_inc(v_maxDischargeDepth_1076_);
                leanh::lean_dec(v_a_1072_);
                v_config_1077_ = leanh::lean_ctor_get(v_a_1062_, 0);
                v_initialLCtxSize_1078_ = leanh::lean_ctor_get(v_a_1062_, 1);
                v_dischargeDepth_1079_ = leanh::lean_ctor_get(v_a_1062_, 2);
                v___x_1080_ = lean_nat_dec_lt(v_maxDischargeDepth_1076_, v_dischargeDepth_1079_);
                leanh::lean_dec(v_maxDischargeDepth_1076_);
                if v___x_1080_ == 0 {
                    leanh::lean_del_object(v___x_1074_);
                    v___x_1081_ = lean_st_ref_get(v_a_1063_);
                    v___x_1082_ = lean_st_ref_get(v_a_1063_);
                    v___x_1083_ = lean_st_ref_get(v_a_1063_);
                    v_persistentCache_1084_ = leanh::lean_ctor_get(v___x_1081_, 1);
                    leanh::lean_inc_ref(v_persistentCache_1084_);
                    leanh::lean_dec(v___x_1081_);
                    v_transientCache_1085_ = leanh::lean_ctor_get(v___x_1082_, 2);
                    leanh::lean_inc_ref(v_transientCache_1085_);
                    leanh::lean_dec(v___x_1082_);
                    v_funext_1086_ = leanh::lean_ctor_get(v___x_1083_, 3);
                    leanh::lean_inc_ref(v_funext_1086_);
                    leanh::lean_dec(v___x_1083_);
                    v___x_1087_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1088_ = lean_nat_add(v_dischargeDepth_1079_, v___x_1087_);
                    leanh::lean_inc(v_initialLCtxSize_1078_);
                    leanh::lean_inc_ref(v_config_1077_);
                    v___x_1089_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1089_, 0, v_config_1077_);
                    leanh::lean_ctor_set(v___x_1089_, 1, v_initialLCtxSize_1078_);
                    leanh::lean_ctor_set(v___x_1089_, 2, v___x_1088_);
                    leanh::lean_inc(v_a_1069_);
                    leanh::lean_inc_ref(v_a_1068_);
                    leanh::lean_inc(v_a_1067_);
                    leanh::lean_inc_ref(v_a_1066_);
                    leanh::lean_inc(v_a_1065_);
                    leanh::lean_inc_ref(v_a_1064_);
                    leanh::lean_inc(v_a_1063_);
                    leanh::lean_inc(v_a_1061_);
                    leanh::lean_inc_ref(v_e_1060_);
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
                    if leanh::lean_obj_tag(v___x_1090_) == 0 {
                        v_a_1091_ = leanh::lean_ctor_get(v___x_1090_, 0);
                        v_isSharedCheck_1108_ =
                            (!leanh::lean_is_exclusive(v___x_1090_)) as u8;
                        if v_isSharedCheck_1108_ == 0 {
                            v___x_1093_ = v___x_1090_;
                            v_isShared_1094_ = v_isSharedCheck_1108_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1091_);
                            leanh::lean_dec(v___x_1090_);
                            v___x_1093_ = leanh::lean_box(0);
                            v_isShared_1094_ = v_isSharedCheck_1108_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1060_);
                        v_a_1109_ = leanh::lean_ctor_get(v___x_1090_, 0);
                        leanh::lean_inc(v_a_1109_);
                        leanh::lean_dec_ref_known(v___x_1090_, 1);
                        v___x_1110_ = leanh::lean_box(0);
                        v___x_1111_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(
                            v_a_1063_,
                            v_persistentCache_1084_,
                            v_transientCache_1085_,
                            v_funext_1086_,
                            v___x_1110_,
                        );
                        v_isSharedCheck_1118_ =
                            (!leanh::lean_is_exclusive(v___x_1111_)) as u8;
                        if v_isSharedCheck_1118_ == 0 {
                            v_unused_1119_ = leanh::lean_ctor_get(v___x_1111_, 0);
                            leanh::lean_dec(v_unused_1119_);
                            v___x_1113_ = v___x_1111_;
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1111_);
                            v___x_1113_ = leanh::lean_box(0);
                            v_isShared_1114_ = v_isSharedCheck_1118_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1060_);
                    v___x_1120_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0;
                    if v_isShared_1075_ == 0 {
                        leanh::lean_ctor_set(v___x_1074_, 0, v___x_1120_);
                        v___x_1122_ = v___x_1074_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1123_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
                        v___x_1122_ = v_reuseFailAlloc_1123_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1095_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_1060_, v_a_1091_);
                leanh::lean_inc_ref(v___x_1095_);
                if v_isShared_1094_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1093_, 1);
                    leanh::lean_ctor_set(v___x_1093_, 0, v___x_1095_);
                    v___x_1097_ = v___x_1093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1095_);
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
                leanh::lean_dec_ref(v___x_1097_);
                v_isSharedCheck_1105_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                if v_isSharedCheck_1105_ == 0 {
                    v_unused_1106_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    leanh::lean_dec(v_unused_1106_);
                    v___x_1100_ = v___x_1098_;
                    v_isShared_1101_ = v_isSharedCheck_1105_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1098_);
                    v___x_1100_ = leanh::lean_box(0);
                    v_isShared_1101_ = v_isSharedCheck_1105_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1101_ == 0 {
                    leanh::lean_ctor_set(v___x_1100_, 0, v___x_1095_);
                    v___x_1103_ = v___x_1100_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1095_);
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
                    leanh::lean_ctor_set_tag(v___x_1113_, 1);
                    leanh::lean_ctor_set(v___x_1113_, 0, v_a_1109_);
                    v___x_1116_ = v___x_1113_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1109_);
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
                    v_reuseFailAlloc_1131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
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
    mut v_e_1133_: *mut leanh::LeanObject,
    mut v_a_1134_: *mut leanh::LeanObject,
    mut v_a_1135_: *mut leanh::LeanObject,
    mut v_a_1136_: *mut leanh::LeanObject,
    mut v_a_1137_: *mut leanh::LeanObject,
    mut v_a_1138_: *mut leanh::LeanObject,
    mut v_a_1139_: *mut leanh::LeanObject,
    mut v_a_1140_: *mut leanh::LeanObject,
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(
        v_e_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_,
        v_a_1141_, v_a_1142_,
    );
    leanh::lean_dec(v_a_1142_);
    leanh::lean_dec_ref(v_a_1141_);
    leanh::lean_dec(v_a_1140_);
    leanh::lean_dec_ref(v_a_1139_);
    leanh::lean_dec(v_a_1138_);
    leanh::lean_dec_ref(v_a_1137_);
    leanh::lean_dec(v_a_1136_);
    leanh::lean_dec_ref(v_a_1135_);
    leanh::lean_dec(v_a_1134_);
    return v_res_1144_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___redArg() -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0;
    v___x_1147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
    return v___x_1147_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(
    mut v_a_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
    return v_res_1149_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone(
    mut v_x_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
    mut v_a_1152_: *mut leanh::LeanObject,
    mut v_a_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
    mut v_a_1157_: *mut leanh::LeanObject,
    mut v_a_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
    return v___x_1161_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeNone___boxed(
    mut v_x_1162_: *mut leanh::LeanObject,
    mut v_a_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_a_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
    mut v_a_1171_: *mut leanh::LeanObject,
    mut v_a_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Lean_Meta_Sym_Simp_dischargeNone(
        v_x_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_,
        v_a_1170_, v_a_1171_,
    );
    leanh::lean_dec(v_a_1171_);
    leanh::lean_dec_ref(v_a_1170_);
    leanh::lean_dec(v_a_1169_);
    leanh::lean_dec_ref(v_a_1168_);
    leanh::lean_dec(v_a_1167_);
    leanh::lean_dec_ref(v_a_1166_);
    leanh::lean_dec(v_a_1165_);
    leanh::lean_dec_ref(v_a_1164_);
    leanh::lean_dec(v_a_1163_);
    leanh::lean_dec_ref(v_x_1162_);
    return v_res_1173_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(
    mut v_e_1177_: *mut leanh::LeanObject,
    mut v_as_1178_: *mut leanh::LeanObject,
    mut v_sz_1179_: usize,
    mut v_i_1180_: usize,
    mut v_b_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v_reuseFailAlloc_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u8 = 0;
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v_a_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_unused_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1187_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
                if v___x_1187_ == 0 {
                    leanh::lean_dec_ref(v_e_1177_);
                    v___x_1188_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1188_, 0, v_b_1181_);
                    return v___x_1188_;
                } else {
                    v_snd_1189_ = leanh::lean_ctor_get(v_b_1181_, 1);
                    v_isSharedCheck_1239_ = (!leanh::lean_is_exclusive(v_b_1181_)) as u8;
                    if v_isSharedCheck_1239_ == 0 {
                        v_unused_1240_ = leanh::lean_ctor_get(v_b_1181_, 0);
                        leanh::lean_dec(v_unused_1240_);
                        v___x_1191_ = v_b_1181_;
                        v_isShared_1192_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1189_);
                        leanh::lean_dec(v_b_1181_);
                        v___x_1191_ = leanh::lean_box(0);
                        v_isShared_1192_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1193_ = leanh::lean_box(0);
                v_a_1202_ = lean_array_uget(v_as_1178_, v_i_1180_);
                if leanh::lean_obj_tag(v_a_1202_) == 0 {
                    v_a_1195_ = v_snd_1189_;
                    state = 2;
                    continue;
                } else {
                    v_val_1203_ = leanh::lean_ctor_get(v_a_1202_, 0);
                    v_isSharedCheck_1238_ = (!leanh::lean_is_exclusive(v_a_1202_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1205_ = v_a_1202_;
                        v_isShared_1206_ = v_isSharedCheck_1238_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1203_);
                        leanh::lean_dec(v_a_1202_);
                        v___x_1205_ = leanh::lean_box(0);
                        v_isShared_1206_ = v_isSharedCheck_1238_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1192_ == 0 {
                    leanh::lean_ctor_set(v___x_1191_, 1, v_a_1195_);
                    leanh::lean_ctor_set(v___x_1191_, 0, v___x_1193_);
                    v___x_1197_ = v___x_1191_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_a_1195_);
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
                v___x_1207_ = leanh::lean_box(0);
                v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0;
                v___x_1209_ = l_Lean_LocalDecl_isAuxDecl(v_val_1203_);
                if v___x_1209_ == 0 {
                    v___x_1210_ = l_Lean_LocalDecl_type(v_val_1203_);
                    leanh::lean_inc_ref(v_e_1177_);
                    v___x_1211_ = l_Lean_Meta_isExprDefEq(
                        v___x_1210_,
                        v_e_1177_,
                        v___y_1182_,
                        v___y_1183_,
                        v___y_1184_,
                        v___y_1185_,
                    );
                    if leanh::lean_obj_tag(v___x_1211_) == 0 {
                        v_a_1212_ = leanh::lean_ctor_get(v___x_1211_, 0);
                        v_isSharedCheck_1229_ =
                            (!leanh::lean_is_exclusive(v___x_1211_)) as u8;
                        if v_isSharedCheck_1229_ == 0 {
                            v___x_1214_ = v___x_1211_;
                            v_isShared_1215_ = v_isSharedCheck_1229_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1212_);
                            leanh::lean_dec(v___x_1211_);
                            v___x_1214_ = leanh::lean_box(0);
                            v_isShared_1215_ = v_isSharedCheck_1229_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1205_);
                        leanh::lean_dec(v_val_1203_);
                        leanh::lean_del_object(v___x_1191_);
                        leanh::lean_dec(v_snd_1189_);
                        leanh::lean_dec_ref(v_e_1177_);
                        v_a_1230_ = leanh::lean_ctor_get(v___x_1211_, 0);
                        v_isSharedCheck_1237_ =
                            (!leanh::lean_is_exclusive(v___x_1211_)) as u8;
                        if v_isSharedCheck_1237_ == 0 {
                            v___x_1232_ = v___x_1211_;
                            v_isShared_1233_ = v_isSharedCheck_1237_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1230_);
                            leanh::lean_dec(v___x_1211_);
                            v___x_1232_ = leanh::lean_box(0);
                            v_isShared_1233_ = v_isSharedCheck_1237_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1205_);
                    leanh::lean_dec(v_val_1203_);
                    leanh::lean_dec(v_snd_1189_);
                    v_a_1195_ = v___x_1208_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1216_ = (leanh::lean_unbox(v_a_1212_) as u8);
                if v___x_1216_ == 0 {
                    leanh::lean_del_object(v___x_1214_);
                    leanh::lean_dec(v_a_1212_);
                    leanh::lean_del_object(v___x_1205_);
                    leanh::lean_dec(v_val_1203_);
                    leanh::lean_dec(v_snd_1189_);
                    v_a_1195_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1191_);
                    leanh::lean_dec_ref(v_e_1177_);
                    v___x_1217_ = l_Lean_LocalDecl_toExpr(v_val_1203_);
                    v___x_1218_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1217_);
                    v___x_1219_ = (leanh::lean_unbox(v_a_1212_) as u8);
                    leanh::lean_dec(v_a_1212_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1218_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1219_,
                    );
                    if v_isShared_1206_ == 0 {
                        leanh::lean_ctor_set(v___x_1205_, 0, v___x_1218_);
                        v___x_1221_ = v___x_1205_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1218_);
                        v___x_1221_ = v_reuseFailAlloc_1228_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1222_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1222_, 0, v___x_1221_);
                leanh::lean_ctor_set(v___x_1222_, 1, v___x_1207_);
                v___x_1223_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
                v___x_1224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                leanh::lean_ctor_set(v___x_1224_, 1, v_snd_1189_);
                if v_isShared_1215_ == 0 {
                    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1224_);
                    v___x_1226_ = v___x_1214_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
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
                    v_reuseFailAlloc_1236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
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
    mut v_e_1241_: *mut leanh::LeanObject,
    mut v_as_1242_: *mut leanh::LeanObject,
    mut v_sz_1243_: *mut leanh::LeanObject,
    mut v_i_1244_: *mut leanh::LeanObject,
    mut v_b_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1251_: usize = 0;
    let mut v_i_boxed_1252_: usize = 0;
    let mut v_res_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1251_ = leanh::lean_unbox_usize(v_sz_1243_);
    leanh::lean_dec(v_sz_1243_);
    v_i_boxed_1252_ = leanh::lean_unbox_usize(v_i_1244_);
    leanh::lean_dec(v_i_1244_);
    v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_1241_, v_as_1242_, v_sz_boxed_1251_, v_i_boxed_1252_, v_b_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
    leanh::lean_dec(v___y_1249_);
    leanh::lean_dec_ref(v___y_1248_);
    leanh::lean_dec(v___y_1247_);
    leanh::lean_dec_ref(v___y_1246_);
    leanh::lean_dec_ref(v_as_1242_);
    return v_res_1253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(
    mut v_e_1254_: *mut leanh::LeanObject,
    mut v_as_1255_: *mut leanh::LeanObject,
    mut v_sz_1256_: usize,
    mut v_i_1257_: usize,
    mut v_b_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: u8 = 0;
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut v_a_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1319_: u8 = 0;
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_unused_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
                if v___x_1269_ == 0 {
                    leanh::lean_dec_ref(v_e_1254_);
                    v___x_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1270_, 0, v_b_1258_);
                    return v___x_1270_;
                } else {
                    v_snd_1271_ = leanh::lean_ctor_get(v_b_1258_, 1);
                    v_isSharedCheck_1321_ = (!leanh::lean_is_exclusive(v_b_1258_)) as u8;
                    if v_isSharedCheck_1321_ == 0 {
                        v_unused_1322_ = leanh::lean_ctor_get(v_b_1258_, 0);
                        leanh::lean_dec(v_unused_1322_);
                        v___x_1273_ = v_b_1258_;
                        v_isShared_1274_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1271_);
                        leanh::lean_dec(v_b_1258_);
                        v___x_1273_ = leanh::lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1275_ = leanh::lean_box(0);
                v_a_1284_ = lean_array_uget(v_as_1255_, v_i_1257_);
                if leanh::lean_obj_tag(v_a_1284_) == 0 {
                    v_a_1277_ = v_snd_1271_;
                    state = 2;
                    continue;
                } else {
                    v_val_1285_ = leanh::lean_ctor_get(v_a_1284_, 0);
                    v_isSharedCheck_1320_ = (!leanh::lean_is_exclusive(v_a_1284_)) as u8;
                    if v_isSharedCheck_1320_ == 0 {
                        v___x_1287_ = v_a_1284_;
                        v_isShared_1288_ = v_isSharedCheck_1320_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1285_);
                        leanh::lean_dec(v_a_1284_);
                        v___x_1287_ = leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1320_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1274_ == 0 {
                    leanh::lean_ctor_set(v___x_1273_, 1, v_a_1277_);
                    leanh::lean_ctor_set(v___x_1273_, 0, v___x_1275_);
                    v___x_1279_ = v___x_1273_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_a_1277_);
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
                v___x_1289_ = leanh::lean_box(0);
                v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0;
                v___x_1291_ = l_Lean_LocalDecl_isAuxDecl(v_val_1285_);
                if v___x_1291_ == 0 {
                    v___x_1292_ = l_Lean_LocalDecl_type(v_val_1285_);
                    leanh::lean_inc_ref(v_e_1254_);
                    v___x_1293_ = l_Lean_Meta_isExprDefEq(
                        v___x_1292_,
                        v_e_1254_,
                        v___y_1264_,
                        v___y_1265_,
                        v___y_1266_,
                        v___y_1267_,
                    );
                    if leanh::lean_obj_tag(v___x_1293_) == 0 {
                        v_a_1294_ = leanh::lean_ctor_get(v___x_1293_, 0);
                        v_isSharedCheck_1311_ =
                            (!leanh::lean_is_exclusive(v___x_1293_)) as u8;
                        if v_isSharedCheck_1311_ == 0 {
                            v___x_1296_ = v___x_1293_;
                            v_isShared_1297_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1294_);
                            leanh::lean_dec(v___x_1293_);
                            v___x_1296_ = leanh::lean_box(0);
                            v_isShared_1297_ = v_isSharedCheck_1311_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1287_);
                        leanh::lean_dec(v_val_1285_);
                        leanh::lean_del_object(v___x_1273_);
                        leanh::lean_dec(v_snd_1271_);
                        leanh::lean_dec_ref(v_e_1254_);
                        v_a_1312_ = leanh::lean_ctor_get(v___x_1293_, 0);
                        v_isSharedCheck_1319_ =
                            (!leanh::lean_is_exclusive(v___x_1293_)) as u8;
                        if v_isSharedCheck_1319_ == 0 {
                            v___x_1314_ = v___x_1293_;
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1312_);
                            leanh::lean_dec(v___x_1293_);
                            v___x_1314_ = leanh::lean_box(0);
                            v_isShared_1315_ = v_isSharedCheck_1319_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1287_);
                    leanh::lean_dec(v_val_1285_);
                    leanh::lean_dec(v_snd_1271_);
                    v_a_1277_ = v___x_1290_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1298_ = (leanh::lean_unbox(v_a_1294_) as u8);
                if v___x_1298_ == 0 {
                    leanh::lean_del_object(v___x_1296_);
                    leanh::lean_dec(v_a_1294_);
                    leanh::lean_del_object(v___x_1287_);
                    leanh::lean_dec(v_val_1285_);
                    leanh::lean_dec(v_snd_1271_);
                    v_a_1277_ = v___x_1290_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1273_);
                    leanh::lean_dec_ref(v_e_1254_);
                    v___x_1299_ = l_Lean_LocalDecl_toExpr(v_val_1285_);
                    v___x_1300_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1300_, 0, v___x_1299_);
                    v___x_1301_ = (leanh::lean_unbox(v_a_1294_) as u8);
                    leanh::lean_dec(v_a_1294_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1300_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1301_,
                    );
                    if v_isShared_1288_ == 0 {
                        leanh::lean_ctor_set(v___x_1287_, 0, v___x_1300_);
                        v___x_1303_ = v___x_1287_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1300_);
                        v___x_1303_ = v_reuseFailAlloc_1310_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1304_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1304_, 0, v___x_1303_);
                leanh::lean_ctor_set(v___x_1304_, 1, v___x_1289_);
                v___x_1305_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
                v___x_1306_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                leanh::lean_ctor_set(v___x_1306_, 1, v_snd_1271_);
                if v_isShared_1297_ == 0 {
                    leanh::lean_ctor_set(v___x_1296_, 0, v___x_1306_);
                    v___x_1308_ = v___x_1296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
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
                    v_reuseFailAlloc_1318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
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
    mut v_e_1323_: *mut leanh::LeanObject,
    mut v_as_1324_: *mut leanh::LeanObject,
    mut v_sz_1325_: *mut leanh::LeanObject,
    mut v_i_1326_: *mut leanh::LeanObject,
    mut v_b_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1338_: usize = 0;
    let mut v_i_boxed_1339_: usize = 0;
    let mut v_res_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1338_ = leanh::lean_unbox_usize(v_sz_1325_);
    leanh::lean_dec(v_sz_1325_);
    v_i_boxed_1339_ = leanh::lean_unbox_usize(v_i_1326_);
    leanh::lean_dec(v_i_1326_);
    v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_1323_, v_as_1324_, v_sz_boxed_1338_, v_i_boxed_1339_, v_b_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    leanh::lean_dec(v___y_1336_);
    leanh::lean_dec_ref(v___y_1335_);
    leanh::lean_dec(v___y_1334_);
    leanh::lean_dec_ref(v___y_1333_);
    leanh::lean_dec(v___y_1332_);
    leanh::lean_dec_ref(v___y_1331_);
    leanh::lean_dec(v___y_1330_);
    leanh::lean_dec_ref(v___y_1329_);
    leanh::lean_dec(v___y_1328_);
    leanh::lean_dec_ref(v_as_1324_);
    return v_res_1340_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_e_1344_: *mut leanh::LeanObject,
    mut v_as_1345_: *mut leanh::LeanObject,
    mut v_sz_1346_: usize,
    mut v_i_1347_: usize,
    mut v_b_1348_: *mut leanh::LeanObject,
    mut v___y_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: usize = 0;
    let mut v___x_1366_: usize = 0;
    let mut v_reuseFailAlloc_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1373_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_a_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut v_unused_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
                if v___x_1354_ == 0 {
                    leanh::lean_dec_ref(v_e_1344_);
                    v___x_1355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1355_, 0, v_b_1348_);
                    return v___x_1355_;
                } else {
                    v_snd_1356_ = leanh::lean_ctor_get(v_b_1348_, 1);
                    v_isSharedCheck_1407_ = (!leanh::lean_is_exclusive(v_b_1348_)) as u8;
                    if v_isSharedCheck_1407_ == 0 {
                        v_unused_1408_ = leanh::lean_ctor_get(v_b_1348_, 0);
                        leanh::lean_dec(v_unused_1408_);
                        v___x_1358_ = v_b_1348_;
                        v_isShared_1359_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1356_);
                        leanh::lean_dec(v_b_1348_);
                        v___x_1358_ = leanh::lean_box(0);
                        v_isShared_1359_ = v_isSharedCheck_1407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1360_ = leanh::lean_box(0);
                v_a_1369_ = lean_array_uget(v_as_1345_, v_i_1347_);
                if leanh::lean_obj_tag(v_a_1369_) == 0 {
                    v_a_1362_ = v_snd_1356_;
                    state = 2;
                    continue;
                } else {
                    v_val_1370_ = leanh::lean_ctor_get(v_a_1369_, 0);
                    v_isSharedCheck_1406_ = (!leanh::lean_is_exclusive(v_a_1369_)) as u8;
                    if v_isSharedCheck_1406_ == 0 {
                        v___x_1372_ = v_a_1369_;
                        v_isShared_1373_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1370_);
                        leanh::lean_dec(v_a_1369_);
                        v___x_1372_ = leanh::lean_box(0);
                        v_isShared_1373_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1359_ == 0 {
                    leanh::lean_ctor_set(v___x_1358_, 1, v_a_1362_);
                    leanh::lean_ctor_set(v___x_1358_, 0, v___x_1360_);
                    v___x_1364_ = v___x_1358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_a_1362_);
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
                v___x_1374_ = leanh::lean_box(0);
                v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
                v___x_1376_ = l_Lean_LocalDecl_isAuxDecl(v_val_1370_);
                if v___x_1376_ == 0 {
                    v___x_1377_ = l_Lean_LocalDecl_type(v_val_1370_);
                    leanh::lean_inc_ref(v_e_1344_);
                    v___x_1378_ = l_Lean_Meta_isExprDefEq(
                        v___x_1377_,
                        v_e_1344_,
                        v___y_1349_,
                        v___y_1350_,
                        v___y_1351_,
                        v___y_1352_,
                    );
                    if leanh::lean_obj_tag(v___x_1378_) == 0 {
                        v_a_1379_ = leanh::lean_ctor_get(v___x_1378_, 0);
                        v_isSharedCheck_1397_ =
                            (!leanh::lean_is_exclusive(v___x_1378_)) as u8;
                        if v_isSharedCheck_1397_ == 0 {
                            v___x_1381_ = v___x_1378_;
                            v_isShared_1382_ = v_isSharedCheck_1397_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1379_);
                            leanh::lean_dec(v___x_1378_);
                            v___x_1381_ = leanh::lean_box(0);
                            v_isShared_1382_ = v_isSharedCheck_1397_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1372_);
                        leanh::lean_dec(v_val_1370_);
                        leanh::lean_del_object(v___x_1358_);
                        leanh::lean_dec(v_snd_1356_);
                        leanh::lean_dec_ref(v_e_1344_);
                        v_a_1398_ = leanh::lean_ctor_get(v___x_1378_, 0);
                        v_isSharedCheck_1405_ =
                            (!leanh::lean_is_exclusive(v___x_1378_)) as u8;
                        if v_isSharedCheck_1405_ == 0 {
                            v___x_1400_ = v___x_1378_;
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1398_);
                            leanh::lean_dec(v___x_1378_);
                            v___x_1400_ = leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1405_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1372_);
                    leanh::lean_dec(v_val_1370_);
                    leanh::lean_dec(v_snd_1356_);
                    v_a_1362_ = v___x_1375_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1383_ = (leanh::lean_unbox(v_a_1379_) as u8);
                if v___x_1383_ == 0 {
                    leanh::lean_del_object(v___x_1381_);
                    leanh::lean_dec(v_a_1379_);
                    leanh::lean_del_object(v___x_1372_);
                    leanh::lean_dec(v_val_1370_);
                    leanh::lean_dec(v_snd_1356_);
                    v_a_1362_ = v___x_1375_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1358_);
                    leanh::lean_dec_ref(v_e_1344_);
                    v___x_1384_ = l_Lean_LocalDecl_toExpr(v_val_1370_);
                    v___x_1385_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                    v___x_1386_ = (leanh::lean_unbox(v_a_1379_) as u8);
                    leanh::lean_dec(v_a_1379_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1385_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1386_,
                    );
                    if v_isShared_1373_ == 0 {
                        leanh::lean_ctor_set(v___x_1372_, 0, v___x_1385_);
                        v___x_1388_ = v___x_1372_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1385_);
                        v___x_1388_ = v_reuseFailAlloc_1396_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1389_, 0, v___x_1388_);
                leanh::lean_ctor_set(v___x_1389_, 1, v___x_1374_);
                v___x_1390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1390_, 0, v___x_1389_);
                v___x_1391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1391_, 0, v___x_1390_);
                v___x_1392_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                leanh::lean_ctor_set(v___x_1392_, 1, v_snd_1356_);
                if v_isShared_1382_ == 0 {
                    leanh::lean_ctor_set(v___x_1381_, 0, v___x_1392_);
                    v___x_1394_ = v___x_1381_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
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
                    v_reuseFailAlloc_1404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
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
    mut v_e_1409_: *mut leanh::LeanObject,
    mut v_as_1410_: *mut leanh::LeanObject,
    mut v_sz_1411_: *mut leanh::LeanObject,
    mut v_i_1412_: *mut leanh::LeanObject,
    mut v_b_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1419_: usize = 0;
    let mut v_i_boxed_1420_: usize = 0;
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1419_ = leanh::lean_unbox_usize(v_sz_1411_);
    leanh::lean_dec(v_sz_1411_);
    v_i_boxed_1420_ = leanh::lean_unbox_usize(v_i_1412_);
    leanh::lean_dec(v_i_1412_);
    v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_1409_, v_as_1410_, v_sz_boxed_1419_, v_i_boxed_1420_, v_b_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    leanh::lean_dec(v___y_1415_);
    leanh::lean_dec_ref(v___y_1414_);
    leanh::lean_dec_ref(v_as_1410_);
    return v_res_1421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(
    mut v_e_1422_: *mut leanh::LeanObject,
    mut v_as_1423_: *mut leanh::LeanObject,
    mut v_sz_1424_: usize,
    mut v_i_1425_: usize,
    mut v_b_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
    mut v___y_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1442_: u8 = 0;
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: u8 = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut v_a_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1437_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
                if v___x_1437_ == 0 {
                    leanh::lean_dec_ref(v_e_1422_);
                    v___x_1438_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1438_, 0, v_b_1426_);
                    return v___x_1438_;
                } else {
                    v_snd_1439_ = leanh::lean_ctor_get(v_b_1426_, 1);
                    v_isSharedCheck_1490_ = (!leanh::lean_is_exclusive(v_b_1426_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v_unused_1491_ = leanh::lean_ctor_get(v_b_1426_, 0);
                        leanh::lean_dec(v_unused_1491_);
                        v___x_1441_ = v_b_1426_;
                        v_isShared_1442_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1439_);
                        leanh::lean_dec(v_b_1426_);
                        v___x_1441_ = leanh::lean_box(0);
                        v_isShared_1442_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1443_ = leanh::lean_box(0);
                v_a_1452_ = lean_array_uget(v_as_1423_, v_i_1425_);
                if leanh::lean_obj_tag(v_a_1452_) == 0 {
                    v_a_1445_ = v_snd_1439_;
                    state = 2;
                    continue;
                } else {
                    v_val_1453_ = leanh::lean_ctor_get(v_a_1452_, 0);
                    v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v_a_1452_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1455_ = v_a_1452_;
                        v_isShared_1456_ = v_isSharedCheck_1489_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1453_);
                        leanh::lean_dec(v_a_1452_);
                        v___x_1455_ = leanh::lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1489_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1442_ == 0 {
                    leanh::lean_ctor_set(v___x_1441_, 1, v_a_1445_);
                    leanh::lean_ctor_set(v___x_1441_, 0, v___x_1443_);
                    v___x_1447_ = v___x_1441_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1445_);
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
                v___x_1457_ = leanh::lean_box(0);
                v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0;
                v___x_1459_ = l_Lean_LocalDecl_isAuxDecl(v_val_1453_);
                if v___x_1459_ == 0 {
                    v___x_1460_ = l_Lean_LocalDecl_type(v_val_1453_);
                    leanh::lean_inc_ref(v_e_1422_);
                    v___x_1461_ = l_Lean_Meta_isExprDefEq(
                        v___x_1460_,
                        v_e_1422_,
                        v___y_1432_,
                        v___y_1433_,
                        v___y_1434_,
                        v___y_1435_,
                    );
                    if leanh::lean_obj_tag(v___x_1461_) == 0 {
                        v_a_1462_ = leanh::lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1480_ =
                            (!leanh::lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1480_ == 0 {
                            v___x_1464_ = v___x_1461_;
                            v_isShared_1465_ = v_isSharedCheck_1480_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1462_);
                            leanh::lean_dec(v___x_1461_);
                            v___x_1464_ = leanh::lean_box(0);
                            v_isShared_1465_ = v_isSharedCheck_1480_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1455_);
                        leanh::lean_dec(v_val_1453_);
                        leanh::lean_del_object(v___x_1441_);
                        leanh::lean_dec(v_snd_1439_);
                        leanh::lean_dec_ref(v_e_1422_);
                        v_a_1481_ = leanh::lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1488_ =
                            (!leanh::lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1488_ == 0 {
                            v___x_1483_ = v___x_1461_;
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1481_);
                            leanh::lean_dec(v___x_1461_);
                            v___x_1483_ = leanh::lean_box(0);
                            v_isShared_1484_ = v_isSharedCheck_1488_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1455_);
                    leanh::lean_dec(v_val_1453_);
                    leanh::lean_dec(v_snd_1439_);
                    v_a_1445_ = v___x_1458_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1466_ = (leanh::lean_unbox(v_a_1462_) as u8);
                if v___x_1466_ == 0 {
                    leanh::lean_del_object(v___x_1464_);
                    leanh::lean_dec(v_a_1462_);
                    leanh::lean_del_object(v___x_1455_);
                    leanh::lean_dec(v_val_1453_);
                    leanh::lean_dec(v_snd_1439_);
                    v_a_1445_ = v___x_1458_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1441_);
                    leanh::lean_dec_ref(v_e_1422_);
                    v___x_1467_ = l_Lean_LocalDecl_toExpr(v_val_1453_);
                    v___x_1468_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1468_, 0, v___x_1467_);
                    v___x_1469_ = (leanh::lean_unbox(v_a_1462_) as u8);
                    leanh::lean_dec(v_a_1462_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1468_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1469_,
                    );
                    if v_isShared_1456_ == 0 {
                        leanh::lean_ctor_set(v___x_1455_, 0, v___x_1468_);
                        v___x_1471_ = v___x_1455_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1468_);
                        v___x_1471_ = v_reuseFailAlloc_1479_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1472_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                leanh::lean_ctor_set(v___x_1472_, 1, v___x_1457_);
                v___x_1473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
                v___x_1474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                v___x_1475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                leanh::lean_ctor_set(v___x_1475_, 1, v_snd_1439_);
                if v_isShared_1465_ == 0 {
                    leanh::lean_ctor_set(v___x_1464_, 0, v___x_1475_);
                    v___x_1477_ = v___x_1464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
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
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
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
    mut v_e_1492_: *mut leanh::LeanObject,
    mut v_as_1493_: *mut leanh::LeanObject,
    mut v_sz_1494_: *mut leanh::LeanObject,
    mut v_i_1495_: *mut leanh::LeanObject,
    mut v_b_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
    mut v___y_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1507_: usize = 0;
    let mut v_i_boxed_1508_: usize = 0;
    let mut v_res_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1507_ = leanh::lean_unbox_usize(v_sz_1494_);
    leanh::lean_dec(v_sz_1494_);
    v_i_boxed_1508_ = leanh::lean_unbox_usize(v_i_1495_);
    leanh::lean_dec(v_i_1495_);
    v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_1492_, v_as_1493_, v_sz_boxed_1507_, v_i_boxed_1508_, v_b_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec_ref(v___y_1504_);
    leanh::lean_dec(v___y_1503_);
    leanh::lean_dec_ref(v___y_1502_);
    leanh::lean_dec(v___y_1501_);
    leanh::lean_dec_ref(v___y_1500_);
    leanh::lean_dec(v___y_1499_);
    leanh::lean_dec_ref(v___y_1498_);
    leanh::lean_dec(v___y_1497_);
    leanh::lean_dec_ref(v_as_1493_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(
    mut v_init_1510_: *mut leanh::LeanObject,
    mut v_e_1511_: *mut leanh::LeanObject,
    mut v_n_1512_: *mut leanh::LeanObject,
    mut v_b_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
    mut v___y_1517_: *mut leanh::LeanObject,
    mut v___y_1518_: *mut leanh::LeanObject,
    mut v___y_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1527_: usize = 0;
    let mut v___x_1528_: usize = 0;
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v_fst_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut v_a_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_vs_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1556_: usize = 0;
    let mut v___x_1557_: usize = 0;
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v_fst_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_1512_) == 0 {
                    v_cs_1524_ = leanh::lean_ctor_get(v_n_1512_, 0);
                    v___x_1525_ = leanh::lean_box(0);
                    v___x_1526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                    leanh::lean_ctor_set(v___x_1526_, 1, v_b_1513_);
                    v_sz_1527_ = lean_array_size(v_cs_1524_);
                    v___x_1528_ = 0usize;
                    v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_1510_, v_e_1511_, v_cs_1524_, v_sz_1527_, v___x_1528_, v___x_1526_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
                    if leanh::lean_obj_tag(v___x_1529_) == 0 {
                        v_a_1530_ = leanh::lean_ctor_get(v___x_1529_, 0);
                        v_isSharedCheck_1544_ =
                            (!leanh::lean_is_exclusive(v___x_1529_)) as u8;
                        if v_isSharedCheck_1544_ == 0 {
                            v___x_1532_ = v___x_1529_;
                            v_isShared_1533_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1530_);
                            leanh::lean_dec(v___x_1529_);
                            v___x_1532_ = leanh::lean_box(0);
                            v_isShared_1533_ = v_isSharedCheck_1544_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1545_ = leanh::lean_ctor_get(v___x_1529_, 0);
                        v_isSharedCheck_1552_ =
                            (!leanh::lean_is_exclusive(v___x_1529_)) as u8;
                        if v_isSharedCheck_1552_ == 0 {
                            v___x_1547_ = v___x_1529_;
                            v_isShared_1548_ = v_isSharedCheck_1552_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1545_);
                            leanh::lean_dec(v___x_1529_);
                            v___x_1547_ = leanh::lean_box(0);
                            v_isShared_1548_ = v_isSharedCheck_1552_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1553_ = leanh::lean_ctor_get(v_n_1512_, 0);
                    v___x_1554_ = leanh::lean_box(0);
                    v___x_1555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1555_, 0, v___x_1554_);
                    leanh::lean_ctor_set(v___x_1555_, 1, v_b_1513_);
                    v_sz_1556_ = lean_array_size(v_vs_1553_);
                    v___x_1557_ = 0usize;
                    v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_1511_, v_vs_1553_, v_sz_1556_, v___x_1557_, v___x_1555_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
                    if leanh::lean_obj_tag(v___x_1558_) == 0 {
                        v_a_1559_ = leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1573_ =
                            (!leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1573_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1573_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1559_);
                            leanh::lean_dec(v___x_1558_);
                            v___x_1561_ = leanh::lean_box(0);
                            v_isShared_1562_ = v_isSharedCheck_1573_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1574_ = leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1581_ =
                            (!leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v___x_1576_ = v___x_1558_;
                            v_isShared_1577_ = v_isSharedCheck_1581_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1574_);
                            leanh::lean_dec(v___x_1558_);
                            v___x_1576_ = leanh::lean_box(0);
                            v_isShared_1577_ = v_isSharedCheck_1581_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1534_ = leanh::lean_ctor_get(v_a_1530_, 0);
                if leanh::lean_obj_tag(v_fst_1534_) == 0 {
                    v_snd_1535_ = leanh::lean_ctor_get(v_a_1530_, 1);
                    leanh::lean_inc(v_snd_1535_);
                    leanh::lean_dec(v_a_1530_);
                    v___x_1536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1536_, 0, v_snd_1535_);
                    if v_isShared_1533_ == 0 {
                        leanh::lean_ctor_set(v___x_1532_, 0, v___x_1536_);
                        v___x_1538_ = v___x_1532_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
                        v___x_1538_ = v_reuseFailAlloc_1539_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_1534_);
                    leanh::lean_dec(v_a_1530_);
                    v_val_1540_ = leanh::lean_ctor_get(v_fst_1534_, 0);
                    leanh::lean_inc(v_val_1540_);
                    leanh::lean_dec_ref_known(v_fst_1534_, 1);
                    if v_isShared_1533_ == 0 {
                        leanh::lean_ctor_set(v___x_1532_, 0, v_val_1540_);
                        v___x_1542_ = v___x_1532_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_val_1540_);
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
                    v_reuseFailAlloc_1551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
                    v___x_1550_ = v_reuseFailAlloc_1551_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1550_;
            }
            6 => {
                v_fst_1563_ = leanh::lean_ctor_get(v_a_1559_, 0);
                if leanh::lean_obj_tag(v_fst_1563_) == 0 {
                    v_snd_1564_ = leanh::lean_ctor_get(v_a_1559_, 1);
                    leanh::lean_inc(v_snd_1564_);
                    leanh::lean_dec(v_a_1559_);
                    v___x_1565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1565_, 0, v_snd_1564_);
                    if v_isShared_1562_ == 0 {
                        leanh::lean_ctor_set(v___x_1561_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1561_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_1563_);
                    leanh::lean_dec(v_a_1559_);
                    v_val_1569_ = leanh::lean_ctor_get(v_fst_1563_, 0);
                    leanh::lean_inc(v_val_1569_);
                    leanh::lean_dec_ref_known(v_fst_1563_, 1);
                    if v_isShared_1562_ == 0 {
                        leanh::lean_ctor_set(v___x_1561_, 0, v_val_1569_);
                        v___x_1571_ = v___x_1561_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1572_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_val_1569_);
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
                    v_reuseFailAlloc_1580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
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
    mut v_init_1582_: *mut leanh::LeanObject,
    mut v_e_1583_: *mut leanh::LeanObject,
    mut v_as_1584_: *mut leanh::LeanObject,
    mut v_sz_1585_: usize,
    mut v_i_1586_: usize,
    mut v_b_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v_a_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: usize = 0;
    let mut v___x_1622_: usize = 0;
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v_unused_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
                if v___x_1598_ == 0 {
                    leanh::lean_dec_ref(v_e_1583_);
                    v___x_1599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1599_, 0, v_b_1587_);
                    return v___x_1599_;
                } else {
                    v_snd_1600_ = leanh::lean_ctor_get(v_b_1587_, 1);
                    v_isSharedCheck_1634_ = (!leanh::lean_is_exclusive(v_b_1587_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v_unused_1635_ = leanh::lean_ctor_get(v_b_1587_, 0);
                        leanh::lean_dec(v_unused_1635_);
                        v___x_1602_ = v_b_1587_;
                        v_isShared_1603_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1600_);
                        leanh::lean_dec(v_b_1587_);
                        v___x_1602_ = leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1604_ = lean_array_uget_borrowed(v_as_1584_, v_i_1586_);
                leanh::lean_inc(v_snd_1600_);
                leanh::lean_inc_ref(v_e_1583_);
                v___x_1605_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1582_, v_e_1583_, v_a_1604_, v_snd_1600_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
                if leanh::lean_obj_tag(v___x_1605_) == 0 {
                    v_a_1606_ = leanh::lean_ctor_get(v___x_1605_, 0);
                    v_isSharedCheck_1625_ = (!leanh::lean_is_exclusive(v___x_1605_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1608_ = v___x_1605_;
                        v_isShared_1609_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1606_);
                        leanh::lean_dec(v___x_1605_);
                        v___x_1608_ = leanh::lean_box(0);
                        v_isShared_1609_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1602_);
                    leanh::lean_dec(v_snd_1600_);
                    leanh::lean_dec_ref(v_e_1583_);
                    v_a_1626_ = leanh::lean_ctor_get(v___x_1605_, 0);
                    v_isSharedCheck_1633_ = (!leanh::lean_is_exclusive(v___x_1605_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1628_ = v___x_1605_;
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1626_);
                        leanh::lean_dec(v___x_1605_);
                        v___x_1628_ = leanh::lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_1606_) == 0 {
                    leanh::lean_dec_ref(v_e_1583_);
                    v___x_1610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1610_, 0, v_a_1606_);
                    if v_isShared_1603_ == 0 {
                        leanh::lean_ctor_set(v___x_1602_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1602_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1610_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_snd_1600_);
                        v___x_1612_ = v_reuseFailAlloc_1616_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1608_);
                    leanh::lean_dec(v_snd_1600_);
                    v_a_1617_ = leanh::lean_ctor_get(v_a_1606_, 0);
                    leanh::lean_inc(v_a_1617_);
                    leanh::lean_dec_ref_known(v_a_1606_, 1);
                    v___x_1618_ = leanh::lean_box(0);
                    if v_isShared_1603_ == 0 {
                        leanh::lean_ctor_set(v___x_1602_, 1, v_a_1617_);
                        leanh::lean_ctor_set(v___x_1602_, 0, v___x_1618_);
                        v___x_1620_ = v___x_1602_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_a_1617_);
                        v___x_1620_ = v_reuseFailAlloc_1624_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1609_ == 0 {
                    leanh::lean_ctor_set(v___x_1608_, 0, v___x_1612_);
                    v___x_1614_ = v___x_1608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
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
                    v_reuseFailAlloc_1632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
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
    mut v_init_1636_: *mut leanh::LeanObject,
    mut v_e_1637_: *mut leanh::LeanObject,
    mut v_as_1638_: *mut leanh::LeanObject,
    mut v_sz_1639_: *mut leanh::LeanObject,
    mut v_i_1640_: *mut leanh::LeanObject,
    mut v_b_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
    mut v___y_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
    mut v___y_1645_: *mut leanh::LeanObject,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1652_: usize = 0;
    let mut v_i_boxed_1653_: usize = 0;
    let mut v_res_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1652_ = leanh::lean_unbox_usize(v_sz_1639_);
    leanh::lean_dec(v_sz_1639_);
    v_i_boxed_1653_ = leanh::lean_unbox_usize(v_i_1640_);
    leanh::lean_dec(v_i_1640_);
    v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_init_1636_, v_e_1637_, v_as_1638_, v_sz_boxed_1652_, v_i_boxed_1653_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
    leanh::lean_dec(v___y_1650_);
    leanh::lean_dec_ref(v___y_1649_);
    leanh::lean_dec(v___y_1648_);
    leanh::lean_dec_ref(v___y_1647_);
    leanh::lean_dec(v___y_1646_);
    leanh::lean_dec_ref(v___y_1645_);
    leanh::lean_dec(v___y_1644_);
    leanh::lean_dec_ref(v___y_1643_);
    leanh::lean_dec(v___y_1642_);
    leanh::lean_dec_ref(v_as_1638_);
    leanh::lean_dec_ref(v_init_1636_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(
    mut v_init_1655_: *mut leanh::LeanObject,
    mut v_e_1656_: *mut leanh::LeanObject,
    mut v_n_1657_: *mut leanh::LeanObject,
    mut v_b_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1655_, v_e_1656_, v_n_1657_, v_b_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
    leanh::lean_dec(v___y_1667_);
    leanh::lean_dec_ref(v___y_1666_);
    leanh::lean_dec(v___y_1665_);
    leanh::lean_dec_ref(v___y_1664_);
    leanh::lean_dec(v___y_1663_);
    leanh::lean_dec_ref(v___y_1662_);
    leanh::lean_dec(v___y_1661_);
    leanh::lean_dec_ref(v___y_1660_);
    leanh::lean_dec(v___y_1659_);
    leanh::lean_dec_ref(v_n_1657_);
    leanh::lean_dec_ref(v_init_1655_);
    return v_res_1669_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(
    mut v_e_1670_: *mut leanh::LeanObject,
    mut v_t_1671_: *mut leanh::LeanObject,
    mut v_init_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v_a_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1697_: usize = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v_fst_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_a_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1683_ = leanh::lean_ctor_get(v_t_1671_, 0);
                v_tail_1684_ = leanh::lean_ctor_get(v_t_1671_, 1);
                leanh::lean_inc_ref(v_e_1670_);
                leanh::lean_inc_ref(v_init_1672_);
                v___x_1685_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_init_1672_, v_e_1670_, v_root_1683_, v_init_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                leanh::lean_dec_ref(v_init_1672_);
                if leanh::lean_obj_tag(v___x_1685_) == 0 {
                    v_a_1686_ = leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1722_ = (!leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1722_ == 0 {
                        v___x_1688_ = v___x_1685_;
                        v_isShared_1689_ = v_isSharedCheck_1722_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1686_);
                        leanh::lean_dec(v___x_1685_);
                        v___x_1688_ = leanh::lean_box(0);
                        v_isShared_1689_ = v_isSharedCheck_1722_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1670_);
                    v_a_1723_ = leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1730_ = (!leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1730_ == 0 {
                        v___x_1725_ = v___x_1685_;
                        v_isShared_1726_ = v_isSharedCheck_1730_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1723_);
                        leanh::lean_dec(v___x_1685_);
                        v___x_1725_ = leanh::lean_box(0);
                        v_isShared_1726_ = v_isSharedCheck_1730_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1686_) == 0 {
                    leanh::lean_dec_ref(v_e_1670_);
                    v_a_1690_ = leanh::lean_ctor_get(v_a_1686_, 0);
                    leanh::lean_inc(v_a_1690_);
                    leanh::lean_dec_ref_known(v_a_1686_, 1);
                    if v_isShared_1689_ == 0 {
                        leanh::lean_ctor_set(v___x_1688_, 0, v_a_1690_);
                        v___x_1692_ = v___x_1688_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1690_);
                        v___x_1692_ = v_reuseFailAlloc_1693_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1688_);
                    v_a_1694_ = leanh::lean_ctor_get(v_a_1686_, 0);
                    leanh::lean_inc(v_a_1694_);
                    leanh::lean_dec_ref_known(v_a_1686_, 1);
                    v___x_1695_ = leanh::lean_box(0);
                    v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
                    leanh::lean_ctor_set(v___x_1696_, 1, v_a_1694_);
                    v_sz_1697_ = lean_array_size(v_tail_1684_);
                    v___x_1698_ = 0usize;
                    v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_1670_, v_tail_1684_, v_sz_1697_, v___x_1698_, v___x_1696_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                    if leanh::lean_obj_tag(v___x_1699_) == 0 {
                        v_a_1700_ = leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1713_ =
                            (!leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1713_ == 0 {
                            v___x_1702_ = v___x_1699_;
                            v_isShared_1703_ = v_isSharedCheck_1713_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1700_);
                            leanh::lean_dec(v___x_1699_);
                            v___x_1702_ = leanh::lean_box(0);
                            v_isShared_1703_ = v_isSharedCheck_1713_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1714_ = leanh::lean_ctor_get(v___x_1699_, 0);
                        v_isSharedCheck_1721_ =
                            (!leanh::lean_is_exclusive(v___x_1699_)) as u8;
                        if v_isSharedCheck_1721_ == 0 {
                            v___x_1716_ = v___x_1699_;
                            v_isShared_1717_ = v_isSharedCheck_1721_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1714_);
                            leanh::lean_dec(v___x_1699_);
                            v___x_1716_ = leanh::lean_box(0);
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
                v_fst_1704_ = leanh::lean_ctor_get(v_a_1700_, 0);
                if leanh::lean_obj_tag(v_fst_1704_) == 0 {
                    v_snd_1705_ = leanh::lean_ctor_get(v_a_1700_, 1);
                    leanh::lean_inc(v_snd_1705_);
                    leanh::lean_dec(v_a_1700_);
                    if v_isShared_1703_ == 0 {
                        leanh::lean_ctor_set(v___x_1702_, 0, v_snd_1705_);
                        v___x_1707_ = v___x_1702_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_snd_1705_);
                        v___x_1707_ = v_reuseFailAlloc_1708_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_1704_);
                    leanh::lean_dec(v_a_1700_);
                    v_val_1709_ = leanh::lean_ctor_get(v_fst_1704_, 0);
                    leanh::lean_inc(v_val_1709_);
                    leanh::lean_dec_ref_known(v_fst_1704_, 1);
                    if v_isShared_1703_ == 0 {
                        leanh::lean_ctor_set(v___x_1702_, 0, v_val_1709_);
                        v___x_1711_ = v___x_1702_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_val_1709_);
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
                    v_reuseFailAlloc_1720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
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
                    v_reuseFailAlloc_1729_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
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
    mut v_e_1731_: *mut leanh::LeanObject,
    mut v_t_1732_: *mut leanh::LeanObject,
    mut v_init_1733_: *mut leanh::LeanObject,
    mut v___y_1734_: *mut leanh::LeanObject,
    mut v___y_1735_: *mut leanh::LeanObject,
    mut v___y_1736_: *mut leanh::LeanObject,
    mut v___y_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1742_);
    leanh::lean_dec_ref(v___y_1741_);
    leanh::lean_dec(v___y_1740_);
    leanh::lean_dec_ref(v___y_1739_);
    leanh::lean_dec(v___y_1738_);
    leanh::lean_dec_ref(v___y_1737_);
    leanh::lean_dec(v___y_1736_);
    leanh::lean_dec_ref(v___y_1735_);
    leanh::lean_dec(v___y_1734_);
    leanh::lean_dec_ref(v_t_1732_);
    return v_res_1744_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_dischargeAssumption(
    mut v_e_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
    mut v_a_1754_: *mut leanh::LeanObject,
    mut v_a_1755_: *mut leanh::LeanObject,
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_a_1758_: *mut leanh::LeanObject,
    mut v_a_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1768_: u8 = 0;
    let mut v_fst_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v_a_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_1761_ = leanh::lean_ctor_get(v_a_1756_, 2);
                v_decls_1762_ = leanh::lean_ctor_get(v_lctx_1761_, 1);
                v___x_1763_ = l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0;
                v___x_1764_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_1750_, v_decls_1762_, v___x_1763_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
                if leanh::lean_obj_tag(v___x_1764_) == 0 {
                    v_a_1765_ = leanh::lean_ctor_get(v___x_1764_, 0);
                    v_isSharedCheck_1778_ = (!leanh::lean_is_exclusive(v___x_1764_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1767_ = v___x_1764_;
                        v_isShared_1768_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1765_);
                        leanh::lean_dec(v___x_1764_);
                        v___x_1767_ = leanh::lean_box(0);
                        v_isShared_1768_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1779_ = leanh::lean_ctor_get(v___x_1764_, 0);
                    v_isSharedCheck_1786_ = (!leanh::lean_is_exclusive(v___x_1764_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1764_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1779_);
                        leanh::lean_dec(v___x_1764_);
                        v___x_1781_ = leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1769_ = leanh::lean_ctor_get(v_a_1765_, 0);
                leanh::lean_inc(v_fst_1769_);
                leanh::lean_dec(v_a_1765_);
                if leanh::lean_obj_tag(v_fst_1769_) == 0 {
                    v___x_1770_ = l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1;
                    if v_isShared_1768_ == 0 {
                        leanh::lean_ctor_set(v___x_1767_, 0, v___x_1770_);
                        v___x_1772_ = v___x_1767_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1773_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
                        v___x_1772_ = v_reuseFailAlloc_1773_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1774_ = leanh::lean_ctor_get(v_fst_1769_, 0);
                    leanh::lean_inc(v_val_1774_);
                    leanh::lean_dec_ref_known(v_fst_1769_, 1);
                    if v_isShared_1768_ == 0 {
                        leanh::lean_ctor_set(v___x_1767_, 0, v_val_1774_);
                        v___x_1776_ = v___x_1767_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1777_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_val_1774_);
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
                    v_reuseFailAlloc_1785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
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
    mut v_e_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_a_1791_: *mut leanh::LeanObject,
    mut v_a_1792_: *mut leanh::LeanObject,
    mut v_a_1793_: *mut leanh::LeanObject,
    mut v_a_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(
        v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_,
        v_a_1795_, v_a_1796_,
    );
    leanh::lean_dec(v_a_1796_);
    leanh::lean_dec_ref(v_a_1795_);
    leanh::lean_dec(v_a_1794_);
    leanh::lean_dec_ref(v_a_1793_);
    leanh::lean_dec(v_a_1792_);
    leanh::lean_dec_ref(v_a_1791_);
    leanh::lean_dec(v_a_1790_);
    leanh::lean_dec_ref(v_a_1789_);
    leanh::lean_dec(v_a_1788_);
    return v_res_1798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(
    mut v_e_1799_: *mut leanh::LeanObject,
    mut v_as_1800_: *mut leanh::LeanObject,
    mut v_sz_1801_: usize,
    mut v_i_1802_: usize,
    mut v_b_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_1799_, v_as_1800_, v_sz_1801_, v_i_1802_, v_b_1803_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
    return v___x_1814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(
    mut v_e_1815_: *mut leanh::LeanObject,
    mut v_as_1816_: *mut leanh::LeanObject,
    mut v_sz_1817_: *mut leanh::LeanObject,
    mut v_i_1818_: *mut leanh::LeanObject,
    mut v_b_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
    mut v___y_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1830_: usize = 0;
    let mut v_i_boxed_1831_: usize = 0;
    let mut v_res_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1830_ = leanh::lean_unbox_usize(v_sz_1817_);
    leanh::lean_dec(v_sz_1817_);
    v_i_boxed_1831_ = leanh::lean_unbox_usize(v_i_1818_);
    leanh::lean_dec(v_i_1818_);
    v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_1815_, v_as_1816_, v_sz_boxed_1830_, v_i_boxed_1831_, v_b_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
    leanh::lean_dec(v___y_1828_);
    leanh::lean_dec_ref(v___y_1827_);
    leanh::lean_dec(v___y_1826_);
    leanh::lean_dec_ref(v___y_1825_);
    leanh::lean_dec(v___y_1824_);
    leanh::lean_dec_ref(v___y_1823_);
    leanh::lean_dec(v___y_1822_);
    leanh::lean_dec_ref(v___y_1821_);
    leanh::lean_dec(v___y_1820_);
    leanh::lean_dec_ref(v_as_1816_);
    return v_res_1832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(
    mut v_e_1833_: *mut leanh::LeanObject,
    mut v_as_1834_: *mut leanh::LeanObject,
    mut v_sz_1835_: usize,
    mut v_i_1836_: usize,
    mut v_b_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_1833_, v_as_1834_, v_sz_1835_, v_i_1836_, v_b_1837_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    return v___x_1848_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_e_1849_: *mut leanh::LeanObject,
    mut v_as_1850_: *mut leanh::LeanObject,
    mut v_sz_1851_: *mut leanh::LeanObject,
    mut v_i_1852_: *mut leanh::LeanObject,
    mut v_b_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1864_: usize = 0;
    let mut v_i_boxed_1865_: usize = 0;
    let mut v_res_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1864_ = leanh::lean_unbox_usize(v_sz_1851_);
    leanh::lean_dec(v_sz_1851_);
    v_i_boxed_1865_ = leanh::lean_unbox_usize(v_i_1852_);
    leanh::lean_dec(v_i_1852_);
    v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_1849_, v_as_1850_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
    leanh::lean_dec(v___y_1862_);
    leanh::lean_dec_ref(v___y_1861_);
    leanh::lean_dec(v___y_1860_);
    leanh::lean_dec_ref(v___y_1859_);
    leanh::lean_dec(v___y_1858_);
    leanh::lean_dec_ref(v___y_1857_);
    leanh::lean_dec(v___y_1856_);
    leanh::lean_dec_ref(v___y_1855_);
    leanh::lean_dec(v___y_1854_);
    leanh::lean_dec_ref(v_as_1850_);
    return v_res_1866_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Discharger(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Discharger(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Discharger(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
}